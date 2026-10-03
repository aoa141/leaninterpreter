// Lazily decoded compacted regions.
//
// Native Lean maps an `.olean` file and uses the objects in place, so importing costs nothing for
// the data that is never looked at (most proofs and definition bodies). The managed counterpart:
// the file stays mapped, and objects are converted into managed objects on demand.
//
//  * A constructor object is created as a "shell": header and scalar fields are filled in, the
//    object fields stay null. `lean_ctor_get` resolves a null field on first use
//    (`LeanRt.lean_ctor_force`): the identity of a region object (`Obj.m_id`) is its logical
//    address, which gives the region (`Find`) and the position of the field in the file.
//  * All other objects are created complete: strings, scalar arrays and big numbers are copied;
//    the elements of arrays (and the values of thunks, tasks, refs, promises and closures) are
//    created together with their owner, as shells if they are constructor objects. This keeps
//    all code that accesses `m_data` directly unchanged.
//  * Every object is created at most once: a table (file offset -> object) per region keeps the
//    objects created so far, so sharing and pointer equality are preserved.
//
// A region can only be read this way if its address range is free (`RegionAddressSpace`);
// otherwise (the file was read before, e.g. it was rebuilt) the eager `RegionReader` is used.
// The mapping lives as long as the process: objects with unresolved fields may outlive the
// `CompactedRegion` value.

using System.IO.MemoryMappedFiles;
using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace LeanInterpreter.Runtime.Compact;

internal sealed unsafe class LazyRegion
{
    /// <summary>Decode regions read by Lean lazily (LEANINTERP_OLEAN_LAZY=0 turns it off).</summary>
    internal static bool Enabled = Environment.GetEnvironmentVariable("LEANINTERP_OLEAN_LAZY") != "0";

    /// <summary>
    /// Map the files (default, except on Windows where a mapped file cannot be replaced or
    /// deleted: there only files under <see cref="MappedRoots"/> are mapped) or copy them into
    /// native memory. Override with LEANINTERP_OLEAN_MMAP=0/1.
    /// </summary>
    internal static bool? UseMmap = Environment.GetEnvironmentVariable("LEANINTERP_OLEAN_MMAP") switch
    {
        "1" => true,
        "0" => false,
        _ => OperatingSystem.IsWindows() ? null : true,
    };

    /// <summary>Directories whose files never change while the process runs (the sysroot's library).</summary>
    public static string[] MappedRoots = Array.Empty<string>();

    static bool ShouldMap(string path) =>
        UseMmap ?? (MappedRoots.Length > 0 && MappedRoots.Any(r => Path.GetFullPath(path).StartsWith(r, StringComparison.OrdinalIgnoreCase)));

    readonly byte* m_p;
    readonly long m_len;
    readonly ulong m_base;
    readonly long m_first;      // file offset of the first object
    readonly long m_end;        // file offset of the end of the object data
    readonly bool m_gmp;
    readonly bool m_closuresOk;
    readonly nint[] m_functions;
    readonly string m_path;
    readonly object m_owner;    // keeps the mapping alive
    CompactedRegionData[] m_deps;   // sorted by BaseAddr

    // Objects created so far: open addressing, key = file offset / 8 (never 0). Lookups do not
    // lock; insertions happen under `m_lock` and write the value before the key.
    sealed class Table
    {
        public readonly int[] Keys;
        public readonly Obj[] Vals;
        public readonly int Shift;
        public Table(int log2) { Keys = new int[1 << log2]; Vals = new Obj[1 << log2]; Shift = 32 - log2; }
    }
    volatile Table m_table;
    int m_count;
    readonly object m_lock = new();

    LazyRegion(byte* p, long len, object owner, string path, in RegionLayout l)
    {
        m_p = p; m_len = len; m_owner = owner; m_path = path;
        m_base = l.Header.BaseAddr;
        m_first = l.DataOff + 8;
        m_end = l.DataOff + l.DataSize;
        m_gmp = l.Header.Gmp;
        m_closuresOk = l.ClosuresOk;
        m_functions = l.Functions;
    }

    // ------------------------------------------------------------------
    // Opening

    sealed class NativeBuffer
    {
        public void* P;
        ~NativeBuffer() { NativeMemory.Free(P); }
    }

    /// <summary>
    /// Opens `path` as a lazily decoded region, or reads it eagerly if its address range is taken.
    /// </summary>
    public static CompactedRegionData Open(string path, IReadOnlyList<CompactedRegionData> deps)
    {
        byte* p;
        long len;
        object owner;
        using (var fs = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.Read | FileShare.Delete, 1))
        {
            len = fs.Length;
            if (len < OleanHeader.Size) throw new OleanFormatException("invalid header");
            if (ShouldMap(path))
            {
                // (the view stays valid after the file is closed)
                using var mmf = MemoryMappedFile.CreateFromFile(fs, null, 0, MemoryMappedFileAccess.Read, HandleInheritability.None, leaveOpen: true);
                var view = mmf.CreateViewAccessor(0, len, MemoryMappedFileAccess.Read);
                byte* q = null;
                view.SafeMemoryMappedViewHandle.AcquirePointer(ref q);
                p = q + view.PointerOffset;
                owner = view;
            }
            else
            {
                var nb = new NativeBuffer { P = NativeMemory.Alloc((nuint)len) };
                p = (byte*)nb.P;
                long done = 0;
                while (done < len)
                {
                    int n = RandomAccess.Read(fs.SafeFileHandle, new Span<byte>(p + done, (int)Math.Min(len - done, 1 << 30)), done);
                    if (n <= 0) throw new OleanFormatException("unexpected end of file");
                    done += n;
                }
                owner = nb;
            }
        }
        var layout = RegionReader.ParseLayout(p, len);
        ulong baseAddr = layout.Header.BaseAddr;
        if (!RegionAddressSpace.TryReserve(baseAddr, (ulong)len))
        {
            (owner as IDisposable)?.Dispose();
            return RegionReader.ReadFile(path, deps);
        }
        bool ok = false;
        try
        {
            var r = new LazyRegion(p, len, owner, path, layout);
            r.m_deps = RegionReader.SortDeps(deps);
            ulong rootAddr = *(ulong*)(p + layout.DataOff);
            var region = new CompactedRegionData
            {
                FilePath = path,
                BaseAddr = baseAddr,
                Size = (ulong)len,
                Header = layout.Header,
                RootAddr = rootAddr,
                m_gmp = layout.Header.Gmp,
                m_count = -1,
                m_firstObjOffset = (ulong)r.m_first,
                m_dataEnd = (ulong)r.m_end,
                IdsAreAddresses = true,
                m_deps = r.m_deps,
                m_lazy = r,
            };
            Register(r);
            try
            {
                region.Root = r.Resolve(rootAddr);
            }
            catch
            {
                Unregister(r);
                throw;
            }
            ok = true;
            return region;
        }
        finally
        {
            if (!ok)
            {
                RegionAddressSpace.Release(baseAddr);
                (owner as IDisposable)?.Dispose();
            }
        }
    }

    // ------------------------------------------------------------------
    // Address -> region

    static readonly object s_lock = new();
    static volatile LazyRegion[] s_regions = Array.Empty<LazyRegion>();   // sorted by base address
    [ThreadStatic] static LazyRegion t_last;

    static void Register(LazyRegion r)
    {
        lock (s_lock)
        {
            var old = s_regions;
            int at = LowerBound(old, r.m_base);
            var n = new LazyRegion[old.Length + 1];
            Array.Copy(old, 0, n, 0, at);
            n[at] = r;
            Array.Copy(old, at, n, at + 1, old.Length - at);
            s_regions = n;
        }
    }

    static void Unregister(LazyRegion r)
    {
        lock (s_lock)
        {
            var old = s_regions;
            int at = Array.IndexOf(old, r);
            if (at < 0) return;
            var n = new LazyRegion[old.Length - 1];
            Array.Copy(old, 0, n, 0, at);
            Array.Copy(old, at + 1, n, at, n.Length - at);
            s_regions = n;
        }
    }

    /// <summary>Index of the first region with base address &gt; addr.</summary>
    static int LowerBound(LazyRegion[] a, ulong addr)
    {
        int lo = 0, hi = a.Length;
        while (lo < hi)
        {
            int mid = (lo + hi) >> 1;
            if (a[mid].m_base <= addr) lo = mid + 1; else hi = mid;
        }
        return lo;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static LazyRegion Find(ulong addr)
    {
        var r = t_last;
        if (r != null && addr - r.m_base < (ulong)r.m_len) return r;
        return FindSlow(addr);
    }

    static LazyRegion FindSlow(ulong addr)
    {
        var a = s_regions;
        int i = LowerBound(a, addr);
        if (i == 0) return null;
        var r = a[i - 1];
        if (addr - r.m_base >= (ulong)r.m_len) return null;
        t_last = r;
        return r;
    }

    /// <summary>
    /// Field `i` of the constructor object `o`, which was found to be null: resolves it if `o` is
    /// a shell of a lazily decoded region (otherwise the field really is null).
    /// </summary>
    internal static Obj ForceField(Obj o, uint i)
    {
        ulong id = (ulong)o.m_id;
        if (id < RegionAddressSpace.MinBase) return null;
        var r = Find(id);
        if (r == null) return null;
        Obj c = r.Resolve(*(ulong*)(r.m_p + (id - r.m_base) + 8 + 8 * (ulong)i));
        LeanRt.lean_ctor_set(o, i, c);
        return c;
    }

    // ------------------------------------------------------------------
    // Pointers -> objects

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    Obj Resolve(ulong v)
    {
        if ((v & 1) != 0) return LeanRt.lean_box(v >> 1);
        ulong off = v - m_base;
        if (off < (ulong)m_len) return Materialize((long)off);
        return ResolveDep(v);
    }

    Obj ResolveDep(ulong v)
    {
        var deps = m_deps;
        int lo = 0, hi = deps.Length - 1, found = -1;
        while (lo <= hi)
        {
            int mid = (lo + hi) >> 1;
            if (deps[mid].BaseAddr <= v) { found = mid; lo = mid + 1; } else hi = mid - 1;
        }
        if (found >= 0 && v - deps[found].BaseAddr < deps[found].Size)
            return deps[found].Lookup(v);
        throw new OleanFormatException($"object pointer 0x{v:x} in '{m_path}' is outside of this region and of all dependency regions");
    }

    /// <summary>The object at file offset `off`.</summary>
    internal Obj Materialize(long off)
    {
        if ((off & 7) != 0 || off < m_first || off >= m_end)
            throw new OleanFormatException($"invalid object pointer 0x{m_base + (ulong)off:x} in '{m_path}'");
        int key = (int)(off >> 3);
        var t = m_table;
        if (t != null)
        {
            var keys = t.Keys;
            int mask = keys.Length - 1;
            int i = (int)(((uint)key * 0x9E3779B9u) >> t.Shift);
            while (true)
            {
                int k = Volatile.Read(ref keys[i]);
                if (k == key) return t.Vals[i];
                if (k == 0) break;
                i = (i + 1) & mask;
            }
        }
        return MaterializeSlow(off, key);
    }

    [ThreadStatic] static int t_depth;

    [MethodImpl(MethodImplOptions.NoInlining)]
    Obj MaterializeSlow(long off, int key)
    {
        lock (m_lock)
        {
            var t = m_table;
            if (t == null) m_table = t = new Table(3);
            int mask = t.Keys.Length - 1;
            int i = (int)(((uint)key * 0x9E3779B9u) >> t.Shift);
            while (true)
            {
                int k = t.Keys[i];
                if (k == key) return t.Vals[i];
                if (k == 0) break;
                i = (i + 1) & mask;
            }
            // (arrays & co. create their elements: they are stored before their owners, so
            // the nesting is bounded by the data, but guard against forged files)
            if (++t_depth > 4000) { t_depth = 0; throw Corrupt(off, "object nesting too deep"); }
            Obj o;
            try { o = Decode(off); }
            finally { if (t_depth > 0) t_depth--; }
            // Decoding may have added objects (and replaced the table).
            t = m_table;
            if ((m_count + 1) * 4L > t.Keys.Length * 3L) t = Grow(t);
            mask = t.Keys.Length - 1;
            i = (int)(((uint)key * 0x9E3779B9u) >> t.Shift);
            while (t.Keys[i] != 0) i = (i + 1) & mask;
            t.Vals[i] = o;
            Volatile.Write(ref t.Keys[i], key);
            m_count++;
            return o;
        }
    }

    Table Grow(Table old)
    {
        var t = new Table(33 - old.Shift);
        int mask = t.Keys.Length - 1;
        for (int j = 0; j < old.Keys.Length; j++)
        {
            int k = old.Keys[j];
            if (k == 0) continue;
            int i = (int)(((uint)k * 0x9E3779B9u) >> t.Shift);
            while (t.Keys[i] != 0) i = (i + 1) & mask;
            t.Keys[i] = k;
            t.Vals[i] = old.Vals[j];
        }
        m_table = t;
        return t;
    }

    Exception Corrupt(long pos, string what) =>
        new OleanFormatException($"corrupted compacted region '{m_path}' at offset {pos}: {what}");

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    Obj R(byte* at) => Resolve(*(ulong*)at);

    /// <summary>Byte size (not rounded) of the object stored at `pos`.</summary>
    long SizeAt(long pos)
    {
        long end = m_end;
        if (end - pos < 8) throw Corrupt(pos, "truncated object");
        byte* q = m_p + pos;
        uint hi = *(uint*)(q + 4);
        int tag = (int)(hi >> 24);
        int other = (int)((hi >> 16) & 0xff);
        long sz;
        if (tag <= LeanRt.LeanMaxCtorTag)
        {
            sz = hi & 0xffff;
            if (sz - 8 - 8L * other < 0) throw Corrupt(pos, "bad constructor size");
        }
        else
        {
            if (end - pos < RegionReader.MinSize(tag)) throw Corrupt(pos, "truncated object");
            switch (tag)
            {
                case LeanRt.LeanArray:
                {
                    long n = *(long*)(q + 8);
                    if (n < 0 || n > (end - pos) / 8) throw Corrupt(pos, "bad array size");
                    sz = OleanLayout.ArrayHeader + 8 * n;
                    break;
                }
                case LeanRt.LeanScalarArray:
                {
                    long n = *(long*)(q + 8);
                    int esz = other & 0x7f;
                    if (n < 0 || n > (end - pos) / Math.Max(esz, 1)) throw Corrupt(pos, "bad scalar array size");
                    sz = OleanLayout.SArrayHeader + n * esz;
                    break;
                }
                case LeanRt.LeanString:
                {
                    long n = *(long*)(q + 8);
                    if (n <= 0 || n > end - pos) throw Corrupt(pos, "bad string size");
                    sz = OleanLayout.StringHeader + n;
                    break;
                }
                case LeanRt.LeanMPZ:
                    if (m_gmp)
                    {
                        long nl = Math.Abs((long)*(int*)(q + 12));
                        sz = OleanLayout.MpzGmpHeader + 8 * nl;
                    }
                    else
                    {
                        long nd = *(long*)(q + 16);
                        if (nd < 0 || nd > (end - pos) / 4) throw Corrupt(pos, "bad mpz size");
                        sz = OleanLayout.MpzLeanHeader + 4 * nd;
                    }
                    break;
                case LeanRt.LeanThunk: sz = OleanLayout.ThunkSize; break;
                case LeanRt.LeanTask: sz = OleanLayout.TaskSize; break;
                case LeanRt.LeanPromise: sz = OleanLayout.PromiseSize; break;
                case LeanRt.LeanRef: sz = OleanLayout.RefSize; break;
                case LeanRt.LeanClosure:
                    sz = OleanLayout.ClosureHeader + 8L * *(ushort*)(q + 18);
                    break;
                default:
                    throw Corrupt(pos, $"unexpected object tag {tag}");
            }
        }
        if (pos + sz > end) throw Corrupt(pos, "object extends beyond the end of the data");
        return sz;
    }

    Obj Decode(long pos)
    {
        long sz = SizeAt(pos);
        byte* q = m_p + pos;
        uint hi = *(uint*)(q + 4);
        int tag = (int)(hi >> 24);
        int other = (int)((hi >> 16) & 0xff);
        Obj o;
        if (tag <= LeanRt.LeanMaxCtorTag)
        {
            Ctor c = other switch
            {
                0 => new Ctor(),
                1 => new Ctor1(),
                2 => new Ctor2(),
                3 => new Ctor3(),
                4 => new Ctor4(),
                5 => new Ctor5(),
                6 => new Ctor6(),
                7 => new Ctor7(),
                8 => new Ctor8(),
                _ => new CtorN { rest = new Obj[other - 8] },
            };
            c.m_tag = (byte)tag;
            c.m_other = (byte)other;
            long ssz = sz - 8 - 8L * other;
            if (ssz != 0)
            {
                byte* s = q + 8 + 8 * other;
                c.m_cs_sz = (ushort)ssz;
                if (ssz >= 8) c.s0 = *(ulong*)s;
                else { ulong s0 = 0; for (int i = 0; i < ssz; i++) s0 |= (ulong)s[i] << (8 * i); c.s0 = s0; }
                if (ssz > 8) c.sx = new ReadOnlySpan<byte>(s + 8, (int)(ssz - 8)).ToArray();
            }
            o = c;
        }
        else
        {
            switch (tag)
            {
                case LeanRt.LeanArray:
                {
                    long n = *(long*)(q + 8);
                    var data = n == 0 ? Array.Empty<Obj>() : new Obj[n];
                    byte* e = q + OleanLayout.ArrayHeader;
                    for (long i = 0; i < n; i++) data[i] = R(e + 8 * i);
                    o = new ArrayObj { m_tag = LeanRt.LeanArray, m_data = data, m_size = n };
                    break;
                }
                case LeanRt.LeanScalarArray:
                {
                    long n = *(long*)(q + 8);
                    int esz = other & 0x7f;
                    var data = new ReadOnlySpan<byte>(q + OleanLayout.SArrayHeader, (int)(n * esz)).ToArray();
                    o = new SArrayObj { m_tag = LeanRt.LeanScalarArray, m_other = (byte)esz, m_data = data, m_size = n, m_capacity = n };
                    break;
                }
                case LeanRt.LeanString:
                {
                    long n = *(long*)(q + 8);
                    var data = new ReadOnlySpan<byte>(q + OleanLayout.StringHeader, (int)n).ToArray();
                    o = new StrObj { m_tag = LeanRt.LeanString, m_data = data, m_size = n, m_length = *(long*)(q + 24) };
                    break;
                }
                case LeanRt.LeanMPZ:
                {
                    BigInteger v;
                    if (m_gmp)
                    {
                        int msz = *(int*)(q + 12);
                        v = new BigInteger(new ReadOnlySpan<byte>(q + OleanLayout.MpzGmpHeader, (int)(sz - OleanLayout.MpzGmpHeader)), isUnsigned: true, isBigEndian: false);
                        if (msz < 0) v = -v;
                    }
                    else
                    {
                        v = new BigInteger(new ReadOnlySpan<byte>(q + OleanLayout.MpzLeanHeader, (int)(sz - OleanLayout.MpzLeanHeader)), isUnsigned: true, isBigEndian: false);
                        if (q[8] != 0) v = -v;
                    }
                    o = new MpzObj { m_tag = LeanRt.LeanMPZ, m_value = v };
                    break;
                }
                case LeanRt.LeanThunk:
                    o = new ThunkObj { m_tag = LeanRt.LeanThunk, m_value = R(q + 8) };
                    break;
                case LeanRt.LeanTask:
                    o = new TaskObj { m_tag = LeanRt.LeanTask, m_value = R(q + 8) };
                    break;
                case LeanRt.LeanPromise:
                {
                    var t = R(q + 8);
                    if (t.m_tag != LeanRt.LeanTask) throw Corrupt(pos, "promise result is not a task");
                    o = new PromiseObj { m_tag = LeanRt.LeanPromise, m_result = Unsafe.As<TaskObj>(t) };
                    break;
                }
                case LeanRt.LeanRef:
                    o = new RefObj { m_tag = LeanRt.LeanRef, m_value = R(q + 8) };
                    break;
                case LeanRt.LeanClosure:
                {
                    if (!m_closuresOk)
                        throw new OleanFormatException("library required for closure relocation is not loaded in this process (the file was saved by a different LeanInterpreter build)");
                    ulong funIndex = *(ulong*)(q + 8);
                    if (m_functions == null || funIndex >= (ulong)m_functions.Length) throw Corrupt(pos, "bad closure function");
                    ushort nfixed = *(ushort*)(q + 18);
                    var args = nfixed == 0 ? Array.Empty<Obj>() : new Obj[nfixed];
                    for (int i = 0; i < nfixed; i++) args[i] = R(q + OleanLayout.ClosureHeader + 8 * i);
                    o = new Closure { m_tag = LeanRt.LeanClosure, m_fun = (void*)m_functions[funIndex], m_arity = *(ushort*)(q + 16), m_num_fixed = nfixed, m_objs = args };
                    break;
                }
                default:
                    throw Corrupt(pos, $"unexpected object tag {tag}");
            }
        }
        o.m_rc = 0;
        o.m_id = (long)(m_base + (ulong)pos);
        return o;
    }

    // ------------------------------------------------------------------
    // Whole-region operations (only needed by tools and fallback paths)

    /// <summary>Number of objects stored in the file.</summary>
    internal int CountObjects()
    {
        int n = 0;
        for (long pos = m_first; pos < m_end; pos += OleanLayout.Align8(SizeAt(pos))) n++;
        return n;
    }

    /// <summary>All objects in file order.</summary>
    internal Obj[] MaterializeAll()
    {
        var l = new List<Obj>();
        for (long pos = m_first; pos < m_end; pos += OleanLayout.Align8(SizeAt(pos))) l.Add(Materialize(pos));
        return l.ToArray();
    }

    /// <summary>Forgets the objects created so far (the region was freed by the program).</summary>
    internal void DropObjects()
    {
        lock (m_lock) { m_table = null; m_count = 0; }
    }

    // ------------------------------------------------------------------
    // Statistics (LEANINTERP_TRACE_OLEAN=1: summary on stderr at exit)

    internal static (int Regions, long Bytes, long Objects) Stats()
    {
        var a = s_regions;
        long bytes = 0, objs = 0;
        foreach (var r in a) { bytes += r.m_len; objs += r.m_count; }
        return (a.Length, bytes, objs);
    }

    static LazyRegion()
    {
        if (Environment.GetEnvironmentVariable("LEANINTERP_TRACE_OLEAN") == "1")
            AppDomain.CurrentDomain.ProcessExit += (_, _) =>
            {
                var (n, bytes, objs) = Stats();
                Console.Error.WriteLine($"[olean] {n} lazily decoded regions, {bytes / (1024.0 * 1024.0):F0} MB mapped, {objs} objects created");
                var gc = GC.GetGCMemoryInfo();
                Console.Error.WriteLine($"[olean] managed heap {gc.HeapSizeBytes >> 20} MB (after the last GC), allocated in total {GC.GetTotalAllocatedBytes() >> 20} MB");
                try
                {
                    foreach (var line in File.ReadLines("/proc/self/status"))
                        if (line.StartsWith("RssAnon") || line.StartsWith("RssFile") || line.StartsWith("VmHWM"))
                            Console.Error.WriteLine("[olean] " + string.Join(' ', line.Split((char[])null, StringSplitOptions.RemoveEmptyEntries)));
                }
                catch (Exception) { }
            };
    }
}
