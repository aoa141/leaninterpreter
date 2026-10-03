// Reader for compacted regions: port of `region_reader` (runtime/compact.cpp) and of the file
// handling of `lean_compacted_region_read` (library/module.cpp). Instead of fixing up pointers in a
// mapped buffer, every object is converted into a managed object in a single pass over the file
// (children are always stored before their parents). All resulting objects are persistent
// (`m_rc == 0`), as objects in native compacted regions are.

using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace LeanInterpreter.Runtime.Compact;

/// <summary>Where the parts of a compacted region file are.</summary>
internal struct RegionLayout
{
    public OleanHeader Header;
    public long DataOff, DataSize;
    public bool ClosuresOk;
    public nint[] Functions;
}

internal sealed unsafe class RegionReader
{
    // Per-thread scratch buffers, reused across reads (importing reads thousands of files).
    [ThreadStatic] static byte[] t_file;
    [ThreadStatic] static Obj[] t_ordered;

    /// <summary>Build the file-order index while reading instead of on demand (for testing).</summary>
    internal static bool EagerIndex = false;

    /// <summary>Scratch buffers larger than this are not kept after a read.</summary>
    const long KeepScratchBytes = 256L << 20;

    Obj[] m_byWord;
    ulong m_base;
    ulong m_fileSize;
    CompactedRegionData[] m_deps;   // sorted by BaseAddr
    string m_path;
    bool m_gmp;
    bool m_closuresOk;
    bool m_assignIds;
    nint[] m_functions;   // function table of the file (closures)
    int m_thread = Environment.CurrentManagedThreadId;

    public static CompactedRegionData ReadFile(string path, IReadOnlyList<CompactedRegionData> deps)
    {
        byte[] buf;
        long len;
        using (var h = File.OpenHandle(path, FileMode.Open, FileAccess.Read, FileShare.Read | FileShare.Delete))
        {
            len = RandomAccess.GetLength(h);
            buf = t_file;
            if (buf == null || buf.LongLength < len)
                buf = GC.AllocateUninitializedArray<byte>((int)Math.Max(len, 1 << 20));
            long done = 0;
            while (done < len)
            {
                int n = RandomAccess.Read(h, buf.AsSpan((int)done, (int)(len - done)), done);
                if (n <= 0) throw new OleanFormatException("unexpected end of file");
                done += n;
            }
        }
        t_file = buf.LongLength <= KeepScratchBytes ? buf : null;
        return Parse(path, buf, len, deps);
    }

    /// <summary>Checks the header and locates the object data and the function table.</summary>
    internal static RegionLayout ParseLayout(byte* buf, long len)
    {
        if (!OleanHeader.TryParse(new ReadOnlySpan<byte>(buf, (int)Math.Min(len, OleanHeader.Size)), out var hdr))
            throw new OleanFormatException("invalid header");
        if (hdr.Version != 2 && hdr.Version != 3)
            throw new OleanFormatException("incompatible header");
        if ((hdr.Flags & ~1) != 0)
            throw new OleanFormatException("incompatible header");

        long dataOff = OleanHeader.Size;
        long dataSize = len - OleanHeader.Size;
        bool closuresOk = true;
        nint[] functions = null;
        if (hdr.Version == 3)
        {
            if (len < OleanHeader.Size + 8) throw new OleanFormatException("truncated file");
            dataSize = (long)*(ulong*)(buf + OleanHeader.Size);
            dataOff = OleanHeader.Size + 8;
            if (dataSize < 0 || dataSize > len - dataOff) throw new OleanFormatException("invalid data size");
            long p = dataOff + dataSize;
            uint U32(long at) => at >= 0 && at + 4 <= len ? *(uint*)(buf + at) : throw new OleanFormatException("truncated file");
            long numClosures = U32(p);
            p += 4 + 8 * numClosures;
            if (numClosures > 0)
            {
                // The functions of the closures, by name (see `FunctionTable`).
                uint nlibs = U32(p);
                p += 4;
                if (nlibs > (len - p) / 12) throw new OleanFormatException("truncated file");
                functions = new nint[nlibs];
                for (uint i = 0; i < nlibs; i++)
                {
                    p += 8;
                    long idLen = U32(p);
                    p += 4;
                    if (p + idLen > len) throw new OleanFormatException("truncated file");
                    string id = System.Text.Encoding.UTF8.GetString(buf + p, (int)idLen);
                    p += idLen;
                    functions[i] = (nint)FunctionTable.Resolve(id);
                    if (functions[i] == 0) closuresOk = false;
                }
            }
        }
        if (dataSize < 8) throw new OleanFormatException("truncated file");
        return new RegionLayout { Header = hdr, DataOff = dataOff, DataSize = dataSize, ClosuresOk = closuresOk, Functions = functions };
    }

    public static CompactedRegionData Parse(string path, byte[] buf, long len, IReadOnlyList<CompactedRegionData> deps)
    {
        RegionLayout layout;
        fixed (byte* p0 = buf) layout = ParseLayout(p0, len);
        var hdr = layout.Header;
        long dataOff = layout.DataOff, dataSize = layout.DataSize;
        bool closuresOk = layout.ClosuresOk;
        nint[] functions = layout.Functions;

        var r = new RegionReader
        {
            m_base = hdr.BaseAddr,
            m_fileSize = (ulong)len,
            m_path = path,
            m_gmp = hdr.Gmp,
            m_closuresOk = closuresOk,
            m_functions = functions,
            // Give the objects their logical address as identity (`ptrAddrUnsafe`), as natively,
            // unless the address range is already taken (the file was read before, or two
            // files happen to overlap): then they get ids from the counter as usual.
            m_assignIds = RegionAddressSpace.TryReserve(hdr.BaseAddr, (ulong)len),
        };
        r.SetDeps(deps);

        long nwords = (len + 7) >> 3;
        long maxObjs = dataSize >> 3;
        var slot = AcquireDenseSlot(nwords, r.m_deps);
        var byWord = slot.Words;
        Obj[] ordered = null;
        if (EagerIndex)
        {
            ordered = t_ordered;
            if (ordered == null || ordered.LongLength < maxObjs) ordered = new Obj[Math.Max(maxObjs, 1 << 17)];
        }
        r.m_byWord = byWord;

        int count = 0;
        bool ok = false;
        try
        {
            fixed (byte* p = buf)
            {
                count = r.ReadObjects(p, dataOff + 8, dataOff + dataSize, ordered);
                ulong rootAddr = *(ulong*)(p + dataOff);
                Obj root = r.Resolve(rootAddr);
                var region = new CompactedRegionData
                {
                    FilePath = path,
                    BaseAddr = hdr.BaseAddr,
                    Size = (ulong)len,
                    Header = hdr,
                    Root = root,
                    RootAddr = rootAddr,
                    m_gmp = hdr.Gmp,
                    m_count = count,
                    m_firstObjOffset = (ulong)(dataOff + 8),
                };
                region.m_dataEnd = (ulong)(dataOff + dataSize);
                region.IdsAreAddresses = r.m_assignIds;
                region.m_deps = r.m_deps;
                if (EagerIndex)
                {
                    var objs = new Obj[count];
                    Array.Copy(ordered, objs, count);
                    region.SetIndex(objs);
                }
                // Keep the word index of this region around for a while: the next reads typically
                // use it as a dependency (`.olean` -> `.olean.server` -> `.olean.private`).
                slot.Region = region;
                region.m_dense = byWord;
                region.m_denseThread = Environment.CurrentManagedThreadId;
                ok = true;
                return region;
            }
        }
        finally
        {
            // Do not keep objects alive through the scratch buffer.
            if (ordered != null)
            {
                Array.Clear(ordered, 0, ok ? count : ordered.Length);
                t_ordered = ordered.LongLength * 8 <= KeepScratchBytes ? ordered : null;
            }
            if (!ok)
            {
                ReleaseDenseSlot(slot);
                if (r.m_assignIds) RegionAddressSpace.Release(hdr.BaseAddr);
            }
        }
    }

    // ------------------------------------------------------------------
    // Word-indexed maps (file offset / 8 -> object) of recently read regions, per thread. The map of
    // the region being read is needed anyway; keeping the last few allows O(1) resolution of
    // pointers into them from the following reads.

    sealed class DenseSlot
    {
        public Obj[] Words;
        public long NWords;      // number of possibly non-null entries
        public CompactedRegionData Region;
        public long Stamp;
    }

    const int NumDenseSlots = 4;
    [ThreadStatic] static DenseSlot[] t_slots;
    [ThreadStatic] static long t_stamp;

    static DenseSlot AcquireDenseSlot(long nwords, CompactedRegionData[] deps)
    {
        var slots = t_slots ??= new DenseSlot[NumDenseSlots];
        // Prefer a free slot, then the least recently used one whose region is not a dependency of
        // the current read.
        DenseSlot best = null;
        int bestRank = int.MaxValue;
        for (int i = 0; i < slots.Length; i++)
        {
            var s = slots[i] ??= new DenseSlot();
            int rank = s.Region == null ? 0 : Array.IndexOf(deps, s.Region) < 0 ? 1 : 2;
            if (rank < bestRank || (rank == bestRank && s.Stamp < best.Stamp)) { best = s; bestRank = rank; }
        }
        ReleaseDenseSlot(best);
        if (best.Words == null || best.Words.LongLength < nwords)
        {
            best.Words = null;
            best.Words = new Obj[Math.Max(nwords, 1 << 16)];
        }
        best.NWords = nwords;
        best.Stamp = ++t_stamp;
        return best;
    }

    /// <summary>Drops the scratch buffers and recent-region indices of the current thread.</summary>
    internal static void ReleaseScratch()
    {
        if (t_slots != null)
            foreach (var s in t_slots)
                if (s != null) { ReleaseDenseSlot(s); s.Words = null; }
        t_slots = null;
        t_ordered = null;
        t_file = null;
    }

    static void ReleaseDenseSlot(DenseSlot s)
    {
        if (s.Region != null)
        {
            s.Region.m_dense = null;
            s.Region = null;
        }
        if (s.Words != null)
        {
            Array.Clear(s.Words, 0, (int)Math.Min(s.NWords, s.Words.LongLength));
            if (s.Words.LongLength * 8 > KeepScratchBytes) s.Words = null;
        }
        s.NWords = 0;
    }

    void SetDeps(IReadOnlyList<CompactedRegionData> deps) => m_deps = SortDeps(deps);

    internal static CompactedRegionData[] SortDeps(IReadOnlyList<CompactedRegionData> deps)
    {
        if (deps == null || deps.Count == 0) return Array.Empty<CompactedRegionData>();
        var l = new List<CompactedRegionData>(deps.Count);
        foreach (var d in deps)
            if (d != null && !l.Contains(d)) l.Add(d);
        l.Sort((a, b) => a.BaseAddr.CompareTo(b.BaseAddr));
        for (int i = 1; i < l.Count; i++)
            if (l[i - 1].BaseAddr + l[i - 1].Size > l[i].BaseAddr)
                throw new OleanFormatException("region_reader: dep regions have overlapping `base_addr` ranges");
        return l.ToArray();
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    Obj R(byte* at) => Resolve(*(ulong*)at);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    Obj Resolve(ulong v)
    {
        if ((v & 1) != 0) return LeanRt.lean_box(v >> 1);
        ulong off = v - m_base;
        if (off < m_fileSize)
        {
            var o = Unsafe.Add(ref MemoryMarshal.GetArrayDataReference(m_byWord), (nint)(off >> 3));
            if (o != null) return o;
            return BadPointer(v);
        }
        return ResolveDep(v);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    Obj BadPointer(ulong v) =>
        throw new OleanFormatException($"invalid object pointer 0x{v:x} (forward reference or not an object start)");

    [MethodImpl(MethodImplOptions.NoInlining)]
    Obj ResolveDep(ulong v)
    {
        var deps = m_deps;
        int lo = 0, hi = deps.Length - 1, found = -1;
        while (lo <= hi)
        {
            int mid = (lo + hi) >> 1;
            if (deps[mid].BaseAddr <= v) { found = mid; lo = mid + 1; } else hi = mid - 1;
        }
        if (found >= 0)
        {
            var d = deps[found];
            ulong off = v - d.BaseAddr;
            if (off < d.Size)
            {
                var dense = d.m_dense;
                if (dense != null && d.m_denseThread == m_thread)
                {
                    var o = dense[off >> 3];
                    if (o != null) return o;
                }
                return d.Lookup(v);
            }
        }
        throw new OleanFormatException($"object pointer 0x{v:x} is outside of this region and of all dependency regions");
    }

    static Exception Corrupt(long pos, string what) =>
        new OleanFormatException($"corrupted compacted region at offset {pos}: {what}");

    int ReadObjects(byte* p, long pos, long end, Obj[] ordered)
    {
        int count = 0;
        ref Obj byWord0 = ref MemoryMarshal.GetArrayDataReference(m_byWord);
        bool keepOrder = ordered != null;
        ref Obj ordered0 = ref keepOrder ? ref MemoryMarshal.GetArrayDataReference(ordered) : ref Unsafe.NullRef<Obj>();
        bool gmp = m_gmp;
        bool assignIds = m_assignIds;
        ulong baseAddr = m_base;
        while (pos < end)
        {
            byte* q = p + pos;
            uint hi = *(uint*)(q + 4);
            int tag = (int)(hi >> 24);
            int other = (int)((hi >> 16) & 0xff);
            int csz = (int)(hi & 0xffff);
            long sz;
            Obj o;
            if (end - pos < 32 && end - pos < MinSize(tag)) throw Corrupt(pos, "truncated object");
            if (tag <= LeanRt.LeanMaxCtorTag)
            {
                sz = csz;
                long ssz = sz - 8 - 8L * other;
                if (ssz < 0 || pos + sz > end) throw Corrupt(pos, "bad constructor size");
                Ctor c = MkCtor(other, q + 8);
                c.m_rc = 0;
                c.m_tag = (byte)tag;
                c.m_other = (byte)other;
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
                        if (n < 0 || n > (end - pos) / 8) throw Corrupt(pos, "bad array size");
                        sz = OleanLayout.ArrayHeader + 8 * n;
                        if (pos + sz > end) throw Corrupt(pos, "bad array size");
                        var data = n == 0 ? Array.Empty<Obj>() : new Obj[n];
                        byte* e = q + OleanLayout.ArrayHeader;
                        ref Obj d0 = ref MemoryMarshal.GetArrayDataReference(data);
                        for (long i = 0; i < n; i++) Unsafe.Add(ref d0, (nint)i) = R(e + 8 * i);
                        o = new ArrayObj { m_rc = 0, m_tag = LeanRt.LeanArray, m_data = data, m_size = n };
                        break;
                    }
                    case LeanRt.LeanScalarArray:
                    {
                        long n = *(long*)(q + 8);
                        int esz = other & 0x7f;
                        if (n < 0 || n > (end - pos) / Math.Max(esz, 1)) throw Corrupt(pos, "bad scalar array size");
                        long nbytes = n * esz;
                        sz = OleanLayout.SArrayHeader + nbytes;
                        if (pos + sz > end) throw Corrupt(pos, "bad scalar array size");
                        var data = new ReadOnlySpan<byte>(q + OleanLayout.SArrayHeader, (int)nbytes).ToArray();
                        o = new SArrayObj { m_rc = 0, m_tag = LeanRt.LeanScalarArray, m_other = (byte)esz, m_data = data, m_size = n, m_capacity = n };
                        break;
                    }
                    case LeanRt.LeanString:
                    {
                        long n = *(long*)(q + 8);
                        long length = *(long*)(q + 24);
                        if (n <= 0 || n > end - pos) throw Corrupt(pos, "bad string size");
                        sz = OleanLayout.StringHeader + n;
                        if (pos + sz > end) throw Corrupt(pos, "bad string size");
                        var data = new ReadOnlySpan<byte>(q + OleanLayout.StringHeader, (int)n).ToArray();
                        o = new StrObj { m_rc = 0, m_tag = LeanRt.LeanString, m_data = data, m_size = n, m_length = length };
                        break;
                    }
                    case LeanRt.LeanMPZ:
                    {
                        BigInteger v;
                        if (gmp)
                        {
                            int msz = *(int*)(q + 12);
                            long nl = Math.Abs((long)msz);
                            sz = OleanLayout.MpzGmpHeader + 8 * nl;
                            if (pos + sz > end) throw Corrupt(pos, "bad mpz size");
                            v = new BigInteger(new ReadOnlySpan<byte>(q + OleanLayout.MpzGmpHeader, (int)(8 * nl)), isUnsigned: true, isBigEndian: false);
                            if (msz < 0) v = -v;
                        }
                        else
                        {
                            bool neg = q[8] != 0;
                            long nd = *(long*)(q + 16);
                            if (nd < 0 || nd > (end - pos) / 4) throw Corrupt(pos, "bad mpz size");
                            sz = OleanLayout.MpzLeanHeader + 4 * nd;
                            if (pos + sz > end) throw Corrupt(pos, "bad mpz size");
                            v = new BigInteger(new ReadOnlySpan<byte>(q + OleanLayout.MpzLeanHeader, (int)(4 * nd)), isUnsigned: true, isBigEndian: false);
                            if (neg) v = -v;
                        }
                        o = new MpzObj { m_rc = 0, m_tag = LeanRt.LeanMPZ, m_value = v };
                        break;
                    }
                    case LeanRt.LeanThunk:
                        sz = OleanLayout.ThunkSize;
                        o = new ThunkObj { m_rc = 0, m_tag = LeanRt.LeanThunk, m_value = R(q + 8) };
                        break;
                    case LeanRt.LeanTask:
                        sz = OleanLayout.TaskSize;
                        o = new TaskObj { m_rc = 0, m_tag = LeanRt.LeanTask, m_value = R(q + 8) };
                        break;
                    case LeanRt.LeanPromise:
                    {
                        sz = OleanLayout.PromiseSize;
                        var t = R(q + 8);
                        if (t.m_tag != LeanRt.LeanTask) throw Corrupt(pos, "promise result is not a task");
                        o = new PromiseObj { m_rc = 0, m_tag = LeanRt.LeanPromise, m_result = Unsafe.As<TaskObj>(t) };
                        break;
                    }
                    case LeanRt.LeanRef:
                        sz = OleanLayout.RefSize;
                        o = new RefObj { m_rc = 0, m_tag = LeanRt.LeanRef, m_value = R(q + 8) };
                        break;
                    case LeanRt.LeanClosure:
                    {
                        if (!m_closuresOk)
                            throw new OleanFormatException("library required for closure relocation is not loaded in this process (the file was saved by a different LeanInterpreter build)");
                        ulong funIndex = *(ulong*)(q + 8);
                        if (m_functions == null || funIndex >= (ulong)m_functions.Length) throw Corrupt(pos, "bad closure function");
                        void* fun = (void*)m_functions[funIndex];
                        ushort arity = *(ushort*)(q + 16);
                        ushort nfixed = *(ushort*)(q + 18);
                        sz = OleanLayout.ClosureHeader + 8L * nfixed;
                        if (pos + sz > end) throw Corrupt(pos, "bad closure size");
                        var args = nfixed == 0 ? Array.Empty<Obj>() : new Obj[nfixed];
                        for (int i = 0; i < nfixed; i++) args[i] = R(q + OleanLayout.ClosureHeader + 8 * i);
                        o = new Closure { m_rc = 0, m_tag = LeanRt.LeanClosure, m_fun = fun, m_arity = arity, m_num_fixed = nfixed, m_objs = args };
                        break;
                    }
                    default:
                        throw Corrupt(pos, $"unexpected object tag {tag}");
                }
            }
            Unsafe.Add(ref byWord0, (nint)(pos >> 3)) = o;
            // (a small big number is read as a shared boxed scalar: no identity)
            if (assignIds && o.m_tag != LeanRt.LeanBoxTag) o.m_id = (long)(baseAddr + (ulong)pos);
            if (keepOrder)
            {
                if ((ulong)count >= (ulong)ordered.Length) throw Corrupt(pos, "too many objects");
                Unsafe.Add(ref ordered0, count) = o;
            }
            count++;
            pos += (sz + 7) & ~7L;
        }
        return count;
    }

    internal static long MinSize(int tag) => tag switch
    {
        <= LeanRt.LeanMaxCtorTag => 8,
        LeanRt.LeanArray or LeanRt.LeanScalarArray or LeanRt.LeanClosure or LeanRt.LeanMPZ or LeanRt.LeanThunk or LeanRt.LeanTask => 24,
        LeanRt.LeanString => 32,
        _ => 16,
    };

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    Ctor MkCtor(int n, byte* f)
    {
        switch (n)
        {
            case 0: return new Ctor();
            case 1: return new Ctor1 { f0 = R(f) };
            case 2: return new Ctor2 { f0 = R(f), f1 = R(f + 8) };
            case 3: return new Ctor3 { f0 = R(f), f1 = R(f + 8), f2 = R(f + 16) };
            case 4: return new Ctor4 { f0 = R(f), f1 = R(f + 8), f2 = R(f + 16), f3 = R(f + 24) };
            default: return MkCtorBig(n, f);
        }
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    Ctor MkCtorBig(int n, byte* f)
    {
        switch (n)
        {
            case 5: return new Ctor5 { f0 = R(f), f1 = R(f + 8), f2 = R(f + 16), f3 = R(f + 24), f4 = R(f + 32) };
            case 6: return new Ctor6 { f0 = R(f), f1 = R(f + 8), f2 = R(f + 16), f3 = R(f + 24), f4 = R(f + 32), f5 = R(f + 40) };
            case 7: return new Ctor7 { f0 = R(f), f1 = R(f + 8), f2 = R(f + 16), f3 = R(f + 24), f4 = R(f + 32), f5 = R(f + 40), f6 = R(f + 48) };
            case 8: return new Ctor8 { f0 = R(f), f1 = R(f + 8), f2 = R(f + 16), f3 = R(f + 24), f4 = R(f + 32), f5 = R(f + 40), f6 = R(f + 48), f7 = R(f + 56) };
            default:
            {
                var rest = new Obj[n - 8];
                for (int i = 0; i < rest.Length; i++) rest[i] = R(f + 64 + 8 * i);
                return new CtorN { f0 = R(f), f1 = R(f + 8), f2 = R(f + 16), f3 = R(f + 24), f4 = R(f + 32), f5 = R(f + 40), f6 = R(f + 48), f7 = R(f + 56), rest = rest };
            }
        }
    }
}

/// <summary>
/// Address ranges of the loaded regions whose objects use their logical address as identity
/// (`Obj.m_id`). Ranges never overlap, and they lie above the ids handed out by the counter in
/// `LeanRt.lean_ptr_addr`, so an id identifies an object, and for these regions also its region
/// and file offset (used by `ObjectCompactor` to refer to objects of dependency regions).
/// A range stays reserved for the lifetime of the process: objects with those ids may live on
/// after the region is released.
/// </summary>
internal static class RegionAddressSpace
{
    /// <summary>Ids from the counter stay below this (2^36 objects would be needed to reach it).</summary>
    internal const ulong MinBase = 1UL << 40;

    static readonly object s_lock = new();
    static readonly SortedList<ulong, ulong> s_ranges = new(); // base -> end

    public static bool TryReserve(ulong baseAddr, ulong size)
    {
        if (baseAddr < MinBase || size == 0 || baseAddr + size < baseAddr || (long)(baseAddr + size) < 0) return false;
        ulong end = baseAddr + size;
        lock (s_lock)
        {
            // first range with base >= baseAddr, and the one before it
            int lo = 0, hi = s_ranges.Count;
            while (lo < hi)
            {
                int mid = (lo + hi) >> 1;
                if (s_ranges.Keys[mid] < baseAddr) lo = mid + 1; else hi = mid;
            }
            if (lo < s_ranges.Count && s_ranges.Keys[lo] < end) return false;
            if (lo > 0 && s_ranges.Values[lo - 1] > baseAddr) return false;
            s_ranges.Add(baseAddr, end);
            return true;
        }
    }

    /// <summary>Gives a range back (only for a read that failed: none of its objects escaped).</summary>
    public static void Release(ulong baseAddr)
    {
        lock (s_lock) s_ranges.Remove(baseAddr);
    }
}
