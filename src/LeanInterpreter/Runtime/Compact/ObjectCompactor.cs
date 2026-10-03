// Port of `object_compactor` (runtime/compact.cpp) and of the file writing part of
// `lean_compacted_region_save` (library/module.cpp).
//
// The output is byte-compatible with native Lean: objects are emitted in the same (depth-first,
// children-first, fields in order) order, with the same maximal sharing of structurally equal
// objects, so compacting the same object graph produces the same bytes as native Lean. The traversal
// uses an explicit stack instead of recursion (deep lists would overflow the managed stack).

using System.Numerics;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace LeanInterpreter.Runtime.Compact;

public sealed unsafe class ObjectCompactor
{
    const int InitSize = 1024 * 1024;

    byte[] m_buf = new byte[InitSize];
    long m_end;
    readonly ulong m_baseAddr;
    readonly bool m_allowClosures;
    readonly bool m_gmp;
    readonly Dictionary<Obj, ulong> m_objTable = new(1 << 16, ReferenceEqualityComparer.Instance);
    readonly MaxSharingTable m_maxSharing;
    readonly List<CompactedRegionData> m_depRegions;
    Dictionary<Obj, ulong> m_depAddr;   // built on first use, for dep regions without address ids
    CompactedRegionData[] m_depsByAddr;  // dep regions whose object ids are addresses, sorted by base
    readonly List<long> m_closureOffsets = new();
    readonly List<nint> m_functions = new();
    readonly Dictionary<nint, int> m_functionIndex = new();

    /// <summary>The functions of the closures compacted so far (a closure's `m_fun` slot holds the index).</summary>
    internal List<nint> Functions => m_functions;

    int FunctionIndex(nint fn)
    {
        if (!m_functionIndex.TryGetValue(fn, out int i))
        {
            i = m_functions.Count;
            m_functions.Add(fn);
            m_functionIndex.Add(fn, i);
        }
        return i;
    }

    // Explicit traversal stack.
    ulong[] m_tmp = new ulong[1024];
    int m_tmpCount;
    Frame[] m_frames = new Frame[256];
    int m_frameCount;

    struct Frame
    {
        public Obj Obj;
        public long Next;
        public long Count;
        public int Base;
    }

    /// <param name="baseAddr">Logical address of buffer offset 0.</param>
    /// <param name="depRegions">Loaded regions whose objects are referenced instead of being copied.</param>
    /// <param name="gmp">Write big numbers in the GMP layout (as the native Lean release build does).</param>
    public ObjectCompactor(ulong baseAddr, IEnumerable<CompactedRegionData> depRegions = null, bool allowClosures = false, bool gmp = true)
    {
        m_baseAddr = baseAddr;
        m_allowClosures = allowClosures;
        m_gmp = gmp;
        m_maxSharing = new MaxSharingTable(this);
        m_depRegions = depRegions?.Where(r => r != null).ToList() ?? new List<CompactedRegionData>();
    }

    public ulong BaseAddr => m_baseAddr;
    public bool Gmp => m_gmp;
    public bool AllowClosures => m_allowClosures;
    /// <summary>Number of bytes compacted so far (including reserved header space of all parts).</summary>
    public long Size => m_end;
    public ReadOnlySpan<byte> Data => new ReadOnlySpan<byte>(m_buf, 0, (int)m_end);
    internal List<long> ClosureOffsets => m_closureOffsets;

    /// <summary>Allocate `sz` zeroed bytes (rounded up to a multiple of 8); returns the buffer offset.</summary>
    public long Alloc(long sz)
    {
        sz = (sz + 7) & ~7L;
        if (m_end + sz > m_buf.LongLength)
        {
            long cap = m_buf.LongLength;
            while (m_end + sz > cap) cap *= 2;
            if (cap > Array.MaxLength) cap = Array.MaxLength;
            if (m_end + sz > cap) throw new OleanFormatException("compacted region too big");
            var nb = GC.AllocateUninitializedArray<byte>((int)cap);
            Buffer.BlockCopy(m_buf, 0, nb, 0, (int)m_end);
            m_buf = nb;
        }
        long r = m_end;
        m_buf.AsSpan((int)r, (int)sz).Clear();
        m_end += sz;
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    ulong AddrOf(long bufOffset) => (ulong)bufOffset + m_baseAddr;

    ulong Save(Obj o, long newOff)
    {
        ulong off = AddrOf(newOff);
        m_objTable[o] = off;
        return off;
    }

    ulong SaveMaxSharing(Obj o, long newOff, long size)
    {
        long existing = m_maxSharing.FindOrAdd(newOff, size);
        if (existing >= 0)
        {
            m_end = newOff;
            newOff = existing;
        }
        return Save(o, newOff);
    }

    /// <summary>`object_compactor::operator()`: reserve the root slot, compact `o`, store its address.</summary>
    public void Compact(Obj o)
    {
        // Discard traversal state left over by a failed compaction.
        Array.Clear(m_frames, 0, m_frameCount);
        m_frameCount = 0;
        m_tmpCount = 0;
        long rootOff = Alloc(8);
        ulong off = ToOffset(o);
        WriteU64(rootOff, off);
    }

    // ------------------------------------------------------------------

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    void WriteU64(long at, ulong v) => Unsafe.WriteUnaligned(ref m_buf[at], v);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    void WriteU32(long at, uint v) => Unsafe.WriteUnaligned(ref m_buf[at], v);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    void WriteU16(long at, ushort v) => Unsafe.WriteUnaligned(ref m_buf[at], v);

    /// <summary>`lean_set_non_heap_header`: m_rc = 0, m_cs_sz = sz, m_other, m_tag.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    void WriteHeader(long at, long sz, int tag, int other)
    {
        ulong h = ((ulong)(ushort)sz << 32) | ((ulong)(byte)other << 48) | ((ulong)(byte)tag << 56);
        WriteU64(at, h);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static ulong BoxAddr(Obj o) => (LeanRt.lean_unbox(o) << 1) | 1;

    /// <summary>Tries to resolve `o` without compacting it (scalar, already compacted, or in a dep region).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    bool TryKnown(Obj o, out ulong off)
    {
        if (o.m_tag == LeanRt.LeanBoxTag) { off = BoxAddr(o); return true; }
        if (m_objTable.TryGetValue(o, out off)) return true;
        if (m_depRegions.Count != 0 && o.m_rc == 0) return TryDep(o, out off);
        return false;
    }

    bool TryDep(Obj o, out ulong off)
    {
        if (m_depsByAddr == null)
        {
            m_depsByAddr = m_depRegions.Where(r => r.IdsAreAddresses).OrderBy(r => r.BaseAddr).ToArray();
            // The other dependency regions (read while their address range was taken) need a map
            // from every object to its logical address.
            var rest = m_depRegions.Where(r => !r.IdsAreAddresses).ToList();
            int n = 0;
            foreach (var r in rest) n += r.ObjectCount;
            var d = new Dictionary<Obj, ulong>(n, ReferenceEqualityComparer.Instance);
            foreach (var r in rest)
                foreach (var (a, x) in r.Objects()) d.TryAdd(x, a);
            m_depAddr = d;
        }
        // An object of a region with address ids: the id says which region and where.
        ulong id = (ulong)o.m_id;
        if (id != 0)
        {
            var deps = m_depsByAddr;
            int lo = 0, hi = deps.Length;
            while (lo < hi)
            {
                int mid = (lo + hi) >> 1;
                if (deps[mid].BaseAddr <= id) lo = mid + 1; else hi = mid;
            }
            if (lo > 0 && deps[lo - 1].Contains(id))
            {
                off = id;
                m_objTable[o] = off;
                return true;
            }
        }
        if (m_depAddr.Count != 0 && m_depAddr.TryGetValue(o, out off))
        {
            m_objTable[o] = off;
            return true;
        }
        off = 0;
        return false;
    }

    ulong ToOffset(Obj root)
    {
        if (TryKnown(root, out var off)) return off;
        if (IsLeaf(root)) return CompactLeaf(root);
        int stackBase = m_frameCount;
        PushFrame(root);
        while (true)
        {
            ref Frame f = ref m_frames[m_frameCount - 1];
            if (f.Next < f.Count)
            {
                Obj c = GetChild(f.Obj, f.Next++);
                if (TryKnown(c, out off)) { PushTmp(off); continue; }
                if (IsLeaf(c)) { PushTmp(CompactLeaf(c)); continue; }
                PushFrame(c);
                continue;
            }
            Obj o = f.Obj;
            int bas = f.Base;
            f.Obj = null;
            m_frameCount--;
            off = Emit(o, bas);
            m_tmpCount = bas;
            if (m_frameCount == stackBase) return off;
            PushTmp(off);
        }
    }

    static bool IsLeaf(Obj o)
    {
        int t = o.m_tag;
        return t == LeanRt.LeanString || t == LeanRt.LeanScalarArray || t == LeanRt.LeanMPZ;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    void PushTmp(ulong v)
    {
        if (m_tmpCount == m_tmp.Length) Array.Resize(ref m_tmp, m_tmp.Length * 2);
        m_tmp[m_tmpCount++] = v;
    }

    void PushFrame(Obj o)
    {
        long count;
        int tag = o.m_tag;
        if (tag <= LeanRt.LeanMaxCtorTag) count = o.m_other;
        else switch (tag)
        {
            case LeanRt.LeanArray: count = Unsafe.As<ArrayObj>(o).m_size; break;
            case LeanRt.LeanThunk: ForceThunk(Unsafe.As<ThunkObj>(o)); count = 1; break;
            case LeanRt.LeanTask: WaitTask(Unsafe.As<TaskObj>(o)); count = 1; break;
            case LeanRt.LeanPromise: count = 1; break;
            case LeanRt.LeanRef: count = 1; break;
            case LeanRt.LeanClosure:
                if (!m_allowClosures)
                    throw new OleanFormatException("Closures cannot be compacted (unless explicitly calling " +
                        "`CompactedRegion.save (allowClosures := true)`). One possible cause of this error is " +
                        "trying to store a function in a persistent environment extension.");
                count = Unsafe.As<Closure>(o).m_num_fixed;
                break;
            case LeanRt.LeanExternal: throw new OleanFormatException("external objects cannot be compacted");
            default: throw new OleanFormatException($"unexpected object tag {tag}");
        }
        if (m_frameCount == m_frames.Length) Array.Resize(ref m_frames, m_frames.Length * 2);
        m_frames[m_frameCount++] = new Frame { Obj = o, Next = 0, Count = count, Base = m_tmpCount };
    }

    static Obj GetChild(Obj o, long i)
    {
        int tag = o.m_tag;
        if (tag <= LeanRt.LeanMaxCtorTag) return LeanRt.lean_ctor_get(o, (uint)i);
        switch (tag)
        {
            case LeanRt.LeanArray: return Unsafe.As<ArrayObj>(o).m_data[i];
            case LeanRt.LeanThunk: return Unsafe.As<ThunkObj>(o).m_value;
            case LeanRt.LeanTask: return Unsafe.As<TaskObj>(o).m_value;
            case LeanRt.LeanPromise: return Unsafe.As<PromiseObj>(o).m_result;
            case LeanRt.LeanRef: return Unsafe.As<RefObj>(o).m_value;
            case LeanRt.LeanClosure: return Unsafe.As<Closure>(o).m_objs[i];
            default: throw new InvalidOperationException();
        }
    }

    ulong Emit(Obj o, int bas)
    {
        int tag = o.m_tag;
        if (tag <= LeanRt.LeanMaxCtorTag)
        {
            // `insert_constructor`: copy of the heap object, whose size is rounded up to 8 bytes.
            int n = o.m_other;
            int ssz = o.m_cs_sz;
            long sz = 8 + 8L * n + ((ssz + 7) & ~7);
            long at = Alloc(sz);
            WriteHeader(at, sz, tag, n);
            for (int i = 0; i < n; i++) WriteU64(at + 8 + 8 * i, m_tmp[bas + i]);
            if (ssz > 0)
            {
                var c = Unsafe.As<Ctor>(o);
                long s = at + 8 + 8L * n;
                if (ssz >= 8) WriteU64(s, c.s0);
                else for (int i = 0; i < ssz; i++) m_buf[s + i] = (byte)(c.s0 >> (8 * i));
                if (ssz > 8) c.sx.AsSpan(0, ssz - 8).CopyTo(m_buf.AsSpan((int)(s + 8)));
            }
            return SaveMaxSharing(o, at, sz);
        }
        switch (tag)
        {
            case LeanRt.LeanArray:
            {
                long n = Unsafe.As<ArrayObj>(o).m_size;
                long sz = OleanLayout.ArrayHeader + 8 * n;
                long at = Alloc(sz);
                WriteHeader(at, 1, LeanRt.LeanArray, 0);
                WriteU64(at + 8, (ulong)n);
                WriteU64(at + 16, (ulong)n);
                for (long i = 0; i < n; i++) WriteU64(at + OleanLayout.ArrayHeader + 8 * i, m_tmp[bas + i]);
                return SaveMaxSharing(o, at, sz);
            }
            case LeanRt.LeanThunk:
            {
                long at = Alloc(OleanLayout.ThunkSize);
                WriteHeader(at, OleanLayout.ThunkSize, LeanRt.LeanThunk, o.m_other);
                WriteU64(at + 8, m_tmp[bas]);
                return SaveMaxSharing(o, at, OleanLayout.ThunkSize);
            }
            case LeanRt.LeanTask:
            {
                long at = Alloc(OleanLayout.TaskSize);
                WriteHeader(at, OleanLayout.TaskSize, LeanRt.LeanTask, o.m_other);
                WriteU64(at + 8, m_tmp[bas]);
                return SaveMaxSharing(o, at, OleanLayout.TaskSize);
            }
            case LeanRt.LeanPromise:
            {
                long at = Alloc(OleanLayout.PromiseSize);
                WriteHeader(at, OleanLayout.PromiseSize, LeanRt.LeanPromise, o.m_other);
                WriteU64(at + 8, m_tmp[bas]);
                return SaveMaxSharing(o, at, OleanLayout.PromiseSize);
            }
            case LeanRt.LeanRef:
            {
                long at = Alloc(OleanLayout.RefSize);
                WriteHeader(at, OleanLayout.RefSize, LeanRt.LeanRef, o.m_other);
                WriteU64(at + 8, m_tmp[bas]);
                // must NOT be max-shared
                return Save(o, at);
            }
            case LeanRt.LeanClosure:
            {
                var c = Unsafe.As<Closure>(o);
                int n = c.m_num_fixed;
                long sz = OleanLayout.ClosureHeader + 8L * n;
                long at = Alloc(sz);
                WriteHeader(at, sz, LeanRt.LeanClosure, o.m_other);
                // the index of the function in the file's function table (see `FunctionTable`)
                WriteU64(at + 8, (ulong)FunctionIndex((nint)c.m_fun));
                WriteU16(at + 16, c.m_arity);
                WriteU16(at + 18, c.m_num_fixed);
                for (int i = 0; i < n; i++) WriteU64(at + OleanLayout.ClosureHeader + 8 * i, m_tmp[bas + i]);
                m_closureOffsets.Add(at + 8);
                return Save(o, at);
            }
            default: throw new InvalidOperationException();
        }
    }

    ulong CompactLeaf(Obj o)
    {
        switch (o.m_tag)
        {
            case LeanRt.LeanScalarArray:
            {
                var a = Unsafe.As<SArrayObj>(o);
                long n = a.m_size;
                int esz = (int)LeanRt.lean_sarray_elem_size(o);
                long nbytes = n * esz;
                long sz = OleanLayout.SArrayHeader + nbytes;
                long at = Alloc(sz);
                WriteHeader(at, 1, LeanRt.LeanScalarArray, esz);
                WriteU64(at + 8, (ulong)n);
                WriteU64(at + 16, (ulong)n);
                a.m_data.AsSpan(0, (int)nbytes).CopyTo(m_buf.AsSpan((int)(at + OleanLayout.SArrayHeader)));
                return SaveMaxSharing(o, at, sz);
            }
            case LeanRt.LeanString:
            {
                var s = Unsafe.As<StrObj>(o);
                long n = s.m_size;
                long sz = OleanLayout.StringHeader + n;
                long at = Alloc(sz);
                WriteHeader(at, 1, LeanRt.LeanString, 0);
                WriteU64(at + 8, (ulong)n);
                WriteU64(at + 16, (ulong)n);
                WriteU64(at + 24, (ulong)s.m_length);
                s.m_data.AsSpan(0, (int)n).CopyTo(m_buf.AsSpan((int)(at + OleanLayout.StringHeader)));
                return SaveMaxSharing(o, at, sz);
            }
            case LeanRt.LeanMPZ:
            {
                BigInteger v = Unsafe.As<MpzObj>(o).m_value;
                BigInteger a = BigInteger.Abs(v);
                int nbytes = a.GetByteCount(isUnsigned: true);
                if (m_gmp)
                {
                    int nlimbs = (nbytes + 7) / 8;
                    long sz = OleanLayout.MpzGmpHeader + 8L * nlimbs;
                    long at = Alloc(sz);
                    WriteHeader(at, sz, LeanRt.LeanMPZ, 0);
                    WriteU32(at + 8, (uint)nlimbs);                                   // _mp_alloc
                    WriteU32(at + 12, (uint)(v.Sign < 0 ? -nlimbs : nlimbs));         // _mp_size
                    long data = at + OleanLayout.MpzGmpHeader;
                    WriteU64(at + 16, AddrOf(data));                                  // _mp_d
                    a.TryWriteBytes(m_buf.AsSpan((int)data, nlimbs * 8), out _, isUnsigned: true, isBigEndian: false);
                    return Save(o, at);
                }
                else
                {
                    int ndigits = (nbytes + 3) / 4;
                    long sz = OleanLayout.MpzLeanHeader + 4L * ndigits;
                    long at = Alloc(sz);
                    WriteHeader(at, sz, LeanRt.LeanMPZ, 0);
                    m_buf[at + 8] = (byte)(v.Sign < 0 ? 1 : 0);                        // m_sign
                    WriteU64(at + 16, (ulong)ndigits);                                // m_size
                    long data = at + OleanLayout.MpzLeanHeader;
                    WriteU64(at + 24, AddrOf(data));                                  // m_digits
                    a.TryWriteBytes(m_buf.AsSpan((int)data, ndigits * 4), out _, isUnsigned: true, isBigEndian: false);
                    return Save(o, at);
                }
            }
            default: throw new InvalidOperationException();
        }
    }

    // ------------------------------------------------------------------
    // Thunks and tasks must be evaluated before they can be compacted (`lean_thunk_get`,
    // `lean_task_get`). These live in the Tasks area; we call them if present.

    static MethodInfo s_thunkGet, s_taskGet;
    static bool s_lookedUp;

    static void LookUp()
    {
        if (s_lookedUp) return;
        var t = typeof(LeanRt);
        s_thunkGet = t.GetMethod("lean_thunk_get_own", BindingFlags.Public | BindingFlags.Static, new[] { typeof(Obj) });
        s_taskGet = t.GetMethod("lean_task_get_own", BindingFlags.Public | BindingFlags.Static, new[] { typeof(Obj) });
        s_lookedUp = true;
    }

    static void ForceThunk(ThunkObj t)
    {
        if (t.m_value != null) return;
        LookUp();
        if (s_thunkGet != null) { LeanRt.lean_dec((Obj)s_thunkGet.Invoke(null, new object[] { t })); if (t.m_value != null) return; }
        var c = t.m_closure;
        if (c == null) throw new OleanFormatException("thunk without value and closure");
        LeanRt.lean_inc(c);
        var v = LeanRt.lean_apply_1(c, LeanRt.lean_box(0));
        t.m_value = v;
        t.m_closure = null;
    }

    static void WaitTask(TaskObj t)
    {
        if (t.m_value != null) return;
        LookUp();
        if (s_taskGet != null) { LeanRt.lean_dec((Obj)s_taskGet.Invoke(null, new object[] { t })); if (t.m_value != null) return; }
        var sw = new SpinWait();
        while (t.m_value == null) sw.SpinOnce();
    }

    // ------------------------------------------------------------------
    // Structural sharing table (`max_sharing_table`): keys are (offset, size) of emitted objects,
    // compared by their bytes in the buffer.

    sealed class MaxSharingTable
    {
        readonly ObjectCompactor m_c;
        long[] m_offs;   // -1 = empty
        int[] m_sizes;
        int[] m_hashes;
        int m_count;
        int m_mask;

        public MaxSharingTable(ObjectCompactor c)
        {
            m_c = c;
            Init(1 << 16);
        }

        void Init(int cap)
        {
            m_offs = new long[cap];
            Array.Fill(m_offs, -1L);
            m_sizes = new int[cap];
            m_hashes = new int[cap];
            m_mask = cap - 1;
            m_count = 0;
        }

        static int Hash(ReadOnlySpan<byte> s)
        {
            // FNV-style 64-bit mixing over 8-byte words (the hash only affects performance).
            ulong h = 0xcbf29ce484222325UL ^ (ulong)s.Length;
            int i = 0;
            for (; i + 8 <= s.Length; i += 8)
            {
                ulong k = Unsafe.ReadUnaligned<ulong>(ref MemoryMarshal.GetReference(s.Slice(i)));
                h = (h ^ k) * 0x100000001b3UL;
                h ^= h >> 29;
            }
            for (; i < s.Length; i++) h = (h ^ s[i]) * 0x100000001b3UL;
            h ^= h >> 32;
            return (int)h;
        }

        /// <summary>Returns the offset of an existing equal object, or adds (off, size) and returns -1.</summary>
        public long FindOrAdd(long off, long size)
        {
            var buf = m_c.m_buf;
            var span = new ReadOnlySpan<byte>(buf, (int)off, (int)size);
            int h = Hash(span);
            int i = h & m_mask;
            while (true)
            {
                long o = m_offs[i];
                if (o < 0) break;
                if (m_hashes[i] == h && m_sizes[i] == size &&
                    span.SequenceEqual(new ReadOnlySpan<byte>(buf, (int)o, (int)size)))
                    return o;
                i = (i + 1) & m_mask;
            }
            m_offs[i] = off;
            m_sizes[i] = (int)size;
            m_hashes[i] = h;
            if (++m_count * 2 > m_offs.Length) Grow();
            return -1;
        }

        void Grow()
        {
            var offs = m_offs; var sizes = m_sizes; var hashes = m_hashes;
            Init(offs.Length * 2);
            for (int j = 0; j < offs.Length; j++)
            {
                if (offs[j] < 0) continue;
                int i = hashes[j] & m_mask;
                while (m_offs[i] >= 0) i = (i + 1) & m_mask;
                m_offs[i] = offs[j]; m_sizes[i] = sizes[j]; m_hashes[i] = hashes[j];
                m_count++;
            }
        }
    }
}
