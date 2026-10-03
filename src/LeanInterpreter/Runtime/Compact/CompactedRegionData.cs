// Managed state of a loaded compacted region. Native Lean keeps the file mapped and uses the objects
// in place; LeanInterpreter converts every object into a managed object instead. To resolve pointers from
// later regions into this one (`depRegions` of `CompactedRegion.read`, e.g. `.olean.server` ->
// `.olean`) and from saves back into this one (`depRegions` of `CompactedRegion.save`), a region needs
// a map between file offsets and objects:
//  * right after reading, the reader's word-indexed map (file offset / 8 -> object) is kept for a
//    few regions per thread (`m_dense`), which covers the usual `.olean` -> `.server` -> `.private`
//    and `.ir.sig` -> `.ir` chains;
//  * otherwise, an index (objects in file order + sparse offset checkpoints) is built on demand. The
//    file order is recovered without re-reading the file: the compactor emits objects in post-order
//    of a depth-first traversal from the root (children in field order, each object once, objects of
//    dependency regions skipped), so the same traversal of the managed graph yields the file order.

using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime.Compact;

public sealed class CompactedRegionData
{
    /// <summary>log2 of the distance between two offset checkpoints.</summary>
    internal const int CpShift = 4;

    public string FilePath { get; internal set; }
    /// <summary>Logical address of the start of the file (`olean_header.base_addr`).</summary>
    public ulong BaseAddr { get; internal set; }
    /// <summary>File size in bytes (the size of the native mapping).</summary>
    public ulong Size { get; internal set; }
    public OleanHeader Header { get; internal set; }
    /// <summary>The root object (may live in a dependency region).</summary>
    public Obj Root { get; internal set; }
    /// <summary>Raw root pointer as stored in the file (logical address or tagged scalar).</summary>
    public ulong RootAddr { get; internal set; }

    /// <summary>Whether the identity (`m_id`) of every object of this region is its logical address (see `RegionAddressSpace`).</summary>
    internal bool IdsAreAddresses;

    internal bool m_gmp;
    internal int m_count;           // number of objects in the file
    internal ulong m_firstObjOffset;
    internal ulong m_dataEnd;       // file offset of the end of the object data
    internal CompactedRegionData[] m_deps;  // regions this one was read against
    // On-demand index (see above).
    internal Obj[] m_objs;          // objects in file order
    uint[] m_checkpoints;           // file offset / 8 of m_objs[i << CpShift]
    readonly object m_indexLock = new();
    // Word-indexed object map while this region is in the recent-reads cache of thread m_denseThread.
    internal volatile Obj[] m_dense;
    internal int m_denseThread;

    /// <summary>Set for a lazily decoded region (see LazyRegion.cs).</summary>
    internal LazyRegion m_lazy;

    public int ObjectCount => m_count >= 0 ? m_count : (m_count = m_lazy.CountObjects());
    public ulong End => BaseAddr + Size;

    /// <summary>Whether logical address `addr` lies inside this region (file).</summary>
    public bool Contains(ulong addr) => addr - BaseAddr < Size;

    /// <summary>The objects of this region with their logical addresses, in file order.</summary>
    public IEnumerable<(ulong Addr, Obj Obj)> Objects()
    {
        var objs = EnsureIndex();
        ulong off = m_firstObjOffset;
        for (int i = 0; i < objs.Length; i++)
        {
            var o = objs[i];
            yield return (BaseAddr + off, o);
            off += (ulong)OleanLayout.CompactedSize(o, m_gmp);
        }
    }

    internal void SetIndex(Obj[] objs)
    {
        var cps = new uint[Math.Max(1, (objs.Length + (1 << CpShift) - 1) >> CpShift)];
        ulong off = m_firstObjOffset;
        for (int i = 0; i < objs.Length; i++)
        {
            if ((i & ((1 << CpShift) - 1)) == 0) cps[i >> CpShift] = (uint)(off >> 3);
            off += (ulong)OleanLayout.CompactedSize(objs[i], m_gmp);
        }
        if (objs.Length != m_count || off != m_dataEnd)
            throw new OleanFormatException($"internal error: cannot reconstruct the object order of region '{FilePath}' " +
                                           $"({objs.Length} of {m_count} objects, end {off} instead of {m_dataEnd})");
        m_checkpoints = cps;
        m_objs = objs;
    }

    /// <summary>Objects of this region in file order (computed on first use).</summary>
    internal Obj[] EnsureIndex()
    {
        var objs = m_objs;
        if (objs != null) return objs;
        lock (m_indexLock)
        {
            if (m_objs != null) return m_objs;
            if (Root == null) throw new OleanFormatException($"compacted region '{FilePath}' has been freed");
            if (m_lazy != null)
            {
                var all = m_lazy.MaterializeAll();
                m_count = all.Length;
                SetIndex(all);
                return m_objs;
            }
            SetIndex(TraverseFileOrder());
            return m_objs;
        }
    }

    /// <summary>Post-order DFS from the root, skipping scalars and objects of dependency regions.</summary>
    internal Obj[] TraverseFileOrder()
    {
        int count = ObjectCount;
        var result = new Obj[count];
        int n = 0;
        if (count == 0) return result;
        // Objects of dependency regions are recognised by their address (id) if the region has
        // address ids, otherwise by a set of all its objects.
        HashSet<Obj> depObjs = null;
        var addrDeps = new List<CompactedRegionData>();
        if (m_deps != null && m_deps.Length > 0)
        {
            int total = 0;
            foreach (var d in m_deps)
                if (d.IdsAreAddresses) addrDeps.Add(d); else total += d.ObjectCount;
            if (total > 0)
            {
                depObjs = new HashSet<Obj>(total, ReferenceEqualityComparer.Instance);
                foreach (var d in m_deps)
                    if (!d.IdsAreAddresses) foreach (var o in d.EnsureIndex()) depObjs.Add(o);
            }
        }
        bool InAddrDep(Obj o)
        {
            ulong id = (ulong)o.m_id;
            if (id == 0) return false;
            foreach (var d in addrDeps) if (d.Contains(id)) return true;
            return false;
        }
        var visited = new HashSet<Obj>(count, ReferenceEqualityComparer.Instance);
        var stack = new Stack<(Obj, long)>();
        bool Enter(Obj o) =>
            o != null && o.m_tag != LeanRt.LeanBoxTag && (depObjs == null || !depObjs.Contains(o)) &&
            (addrDeps.Count == 0 || !InAddrDep(o)) && visited.Add(o);
        if (Enter(Root)) stack.Push((Root, 0));
        while (stack.Count > 0)
        {
            var (o, i) = stack.Pop();
            long cnt = ChildCount(o);
            if (i < cnt)
            {
                stack.Push((o, i + 1));
                var c = Child(o, i);
                if (Enter(c)) stack.Push((c, 0));
                continue;
            }
            if (n == result.Length) throw new OleanFormatException($"internal error: region '{FilePath}' has more reachable objects than stored");
            result[n++] = o;
        }
        if (n != result.Length) Array.Resize(ref result, n);
        return result;
    }

    static long ChildCount(Obj o)
    {
        int tag = o.m_tag;
        if (tag <= LeanRt.LeanMaxCtorTag) return o.m_other;
        switch (tag)
        {
            case LeanRt.LeanArray: return Unsafe.As<ArrayObj>(o).m_size;
            case LeanRt.LeanThunk: case LeanRt.LeanTask: case LeanRt.LeanPromise: case LeanRt.LeanRef: return 1;
            case LeanRt.LeanClosure: return Unsafe.As<Closure>(o).m_num_fixed;
            default: return 0;
        }
    }

    static Obj Child(Obj o, long i)
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
            default: return null;
        }
    }

    /// <summary>Object stored at logical address `addr` (which must be inside this region).</summary>
    internal Obj Lookup(ulong addr)
    {
        ulong off = addr - BaseAddr;
        if (m_lazy != null && off < Size) return m_lazy.Materialize((long)off);
        if (off >= Size || (off & 7) != 0 || m_count == 0)
            throw new OleanFormatException($"invalid pointer 0x{addr:x} into region '{FilePath}'");
        uint word = (uint)(off >> 3);
        var objs = EnsureIndex();
        var cps = m_checkpoints;
        // Largest checkpoint <= word.
        int lo = 0, hi = cps.Length - 1;
        if (word < cps[0]) throw new OleanFormatException($"invalid pointer 0x{addr:x} into region '{FilePath}'");
        while (lo < hi)
        {
            int mid = (lo + hi + 1) >> 1;
            if (cps[mid] <= word) lo = mid; else hi = mid - 1;
        }
        int i = lo << CpShift;
        ulong w = cps[lo];
        int end = Math.Min(m_count, i + (1 << CpShift));
        while (i < end)
        {
            if (w == word) return objs[i];
            w += (ulong)(OleanLayout.CompactedSize(objs[i], m_gmp) >> 3);
            if (w > word) break;
            i++;
        }
        throw new OleanFormatException($"pointer 0x{addr:x} into region '{FilePath}' does not point to an object");
    }

    internal void Release()
    {
        m_dense = null;
        m_lazy?.DropObjects();
        m_objs = null;
        m_checkpoints = null;
        m_deps = null;
        Root = null;
    }

    // ------------------------------------------------------------------
    // Registry: Lean `CompactedRegion` values -> managed region data.
    // Keyed by the root object (the `root` field of `CompactedRegion`), which is also what survives
    // when a `CompactedRegion` value is itself saved into and re-read from a snapshot.

    static readonly ConditionalWeakTable<Obj, List<CompactedRegionData>> s_byRoot = new();
    static readonly object s_lock = new();

    internal static void Register(CompactedRegionData r)
    {
        lock (s_lock)
        {
            var l = s_byRoot.GetOrCreateValue(r.Root);
            l.Add(r);
        }
    }

    internal static void Unregister(CompactedRegionData r, Obj root)
    {
        lock (s_lock)
        {
            if (root != null && s_byRoot.TryGetValue(root, out var l)) l.Remove(r);
        }
    }

    internal static CompactedRegionData Find(Obj root, ulong baseAddr, ulong size)
    {
        lock (s_lock)
        {
            if (root != null && s_byRoot.TryGetValue(root, out var l))
                for (int i = l.Count - 1; i >= 0; i--)
                    if (l[i].BaseAddr == baseAddr && l[i].Size == size) return l[i];
        }
        return null;
    }
}
