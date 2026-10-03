// Port of runtime/sharecommon.{h,cpp}.
//
// `lean_sharecommon_eq` / `lean_sharecommon_hash` are *shallow* in C: they compare/hash the raw
// object body, i.e. the header fields relevant for the layout, the scalar data and the child
// *pointers*. We mirror this: children are compared by identity (`PtrEq`, tagged scalars by value)
// and hashed through `lean_ptr_addr`. Hash values therefore differ from C (which hashes raw
// addresses) but are consistent with the equality.

using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

internal static class ShareCommonUtil
{
    static bool FieldEq(Obj a, Obj b)
    {
        if (a == null || b == null) return a == null && b == null;
        return StrRtUtil.PtrEq(a, b);
    }

    static ulong FieldHash(Obj a) => a == null ? 0UL : LeanRt.lean_ptr_addr(a);

    internal static bool Eq(Obj o1, Obj o2)
    {
        if (ReferenceEquals(o1, o2)) return true;
        byte tag = o1.m_tag;
        if (tag != o2.m_tag) return false;
        if (o1.m_other != o2.m_other) return false;
        if (tag == LeanRt.LeanBoxTag)
            return Unsafe.As<Box>(o1).m_value == Unsafe.As<Box>(o2).m_value;
        if (tag <= LeanRt.LeanMaxCtorTag)
        {
            var c1 = Unsafe.As<Ctor>(o1);
            var c2 = Unsafe.As<Ctor>(o2);
            if (c1.m_cs_sz != c2.m_cs_sz) return false;
            int n = o1.m_other;
            for (int i = 0; i < n; i++)
                if (!FieldEq(LeanRt.lean_ctor_get_core(o1, i), LeanRt.lean_ctor_get_core(o2, i))) return false;
            if (c1.s0 != c2.s0) return false;
            if (c1.sx == null || c2.sx == null) return c1.sx == null && c2.sx == null;
            return c1.sx.AsSpan().SequenceEqual(c2.sx);
        }
        switch (tag)
        {
            case LeanRt.LeanArray:
            {
                var a1 = Unsafe.As<ArrayObj>(o1);
                var a2 = Unsafe.As<ArrayObj>(o2);
                if (a1.m_size != a2.m_size || a1.m_data.Length != a2.m_data.Length) return false;
                for (long i = 0; i < a1.m_size; i++)
                    if (!FieldEq(a1.m_data[i], a2.m_data[i])) return false;
                return true;
            }
            case LeanRt.LeanScalarArray:
            {
                var a1 = Unsafe.As<SArrayObj>(o1);
                var a2 = Unsafe.As<SArrayObj>(o2);
                if (a1.m_size != a2.m_size || a1.m_capacity != a2.m_capacity) return false;
                int len = (int)(LeanRt.lean_sarray_elem_size(o1) * (ulong)a1.m_size);
                return new ReadOnlySpan<byte>(a1.m_data, 0, len).SequenceEqual(new ReadOnlySpan<byte>(a2.m_data, 0, len));
            }
            case LeanRt.LeanString:
            {
                var s1 = Unsafe.As<StrObj>(o1);
                var s2 = Unsafe.As<StrObj>(o2);
                if (s1.m_size != s2.m_size || s1.m_data.Length != s2.m_data.Length || s1.m_length != s2.m_length) return false;
                int n = (int)s1.m_size;
                return new ReadOnlySpan<byte>(s1.m_data, 0, n).SequenceEqual(new ReadOnlySpan<byte>(s2.m_data, 0, n));
            }
            case LeanRt.LeanMPZ:
                return Unsafe.As<MpzObj>(o1).m_value == Unsafe.As<MpzObj>(o2).m_value;
            case LeanRt.LeanClosure:
            {
                var c1 = Unsafe.As<Closure>(o1);
                var c2 = Unsafe.As<Closure>(o2);
                unsafe
                {
                    if (c1.m_fun != c2.m_fun) return false;
                }
                if (c1.m_arity != c2.m_arity || c1.m_num_fixed != c2.m_num_fixed) return false;
                for (int i = 0; i < c1.m_num_fixed; i++)
                    if (!FieldEq(c1.m_objs[i], c2.m_objs[i])) return false;
                return true;
            }
            case LeanRt.LeanThunk:
            {
                var t1 = Unsafe.As<ThunkObj>(o1);
                var t2 = Unsafe.As<ThunkObj>(o2);
                return FieldEq(t1.m_value, t2.m_value) && FieldEq(t1.m_closure, t2.m_closure);
            }
            case LeanRt.LeanRef:
                return FieldEq(Unsafe.As<RefObj>(o1).m_value, Unsafe.As<RefObj>(o2).m_value);
            case LeanRt.LeanExternal:
            {
                var e1 = Unsafe.As<ExternalObj>(o1);
                var e2 = Unsafe.As<ExternalObj>(o2);
                return ReferenceEquals(e1.m_class, e2.m_class) && ReferenceEquals(e1.m_data, e2.m_data);
            }
            default:
                // Tasks and promises: the body holds implementation pointers; identity is the only sane choice.
                return false;
        }
    }

    internal static ulong Hash(Obj o)
    {
        byte tag = o.m_tag;
        if (tag == LeanRt.LeanBoxTag) return LeanHash.Mix(Unsafe.As<Box>(o).m_value, 11);
        if (tag == LeanRt.LeanMPZ)
        {
            var bytes = Unsafe.As<MpzObj>(o).m_value.ToByteArray();
            return LeanHash.Mix(tag, LeanHash.HashStr(bytes, 11));
        }
        // hash relevant parts of the header (C truncates the initial value to `unsigned`)
        ulong h = (uint)LeanHash.Mix(tag, o.m_other);
        if (tag <= LeanRt.LeanMaxCtorTag)
        {
            var c = Unsafe.As<Ctor>(o);
            h = LeanHash.Mix(h, c.m_cs_sz);
            int n = o.m_other;
            for (int i = 0; i < n; i++) h = LeanHash.Mix(h, FieldHash(LeanRt.lean_ctor_get_core(o, i)));
            if (c.m_cs_sz != 0)
            {
                h = LeanHash.Mix(h, c.s0);
                if (c.sx != null) h = LeanHash.HashStr(c.sx, h);
            }
            return h;
        }
        switch (tag)
        {
            case LeanRt.LeanArray:
            {
                var a = Unsafe.As<ArrayObj>(o);
                h = LeanHash.Mix(LeanHash.Mix(h, (ulong)a.m_size), (ulong)a.m_data.Length);
                for (long i = 0; i < a.m_size; i++) h = LeanHash.Mix(h, FieldHash(a.m_data[i]));
                return h;
            }
            case LeanRt.LeanScalarArray:
            {
                var a = Unsafe.As<SArrayObj>(o);
                h = LeanHash.Mix(LeanHash.Mix(h, (ulong)a.m_size), (ulong)a.m_capacity);
                int len = (int)(LeanRt.lean_sarray_elem_size(o) * (ulong)a.m_size);
                return LeanHash.HashStr(new ReadOnlySpan<byte>(a.m_data, 0, len), h);
            }
            case LeanRt.LeanString:
            {
                var s = Unsafe.As<StrObj>(o);
                h = LeanHash.Mix(LeanHash.Mix(LeanHash.Mix(h, (ulong)s.m_size), (ulong)s.m_data.Length), (ulong)s.m_length);
                return LeanHash.HashStr(new ReadOnlySpan<byte>(s.m_data, 0, (int)s.m_size), h);
            }
            case LeanRt.LeanClosure:
            {
                var c = Unsafe.As<Closure>(o);
                unsafe { h = LeanHash.Mix(h, (ulong)c.m_fun); }
                h = LeanHash.Mix(h, ((ulong)c.m_arity << 16) | c.m_num_fixed);
                for (int i = 0; i < c.m_num_fixed; i++) h = LeanHash.Mix(h, FieldHash(c.m_objs[i]));
                return h;
            }
            case LeanRt.LeanThunk:
            {
                var t = Unsafe.As<ThunkObj>(o);
                return LeanHash.Mix(LeanHash.Mix(h, FieldHash(t.m_value)), FieldHash(t.m_closure));
            }
            case LeanRt.LeanRef:
                return LeanHash.Mix(h, FieldHash(Unsafe.As<RefObj>(o).m_value));
            case LeanRt.LeanExternal:
            {
                var e = Unsafe.As<ExternalObj>(o);
                return LeanHash.Mix(h, e.m_data == null ? 0UL : (ulong)(uint)RuntimeHelpers.GetHashCode(e.m_data));
            }
            default:
                return LeanHash.Mix(h, LeanRt.lean_ptr_addr(o));
        }
    }
}

/// <summary>`set_hash` / `set_eq` of `sharecommon_quick_fn`.</summary>
internal sealed class ShareCommonComparer : IEqualityComparer<Obj>
{
    public static readonly ShareCommonComparer Instance = new();
    public bool Equals(Obj a, Obj b) => ShareCommonUtil.Eq(a, b);
    public int GetHashCode(Obj o)
    {
        ulong h = ShareCommonUtil.Hash(o);
        return (int)(h ^ (h >> 32));
    }
}

/// <summary>
/// Port of `sharecommon_quick_fn`: a fast version of `sharecommon_fn` which only uses a local state.
/// </summary>
public class SharecommonQuickFn
{
    /*
    We use `m_cache` to ensure we do **not** traverse a DAG as a tree.
    We use pointer equality for this collection.
    */
    protected readonly Dictionary<Obj, Obj> m_cache = new(ReferenceEqualityComparer.Instance);
    /* Set of maximally shared terms. AKA hash-consing table. */
    protected readonly HashSet<Obj> m_set = new(ShareCommonComparer.Instance);
    /* If `true`, `check_cache` will also check `m_set`. */
    protected bool m_check_set;

    public SharecommonQuickFn(bool s = false) { m_check_set = s; }
    public void SetCheckSet(bool f) { m_check_set = f; }

    /// <summary>Takes a reference to an object in the range of `m_cache` or in `m_set` (`inc_st`).</summary>
    static void IncSt(Obj o)
    {
        if (o.m_rc == int.MaxValue) throw LeanRt.lean_internal_panic_rc_overflow();
        LeanRt.lean_inc_ref(o);
    }

    protected Obj CheckCache(Obj a)
    {
        if (!LeanRt.lean_is_exclusive(a))
        {
            // We only check the cache if `a` is a shared object
            if (m_cache.TryGetValue(a, out var r))
            {
                IncSt(r);
                return r;
            }
            if (m_check_set && m_set.TryGetValue(a, out var result))
            {
                IncSt(result);
                return result;
            }
        }
        return null;
    }

    /* `new_a` is a new object that is equal to `a`, but its subobjects are maximally shared. */
    Obj Save(Obj a, Obj new_a)
    {
        Obj result;
        if (!m_set.TryGetValue(new_a, out result))
        {
            // `new_a` is a new object
            m_set.Add(new_a);
            result = new_a;
        }
        else
        {
            // We already have a maximally shared object that is equal to `new_a`
            LeanRt.lean_dec_ref(new_a); // delete `new_a`
            IncSt(result);
        }
        if (!LeanRt.lean_is_exclusive(a))
        {
            // We only cache the result if `a` is a shared object.
            m_cache.TryAdd(a, result);
        }
        return result;
    }

    // `sarray`, `string` and `mpz`
    Obj VisitTerminal(Obj a)
    {
        if (m_set.TryGetValue(a, out var existing))
            a = existing;
        else
            m_set.Add(a);
        LeanRt.lean_inc_ref(a);
        return a;
    }

    Obj VisitArray(Obj a)
    {
        Obj r = CheckCache(a);
        if (r != null) return r;
        var ao = Unsafe.As<ArrayObj>(a);
        ulong sz = (ulong)ao.m_size;
        Obj new_a = LeanRt.lean_alloc_array(sz, sz);
        Obj[] dest = Unsafe.As<ArrayObj>(new_a).m_data;
        for (ulong i = 0; i < sz; i++) dest[i] = Visit(ao.m_data[i]);
        return Save(a, new_a);
    }

    Obj VisitCtor(Obj a)
    {
        Obj r = CheckCache(a);
        if (r != null) return r;
        uint num_objs = LeanRt.lean_ctor_num_objs(a);
        var ca = Unsafe.As<Ctor>(a);
        uint scalar_sz = ca.m_cs_sz;
        Obj new_a = LeanRt.lean_alloc_ctor(a.m_tag, num_objs, scalar_sz);
        for (uint i = 0; i < num_objs; i++)
            LeanRt.lean_ctor_set(new_a, i, Visit(LeanRt.lean_ctor_get(a, i)));
        if (scalar_sz > 0)
        {
            var cn = Unsafe.As<Ctor>(new_a);
            cn.s0 = ca.s0;
            if (ca.sx != null) Array.Copy(ca.sx, cn.sx, ca.sx.Length);
        }
        return Save(a, new_a);
    }

    protected Obj Visit(Obj a)
    {
        if (LeanRt.lean_is_scalar(a)) return a;
        switch (a.m_tag)
        {
            /* Similarly to `sharecommon_fn`, we only maximally share arrays, scalar arrays, strings, and
               constructor objects. */
            case LeanRt.LeanClosure:
            case LeanRt.LeanThunk:
            case LeanRt.LeanTask:
            case LeanRt.LeanPromise:
            case LeanRt.LeanRef:
            case LeanRt.LeanExternal:
                LeanRt.lean_inc_ref(a);
                return a;
            case LeanRt.LeanMPZ:
            case LeanRt.LeanScalarArray:
            case LeanRt.LeanString:
                return VisitTerminal(a);
            case LeanRt.LeanArray:
                return VisitArray(a);
            default:
                return VisitCtor(a);
        }
    }

    /// <summary>`operator()`: `a` is borrowed; the result is owned.</summary>
    public Obj Invoke(Obj a) => Visit(a);
}

/// <summary>
/// Port of `sharecommon_persistent_fn`: like `SharecommonQuickFn`, but the entry points and
/// results are kept alive (call `Dispose` to release them, as the C++ destructor does).
/// </summary>
public sealed class SharecommonPersistentFn : SharecommonQuickFn, IDisposable
{
    readonly List<Obj> m_saved = new();

    public SharecommonPersistentFn(bool s = false) : base(s) { }

    public new Obj Invoke(Obj e)
    {
        Obj r = CheckCache(e);
        if (r != null) return r;
        LeanRt.lean_inc(e);
        m_saved.Add(e);
        r = Visit(e);
        LeanRt.lean_inc(r);
        m_saved.Add(r);
        return r;
    }

    public void Dispose()
    {
        foreach (var o in m_saved) LeanRt.lean_dec(o);
        m_saved.Clear();
    }
}

/// <summary>Port of `sharecommon_state` + `sharecommon_fn` (the `ShareCommon.State` based version).</summary>
internal sealed class SharecommonStateFn
{
    // sharecommon_state
    readonly Obj m_map_find;
    readonly Obj m_map_insert;
    readonly Obj m_set_find;
    readonly Obj m_set_insert;
    Obj m_map;
    Obj m_set;

    readonly List<Obj> m_children = new();
    readonly List<Obj> m_todo = new();

    public SharecommonStateFn(Obj tc, Obj s)
    {
        m_map_find = LeanRt.lean_ctor_get(tc, 1);
        m_map_insert = LeanRt.lean_ctor_get(tc, 2);
        m_set_find = LeanRt.lean_ctor_get(tc, 3);
        m_set_insert = LeanRt.lean_ctor_get(tc, 4);
        m_map = LeanRt.lean_ctor_get(s, 0); LeanRt.lean_inc(m_map);
        m_set = LeanRt.lean_ctor_get(s, 1); LeanRt.lean_inc(m_set);
        LeanRt.lean_dec(s);
    }

    /// <summary>`~sharecommon_state`.</summary>
    void Destroy()
    {
        LeanRt.lean_dec(m_map);
        LeanRt.lean_dec(m_set);
    }

    Obj Pack(Obj a)
    {
        Obj r = LeanRt.lean_mk_pair(a, LeanRt.lean_mk_pair(m_map, m_set));
        m_map = LeanRt.lean_box(0);
        m_set = LeanRt.lean_box(0);
        return r;
    }

    Obj MapFind(Obj k)
    {
        LeanRt.lean_inc(m_map_find); LeanRt.lean_inc(m_map); LeanRt.lean_inc(k);
        return LeanRt.lean_apply_2(m_map_find, m_map, k);
    }

    void MapInsert(Obj k, Obj v)
    {
        LeanRt.lean_inc(m_map_insert);
        m_map = LeanRt.lean_apply_3(m_map_insert, m_map, k, v);
    }

    Obj SetFind(Obj o)
    {
        LeanRt.lean_inc(m_set_find); LeanRt.lean_inc(m_set); LeanRt.lean_inc(o);
        return LeanRt.lean_apply_2(m_set_find, m_set, o);
    }

    void SetInsert(Obj o)
    {
        LeanRt.lean_inc(m_set_insert);
        m_set = LeanRt.lean_apply_2(m_set_insert, m_set, o);
    }

    // sharecommon_fn

    bool PushChild(Obj a)
    {
        if (LeanRt.lean_is_scalar(a))
        {
            m_children.Add(a);
            return true;
        }
        switch (a.m_tag)
        {
            // We do not maximize sharing for the following kinds of objects
            case LeanRt.LeanThunk:
            case LeanRt.LeanTask:
            case LeanRt.LeanRef:
            case LeanRt.LeanExternal:
            case LeanRt.LeanClosure:
            case LeanRt.LeanPromise:
                m_children.Add(a);
                return true;
        }
        // Check whether we have already maximized sharing for `a`
        Obj o = MapFind(a);
        if (!LeanRt.lean_is_scalar(o))
        {
            Obj r = LeanRt.lean_ctor_get(o, 0);
            LeanRt.lean_dec(o);
            // The map still has a reference to `r`
            m_children.Add(r);
            return true;
        }
        m_todo.Add(a);
        return false;
    }

    void Save(Obj a, Obj new_a)
    {
        m_todo.RemoveAt(m_todo.Count - 1);
        Obj opt_new_r = SetFind(new_a);
        if (!LeanRt.lean_is_scalar(opt_new_r))
        {
            LeanRt.lean_dec(new_a); // we already have a maximally shared term equivalent to `new_a`
            new_a = LeanRt.lean_ctor_get(opt_new_r, 0);
            LeanRt.lean_inc(new_a);
            LeanRt.lean_dec(opt_new_r);
            LeanRt.lean_inc(a);
            MapInsert(a, new_a);
        }
        else
        {
            LeanRt.lean_inc(a);
            LeanRt.lean_inc_n(new_a, 3);
            SetInsert(new_a);        // `new_a` is a new maximally shared term
            MapInsert(a, new_a);     // `new_a` is the maximally shared representation for `a`
            MapInsert(new_a, new_a); // `new_a` is the maximally shared representation for itself
        }
    }

    void VisitArray(Obj a)
    {
        m_children.Clear();
        bool missing_children = false;
        var ao = Unsafe.As<ArrayObj>(a);
        long sz = ao.m_size;
        for (long i = 0; i < sz; i++)
            if (!PushChild(ao.m_data[i])) missing_children = true;
        if (missing_children) return;
        Obj new_a = LeanRt.lean_alloc_array((ulong)sz, (ulong)sz);
        Obj[] d = Unsafe.As<ArrayObj>(new_a).m_data;
        for (int i = 0; i < sz; i++)
        {
            LeanRt.lean_inc(m_children[i]);
            d[i] = m_children[i];
        }
        Save(a, new_a);
    }

    void VisitSArray(Obj a)
    {
        var ao = Unsafe.As<SArrayObj>(a);
        ulong sz = (ulong)ao.m_size;
        uint elem_sz = LeanRt.lean_sarray_elem_size(a);
        Obj new_a = LeanRt.lean_alloc_sarray(elem_sz, sz, sz);
        Array.Copy(ao.m_data, Unsafe.As<SArrayObj>(new_a).m_data, (long)(elem_sz * sz));
        Save(a, new_a);
    }

    void VisitString(Obj a)
    {
        var so = Unsafe.As<StrObj>(a);
        ulong sz = (ulong)so.m_size;
        Obj new_a = LeanRt.lean_alloc_string(sz, sz, (ulong)so.m_length);
        Array.Copy(so.m_data, Unsafe.As<StrObj>(new_a).m_data, (long)sz);
        Save(a, new_a);
    }

    void VisitMpz(Obj a)
    {
        Save(a, LeanRt.lean_alloc_mpz(Unsafe.As<MpzObj>(a).m_value));
    }

    void VisitCtor(Obj a)
    {
        m_children.Clear();
        uint num_objs = LeanRt.lean_ctor_num_objs(a);
        bool missing_child = false;
        for (uint i = 0; i < num_objs; i++)
            if (!PushChild(LeanRt.lean_ctor_get(a, i))) missing_child = true;
        if (missing_child) return;
        var ca = Unsafe.As<Ctor>(a);
        uint scalar_sz = ca.m_cs_sz;
        Obj new_a = LeanRt.lean_alloc_ctor(a.m_tag, num_objs, scalar_sz);
        for (int i = 0; i < num_objs; i++)
        {
            LeanRt.lean_inc(m_children[i]);
            LeanRt.lean_ctor_set(new_a, (uint)i, m_children[i]);
        }
        if (scalar_sz > 0)
        {
            var cn = Unsafe.As<Ctor>(new_a);
            cn.s0 = ca.s0;
            if (ca.sx != null) Array.Copy(ca.sx, cn.sx, ca.sx.Length);
        }
        Save(a, new_a);
    }

    public Obj Run(Obj a)
    {
        try
        {
            if (PushChild(a))
            {
                Obj r0 = m_children[m_children.Count - 1];
                LeanRt.lean_inc(r0);
                LeanRt.lean_dec(a);
                return Pack(r0);
            }
            while (m_todo.Count > 0)
            {
                Obj curr = m_todo[m_todo.Count - 1];
                switch (curr.m_tag)
                {
                    case LeanRt.LeanArray: VisitArray(curr); break;
                    case LeanRt.LeanScalarArray: VisitSArray(curr); break;
                    case LeanRt.LeanString: VisitString(curr); break;
                    case LeanRt.LeanMPZ: VisitMpz(curr); break;
                    case LeanRt.LeanClosure:
                    case LeanRt.LeanThunk:
                    case LeanRt.LeanTask:
                    case LeanRt.LeanPromise:
                    case LeanRt.LeanRef:
                    case LeanRt.LeanExternal:
                    case LeanRt.LeanReserved:
                        throw LeanRt.lean_internal_panic_unreachable();
                    default: VisitCtor(curr); break;
                }
            }
            Obj o = MapFind(a);
            Obj r = LeanRt.lean_ctor_get(o, 0);
            LeanRt.lean_inc(r);
            LeanRt.lean_dec(o);
            LeanRt.lean_dec(a);
            return Pack(r);
        }
        finally
        {
            Destroy();
        }
    }
}

public static unsafe partial class LeanRt
{
    public static byte lean_sharecommon_eq(Obj o1, Obj o2) => ShareCommonUtil.Eq(o1, o2) ? (byte)1 : (byte)0;

    public static ulong lean_sharecommon_hash(Obj o) => ShareCommonUtil.Hash(o);

    /// <summary>`def State.shareCommon {α} {σ : @&amp; StateFactory} (s : State σ) (a : α) : α × State σ`</summary>
    public static Obj lean_state_sharecommon(Obj tc, Obj s, Obj a) => new SharecommonStateFn(tc, s).Run(a);

    /// <summary>`def ShareCommon.shareCommon' (a : @&amp; α) : α := a` (`a` is borrowed, the result owned).</summary>
    public static Obj lean_sharecommon_quick(Obj a) => new SharecommonQuickFn().Invoke(a);
}
