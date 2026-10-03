// Port of the object layer of `lean.h` / `runtime/object.cpp`: tags, boxing, reference counting,
// constructor objects, closures, and object identity.

using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    public const int LeanMaxCtorTag = 243;
    public const int LeanPromise = 244;
    public const int LeanClosure = 245;
    public const int LeanArray = 246;
    public const int LeanStructArray = 247;
    public const int LeanScalarArray = 248;
    public const int LeanString = 249;
    public const int LeanMPZ = 250;
    public const int LeanThunk = 251;
    public const int LeanTask = 252;
    public const int LeanRef = 253;
    public const int LeanExternal = 254;
    public const int LeanReserved = 255;
    /// <summary>Tag used by `Box` (boxed scalars / "tagged pointers").</summary>
    public const byte LeanBoxTag = 255;

    public const int LEAN_MAX_CTOR_FIELDS = 256;
    public const int LEAN_MAX_CTOR_SCALARS_SIZE = 1024;
    public const int LEAN_CLOSURE_MAX_ARGS = 16;
    public const byte LEAN_LINEAR_MARK_MASK = 0x80;
    public const ulong LEAN_MAX_SMALL_NAT = ulong.MaxValue >> 1;

    // ------------------------------------------------------------------
    // Boxing

    const int BoxCacheSize = 4096;
    static readonly Box[] s_boxCache = MkBoxCache();

    static Box[] MkBoxCache()
    {
        var r = new Box[BoxCacheSize];
        for (int i = 0; i < BoxCacheSize; i++) r[i] = new Box((ulong)i);
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_box(ulong n) => n < BoxCacheSize ? s_boxCache[n] : new Box(n);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong lean_unbox(Obj o) => Unsafe.As<Box>(o).m_value;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_is_scalar(Obj o) => o.m_tag == LeanBoxTag;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_ptr_tag(Obj o) => o.m_tag;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static uint lean_ptr_other(Obj o) => o.m_other;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static uint lean_obj_tag(Obj o) => o.m_tag == LeanBoxTag ? (uint)Unsafe.As<Box>(o).m_value : o.m_tag;

    public static Obj lean_obj_tag_nat(Obj o) => lean_box(lean_obj_tag(o));

    public static bool lean_is_ctor(Obj o) => o.m_tag <= LeanMaxCtorTag;
    public static bool lean_is_closure(Obj o) => o.m_tag == LeanClosure;
    public static bool lean_is_array(Obj o) => o.m_tag == LeanArray;
    public static bool lean_is_sarray(Obj o) => o.m_tag == LeanScalarArray;
    public static bool lean_is_string(Obj o) => o.m_tag == LeanString;
    public static bool lean_is_mpz(Obj o) => o.m_tag == LeanMPZ;
    public static bool lean_is_thunk(Obj o) => o.m_tag == LeanThunk;
    public static bool lean_is_task(Obj o) => o.m_tag == LeanTask;
    public static bool lean_is_promise(Obj o) => o.m_tag == LeanPromise;
    public static bool lean_is_external(Obj o) => o.m_tag == LeanExternal;
    public static bool lean_is_ref(Obj o) => o.m_tag == LeanRef;

    // ------------------------------------------------------------------
    // Reference counting

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_is_mt(Obj o) => o.m_rc < 0;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_is_st(Obj o) => o.m_rc > 0;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_is_persistent(Obj o) => o.m_rc == 0;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_has_rc(Obj o) => o.m_rc != 0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_inc_ref(Obj o)
    {
        int rc = o.m_rc;
        if (rc > 0) o.m_rc = rc + 1;
        else if (rc != 0) Interlocked.Decrement(ref o.m_rc);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_inc_ref_n(Obj o, ulong n)
    {
        int rc = o.m_rc;
        if (rc > 0) o.m_rc = (int)Math.Min((long)rc + (long)n, int.MaxValue);
        else if (rc != 0) Interlocked.Add(ref o.m_rc, -(int)Math.Min(n, (ulong)int.MaxValue / 2));
    }

    // Boxes are persistent (rc == 0), so the scalar test is unnecessary.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_inc(Obj o) => lean_inc_ref(o);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_inc_n(Obj o, ulong n) => lean_inc_ref_n(o, n);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_dec_ref(Obj o)
    {
        int rc = o.m_rc;
        if (rc > 1) o.m_rc = rc - 1;
        else if (rc != 0) lean_dec_ref_cold(o);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_dec(Obj o) => lean_dec_ref(o);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_dec_ref_known(Obj o, uint objs) => lean_dec_ref(o);

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static void lean_dec_ref_cold(Obj o)
    {
        if (o.m_rc != 1)
        {
            // multi-threaded object: m_rc < 0
            if (Interlocked.Increment(ref o.m_rc) != 0) return;
        }
        else
        {
            o.m_rc = 0;
        }
        // The object is dead: release its children. We use an explicit work list to avoid deep
        // recursion on long lists.
        DelCore(o);
    }

    [ThreadStatic] static Stack<Obj> t_delTodo;

    static void DecForDel(Obj o, Stack<Obj> todo)
    {
        int rc = o.m_rc;
        if (rc > 1) o.m_rc = rc - 1;
        else if (rc == 1) { o.m_rc = 0; todo.Push(o); }
        else if (rc != 0)
        {
            if (Interlocked.Increment(ref o.m_rc) == 0) todo.Push(o);
        }
    }

    static void DelCore(Obj root)
    {
        var todo = t_delTodo ??= new Stack<Obj>();
        bool nested = todo.Count > 0;
        if (nested)
        {
            // re-entrant call (e.g. from an external finalizer); use a fresh stack
            todo = new Stack<Obj>();
        }
        todo.Push(root);
        while (todo.Count > 0)
        {
            Obj o = todo.Pop();
            byte tag = o.m_tag;
            if (tag <= LeanMaxCtorTag)
            {
                int n = o.m_other;
                for (int i = 0; i < n; i++)
                {
                    Obj c = lean_ctor_get_core(o, i);
                    if (c != null) DecForDel(c, todo);
                }
                continue;
            }
            switch (tag)
            {
                case LeanClosure:
                {
                    var c = Unsafe.As<Closure>(o);
                    int n = c.m_num_fixed;
                    for (int i = 0; i < n; i++) { var a = c.m_objs[i]; if (a != null) DecForDel(a, todo); }
                    break;
                }
                case LeanArray:
                {
                    var a = Unsafe.As<ArrayObj>(o);
                    long n = a.m_size;
                    var d = a.m_data;
                    for (long i = 0; i < n; i++) { var e = d[i]; if (e != null) DecForDel(e, todo); }
                    break;
                }
                case LeanThunk:
                {
                    var t = Unsafe.As<ThunkObj>(o);
                    var c = t.m_closure; if (c != null) DecForDel(c, todo);
                    var v = t.m_value; if (v != null) DecForDel(v, todo);
                    break;
                }
                case LeanRef:
                {
                    var v = Unsafe.As<RefObj>(o).m_value; if (v != null) DecForDel(v, todo);
                    break;
                }
                case LeanTask:
                    TaskDeactivateHook?.Invoke(Unsafe.As<TaskObj>(o));
                    break;
                case LeanPromise:
                    PromiseDeactivateHook?.Invoke(Unsafe.As<PromiseObj>(o));
                    break;
                case LeanExternal:
                {
                    var e = Unsafe.As<ExternalObj>(o);
                    e.m_class?.Finalize?.Invoke(e.m_data);
                    break;
                }
                default:
                    break;
            }
        }
    }

    /// <summary>Called when the RC of a task object drops to zero (set by the task manager).</summary>
    public static Action<TaskObj> TaskDeactivateHook;
    /// <summary>Called when the RC of a promise object drops to zero (set by the task manager).</summary>
    public static Action<PromiseObj> PromiseDeactivateHook;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_is_exclusive(Obj o) => o.m_rc == 1;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_is_exclusive_obj(Obj o) => o.m_rc == 1 ? (byte)1 : (byte)0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_is_shared(Obj o) => o.m_rc > 1;

    public static void lean_free_object(Obj o) { /* memory is managed by the GC */ }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_del_object(Obj o) { }

    public static bool lean_is_marked_linear_core(Obj o) => (o.m_other & LEAN_LINEAR_MARK_MASK) != 0;
    public static void lean_mark_linear_core(Obj o) => o.m_other |= LEAN_LINEAR_MARK_MASK;

    /// <summary>Enumerate the direct children of an object (used by mark_mt/mark_persistent and others).</summary>
    public static void ForEachChild(Obj o, Action<Obj> f)
    {
        byte tag = o.m_tag;
        if (tag <= LeanMaxCtorTag)
        {
            int n = o.m_other;
            for (int i = 0; i < n; i++) f(lean_ctor_get_core(o, i));
            return;
        }
        switch (tag)
        {
            case LeanClosure:
            {
                var c = Unsafe.As<Closure>(o);
                for (int i = 0; i < c.m_num_fixed; i++) f(c.m_objs[i]);
                break;
            }
            case LeanArray:
            {
                var a = Unsafe.As<ArrayObj>(o);
                for (long i = 0; i < a.m_size; i++) f(a.m_data[i]);
                break;
            }
            case LeanThunk:
            {
                var t = Unsafe.As<ThunkObj>(o);
                var c = t.m_closure; if (c != null) f(c);
                var v = t.m_value; if (v != null) f(v);
                break;
            }
            case LeanRef:
            {
                var v = Unsafe.As<RefObj>(o).m_value; if (v != null) f(v);
                break;
            }
            case LeanTask:
            {
                var v = Unsafe.As<TaskObj>(o).m_value; if (v != null) f(v);
                break;
            }
            case LeanPromise:
            {
                var r = Unsafe.As<PromiseObj>(o).m_result; if (r != null) f(r);
                break;
            }
            case LeanExternal:
            {
                var e = Unsafe.As<ExternalObj>(o);
                if (e.m_class?.Foreach != null)
                {
                    // `foreach` takes a Lean closure in C; we pass the children directly.
                    e.m_class.Foreach(e.m_data, lean_alloc_closure((delegate*<Obj, Obj>)&ForeachChildTrampoline, 1, 0));
                }
                break;
            }
        }
    }

    [ThreadStatic] static Action<Obj> t_foreachChildAction;
    static Obj ForeachChildTrampoline(Obj o) { t_foreachChildAction?.Invoke(o); return lean_box(0); }

    public static void lean_mark_persistent(Obj root)
    {
        if (root == null) return;
        var todo = new Stack<Obj>();
        todo.Push(root);
        while (todo.Count > 0)
        {
            Obj o = todo.Pop();
            if (o == null || o.m_rc == 0) continue;
            o.m_rc = 0;
            PushChildren(o, todo);
        }
    }

    public static void lean_mark_mt(Obj root)
    {
        if (root == null || root.m_rc <= 0) return;
        var todo = new Stack<Obj>();
        todo.Push(root);
        while (todo.Count > 0)
        {
            Obj o = todo.Pop();
            if (o == null || o.m_rc <= 0) continue;
            o.m_rc = -o.m_rc;
            PushChildren(o, todo);
        }
    }

    static void PushChildren(Obj o, Stack<Obj> todo)
    {
        byte tag = o.m_tag;
        if (tag <= LeanMaxCtorTag)
        {
            int n = o.m_other;
            for (int i = 0; i < n; i++) todo.Push(lean_ctor_get_core(o, i));
            return;
        }
        switch (tag)
        {
            case LeanClosure:
            {
                var c = Unsafe.As<Closure>(o);
                for (int i = 0; i < c.m_num_fixed; i++) todo.Push(c.m_objs[i]);
                break;
            }
            case LeanArray:
            {
                var a = Unsafe.As<ArrayObj>(o);
                for (long i = 0; i < a.m_size; i++) todo.Push(a.m_data[i]);
                break;
            }
            case LeanThunk:
            {
                var t = Unsafe.As<ThunkObj>(o);
                todo.Push(t.m_closure); todo.Push(t.m_value);
                break;
            }
            case LeanRef:
                todo.Push(Unsafe.As<RefObj>(o).m_value);
                break;
            case LeanTask:
                todo.Push(Unsafe.As<TaskObj>(o).m_value);
                break;
            case LeanPromise:
                todo.Push(Unsafe.As<PromiseObj>(o).m_result);
                break;
            case LeanExternal:
            {
                var e = Unsafe.As<ExternalObj>(o);
                if (e.m_class?.Foreach != null)
                {
                    var prev = t_foreachChildAction;
                    t_foreachChildAction = c => todo.Push(c);
                    try
                    {
                        var f = lean_alloc_closure((delegate*<Obj, Obj>)&ForeachChildTrampoline, 1, 0);
                        e.m_class.Foreach(e.m_data, f);
                    }
                    finally { t_foreachChildAction = prev; }
                }
                break;
            }
        }
    }

    public static void lean_runtime_mark_persistent_core(Obj o) => lean_mark_persistent(o);

    // ------------------------------------------------------------------
    // Object identity (`ptrAddrUnsafe`)

    static long s_nextId = 0;

    /// <summary>Unique, stable pseudo-address of an object. Scalars map to their tagged-pointer value.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong lean_ptr_addr(Obj o)
    {
        if (o.m_tag == LeanBoxTag) return (Unsafe.As<Box>(o).m_value << 1) | 1;
        long id = o.m_id;
        if (id != 0) return (ulong)id;
        return AssignId(o);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    static ulong AssignId(Obj o)
    {
        long id = Interlocked.Add(ref s_nextId, 16) + 0x100000;
        long prev = Interlocked.CompareExchange(ref o.m_id, id, 0);
        return (ulong)(prev == 0 ? id : prev);
    }

    // ------------------------------------------------------------------
    // Constructor objects

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_alloc_ctor(uint tag, uint num_objs, uint scalar_sz)
    {
        LeanHeartbeats.t_count++;
        Ctor o = num_objs switch
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
            _ => new CtorN { rest = new Obj[num_objs - 8] },
        };
        o.m_tag = (byte)tag;
        o.m_other = (byte)num_objs;
        if (scalar_sz != 0)
        {
            o.m_cs_sz = (ushort)scalar_sz;
            if (scalar_sz > 8) o.sx = new byte[scalar_sz - 8];
        }
        return o;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static uint lean_ctor_num_objs(Obj o) => o.m_other;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_ctor_get(Obj o, uint i)
    {
        // (a null field is a field of a lazily decoded region object that was not read yet)
        switch (i)
        {
            case 0: return Unsafe.As<Ctor1>(o).f0 ?? lean_ctor_force(o, i);
            case 1: return Unsafe.As<Ctor2>(o).f1 ?? lean_ctor_force(o, i);
            case 2: return Unsafe.As<Ctor3>(o).f2 ?? lean_ctor_force(o, i);
            case 3: return Unsafe.As<Ctor4>(o).f3 ?? lean_ctor_force(o, i);
            case 4: return Unsafe.As<Ctor5>(o).f4 ?? lean_ctor_force(o, i);
            case 5: return Unsafe.As<Ctor6>(o).f5 ?? lean_ctor_force(o, i);
            case 6: return Unsafe.As<Ctor7>(o).f6 ?? lean_ctor_force(o, i);
            case 7: return Unsafe.As<Ctor8>(o).f7 ?? lean_ctor_force(o, i);
            default: return Unsafe.As<CtorN>(o).rest[i - 8] ?? lean_ctor_force(o, i);
        }
    }

    /// <summary>
    /// Slow path of `lean_ctor_get`: object field `i` of `o` is null. Objects of lazily decoded
    /// `.olean` regions get their fields on first use (Compact/LazyRegion.cs).
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    public static Obj lean_ctor_force(Obj o, uint i) => Compact.LazyRegion.ForceField(o, i);

    public static Obj lean_ctor_get_core(Obj o, int i) => lean_ctor_get(o, (uint)i);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set(Obj o, uint i, Obj v)
    {
        switch (i)
        {
            case 0: Unsafe.As<Ctor1>(o).f0 = v; return;
            case 1: Unsafe.As<Ctor2>(o).f1 = v; return;
            case 2: Unsafe.As<Ctor3>(o).f2 = v; return;
            case 3: Unsafe.As<Ctor4>(o).f3 = v; return;
            case 4: Unsafe.As<Ctor5>(o).f4 = v; return;
            case 5: Unsafe.As<Ctor6>(o).f5 = v; return;
            case 6: Unsafe.As<Ctor7>(o).f6 = v; return;
            case 7: Unsafe.As<Ctor8>(o).f7 = v; return;
            default: Unsafe.As<CtorN>(o).rest[i - 8] = v; return;
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_tag(Obj o, uint new_tag) => o.m_tag = (byte)new_tag;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_release(Obj o, uint i)
    {
        lean_dec(lean_ctor_get(o, i));
        lean_ctor_set(o, i, lean_box(0));
    }

    /// <summary>
    /// `reuse x in ctor_i ys`: reuse the memory cell of `x` if it is a constructor object with a
    /// compatible layout, otherwise allocate a fresh object.
    /// </summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_ctor_reuse(Obj x, uint tag, uint num_objs, uint scalar_sz, bool updt_header)
    {
        if (x.m_tag == LeanBoxTag || x.m_other != num_objs || x.m_cs_sz != scalar_sz)
            return lean_alloc_ctor(tag, num_objs, scalar_sz);
        if (updt_header) x.m_tag = (byte)tag;
        return x;
    }

    // Scalar fields. `_s` variants take offsets relative to the start of the scalar area; the
    // standard variants take offsets relative to the start of the object fields, as in C.

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static uint ScalarRel(Obj o, uint offset) => offset - 8u * o.m_other;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_ctor_get_uint8_s(Obj o, uint r)
    {
        var c = Unsafe.As<Ctor>(o);
        return r < 8 ? (byte)(c.s0 >> (int)(8 * r)) : c.sx[r - 8];
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_uint8_s(Obj o, uint r, byte v)
    {
        var c = Unsafe.As<Ctor>(o);
        if (r < 8)
        {
            int sh = (int)(8 * r);
            c.s0 = (c.s0 & ~(0xFFUL << sh)) | ((ulong)v << sh);
        }
        else c.sx[r - 8] = v;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ushort lean_ctor_get_uint16_s(Obj o, uint r)
    {
        var c = Unsafe.As<Ctor>(o);
        return r < 8 ? (ushort)(c.s0 >> (int)(8 * r)) : Unsafe.ReadUnaligned<ushort>(ref c.sx[r - 8]);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_uint16_s(Obj o, uint r, ushort v)
    {
        var c = Unsafe.As<Ctor>(o);
        if (r < 8)
        {
            int sh = (int)(8 * r);
            c.s0 = (c.s0 & ~(0xFFFFUL << sh)) | ((ulong)v << sh);
        }
        else Unsafe.WriteUnaligned(ref c.sx[r - 8], v);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static uint lean_ctor_get_uint32_s(Obj o, uint r)
    {
        var c = Unsafe.As<Ctor>(o);
        return r < 8 ? (uint)(c.s0 >> (int)(8 * r)) : Unsafe.ReadUnaligned<uint>(ref c.sx[r - 8]);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_uint32_s(Obj o, uint r, uint v)
    {
        var c = Unsafe.As<Ctor>(o);
        if (r < 8)
        {
            int sh = (int)(8 * r);
            c.s0 = (c.s0 & ~(0xFFFFFFFFUL << sh)) | ((ulong)v << sh);
        }
        else Unsafe.WriteUnaligned(ref c.sx[r - 8], v);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong lean_ctor_get_uint64_s(Obj o, uint r)
    {
        var c = Unsafe.As<Ctor>(o);
        return r == 0 ? c.s0 : Unsafe.ReadUnaligned<ulong>(ref c.sx[r - 8]);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_uint64_s(Obj o, uint r, ulong v)
    {
        var c = Unsafe.As<Ctor>(o);
        if (r == 0) c.s0 = v; else Unsafe.WriteUnaligned(ref c.sx[r - 8], v);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static double lean_ctor_get_float_s(Obj o, uint r) => BitConverter.UInt64BitsToDouble(lean_ctor_get_uint64_s(o, r));
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_float_s(Obj o, uint r, double v) => lean_ctor_set_uint64_s(o, r, BitConverter.DoubleToUInt64Bits(v));
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static float lean_ctor_get_float32_s(Obj o, uint r) => BitConverter.UInt32BitsToSingle(lean_ctor_get_uint32_s(o, r));
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_float32_s(Obj o, uint r, float v) => lean_ctor_set_uint32_s(o, r, BitConverter.SingleToUInt32Bits(v));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_ctor_get_uint8(Obj o, uint offset) => lean_ctor_get_uint8_s(o, ScalarRel(o, offset));
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ushort lean_ctor_get_uint16(Obj o, uint offset) => lean_ctor_get_uint16_s(o, ScalarRel(o, offset));
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static uint lean_ctor_get_uint32(Obj o, uint offset) => lean_ctor_get_uint32_s(o, ScalarRel(o, offset));
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong lean_ctor_get_uint64(Obj o, uint offset) => lean_ctor_get_uint64_s(o, ScalarRel(o, offset));
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static double lean_ctor_get_float(Obj o, uint offset) => lean_ctor_get_float_s(o, ScalarRel(o, offset));
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static float lean_ctor_get_float32(Obj o, uint offset) => lean_ctor_get_float32_s(o, ScalarRel(o, offset));
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_uint8(Obj o, uint offset, byte v) => lean_ctor_set_uint8_s(o, ScalarRel(o, offset), v);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_uint16(Obj o, uint offset, ushort v) => lean_ctor_set_uint16_s(o, ScalarRel(o, offset), v);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_uint32(Obj o, uint offset, uint v) => lean_ctor_set_uint32_s(o, ScalarRel(o, offset), v);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_uint64(Obj o, uint offset, ulong v) => lean_ctor_set_uint64_s(o, ScalarRel(o, offset), v);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_float(Obj o, uint offset, double v) => lean_ctor_set_float_s(o, ScalarRel(o, offset), v);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_float32(Obj o, uint offset, float v) => lean_ctor_set_float32_s(o, ScalarRel(o, offset), v);

    /// <summary>`i` is a slot index (&gt;= number of object fields), as in C.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong lean_ctor_get_usize(Obj o, uint i) => lean_ctor_get_uint64_s(o, 8u * (i - o.m_other));
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_ctor_set_usize(Obj o, uint i, ulong v) => lean_ctor_set_uint64_s(o, 8u * (i - o.m_other), v);

    /// <summary>Copy of the scalar area of a constructor object (length `m_cs_sz`).</summary>
    public static byte[] CtorScalarBytes(Obj o)
    {
        var c = Unsafe.As<Ctor>(o);
        int sz = c.m_cs_sz;
        var r = new byte[sz];
        for (int i = 0; i < sz && i < 8; i++) r[i] = (byte)(c.s0 >> (8 * i));
        if (sz > 8) Array.Copy(c.sx, 0, r, 8, sz - 8);
        return r;
    }

    public static void SetCtorScalarBytes(Obj o, ReadOnlySpan<byte> data)
    {
        var c = Unsafe.As<Ctor>(o);
        ulong s0 = 0;
        for (int i = 0; i < data.Length && i < 8; i++) s0 |= (ulong)data[i] << (8 * i);
        c.s0 = s0;
        if (data.Length > 8)
        {
            if (c.sx == null || c.sx.Length != data.Length - 8) c.sx = new byte[data.Length - 8];
            data.Slice(8).CopyTo(c.sx);
        }
    }

    // ------------------------------------------------------------------
    // Closures

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_alloc_closure(void* fun, uint arity, uint num_fixed)
    {
        // (no heartbeat: natively closures, arrays and strings come from `lean_alloc_object`,
        // which does not count; see `LeanHeartbeats`)
        return new Closure
        {
            m_tag = LeanClosure,
            m_fun = fun,
            m_arity = (ushort)arity,
            m_num_fixed = (ushort)num_fixed,
            m_objs = num_fixed == 0 ? Array.Empty<Obj>() : new Obj[num_fixed],
        };
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_closure_set(Obj o, uint i, Obj a) => Unsafe.As<Closure>(o).m_objs[i] = a;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_closure_get(Obj o, uint i) => Unsafe.As<Closure>(o).m_objs[i];
    public static void* lean_closure_fun(Obj o) => Unsafe.As<Closure>(o).m_fun;
    public static uint lean_closure_arity(Obj o) => Unsafe.As<Closure>(o).m_arity;
    public static uint lean_closure_num_fixed(Obj o) => Unsafe.As<Closure>(o).m_num_fixed;

    // ------------------------------------------------------------------
    // Refs

    public static Obj lean_st_mk_ref(Obj a)
    {
        LeanHeartbeats.t_count++;
        var r = new RefObj { m_tag = LeanRef, m_value = a };
        if (LeanGlobalRefs.Recording) LeanGlobalRefs.Register(r);
        else LeanGlobalRefs.LateRefHook?.Invoke(r);
        return r;
    }

    // ------------------------------------------------------------------
    // IO results

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_io_mk_world() => lean_box(0);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_io_result_is_ok(Obj r) => r.m_tag == 0;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_io_result_is_error(Obj r) => r.m_tag == 1;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_io_result_get_value(Obj r) => lean_ctor_get(r, 0);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_io_result_get_error(Obj r) => lean_ctor_get(r, 0);

    public static Obj lean_io_result_take_value(Obj r)
    {
        Obj v = lean_io_result_get_value(r);
        lean_inc(v);
        lean_dec(r);
        return v;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_io_result_mk_ok(Obj a)
    {
        LeanHeartbeats.t_count++; // `lean_alloc_ctor`
        var r = new Ctor1 { m_tag = 0, m_other = 1, f0 = a };
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_io_result_mk_error(Obj e)
    {
        LeanHeartbeats.t_count++; // `lean_alloc_ctor`
        var r = new Ctor1 { m_tag = 1, m_other = 1, f0 = e };
        return r;
    }

    public static Obj lean_void_mk(Obj a) { lean_dec(a); return lean_box(0); }

    // ------------------------------------------------------------------
    // Once cells (closed terms)

    static readonly object s_onceLock = new object();

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static Obj lean_obj_once(ref Obj cell, delegate*<Obj> init)
    {
        var v = Volatile.Read(ref cell);
        if (v != null) return v;
        lock (s_onceLock)
        {
            v = cell;
            if (v != null) return v;
            v = init();
            lean_mark_persistent(v);
            Volatile.Write(ref cell, v);
            return v;
        }
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static T lean_scalar_once<T>(ref T cell, ref int state, delegate*<T> init) where T : unmanaged
    {
        if (Volatile.Read(ref state) == 2) return cell;
        lock (s_onceLock)
        {
            if (state == 2) return cell;
            cell = init();
            Volatile.Write(ref state, 2);
            return cell;
        }
    }
}
