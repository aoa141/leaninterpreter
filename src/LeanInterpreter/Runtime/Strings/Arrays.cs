// Port of the `Array` part of lean.h (≈ lines 1016-1211) and runtime/object.cpp ("Arrays",
// "Array functions for generated code").

using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    // ------------------------------------------------------------------
    // Exported Lean functions

    // (Private wrappers with area-specific names to avoid clashes with other areas' helpers.)
    static delegate*<Obj, Obj, Obj> s_strarr_list_to_array;
    static delegate*<Obj, Obj, Obj> s_strarr_array_to_list_impl;

    /// <summary>`lean_list_to_array` = `List.toArrayImpl`; the first argument is the erased type.</summary>
    static Obj strarr_list_to_array(Obj type, Obj lst)
    {
        if (s_strarr_list_to_array == null) s_strarr_list_to_array = (delegate*<Obj, Obj, Obj>)LeanExports.Get("lean_list_to_array");
        return s_strarr_list_to_array(type, lst);
    }

    /// <summary>`lean_array_to_list_impl` = `Array.toListImpl`; the first argument is the erased type.</summary>
    static Obj strarr_array_to_list_impl(Obj type, Obj a)
    {
        if (s_strarr_array_to_list_impl == null) s_strarr_array_to_list_impl = (delegate*<Obj, Obj, Obj>)LeanExports.Get("lean_array_to_list_impl");
        return s_strarr_array_to_list_impl(type, a);
    }

    public static Obj lean_array_mk(Obj lst) => strarr_list_to_array(lean_box(0), lst);

    public static Obj lean_array_to_list(Obj a) => strarr_array_to_list_impl(lean_box(0), a);

    // ------------------------------------------------------------------
    // Low level

    public static bool lean_array_is_marked_linear(Obj o) => lean_is_marked_linear_core(o);
    public static void lean_array_mark_linear_core(Obj o) => lean_mark_linear_core(o);

    public static Obj lean_array_get_panic(Obj def_val) =>
        lean_panic_fn(def_val, lean_mk_ascii_string_unchecked("Error: index out of bounds"));

    public static Obj lean_array_set_panic(Obj a, Obj v)
    {
        lean_dec(v);
        return lean_panic_fn(a, lean_mk_ascii_string_unchecked("Error: index out of bounds"));
    }

    public static Obj lean_copy_expand_array(Obj a, bool expand)
    {
        var ao = Unsafe.As<ArrayObj>(a);
        ulong sz = (ulong)ao.m_size;
        ulong cap = (ulong)ao.m_data.Length;
        if (expand) cap = (cap + 1) * 2;
        var r = Unsafe.As<ArrayObj>(lean_alloc_array(sz, cap));
        if (lean_array_is_marked_linear(a)) lean_array_mark_linear_core(r);
        Obj[] src = ao.m_data;
        Obj[] dest = r.m_data;
        if (lean_is_exclusive(a))
        {
            // transfer ownership of elements directly instead of inc+dec
            Array.Copy(src, dest, (long)sz);
            // `a` is freed in C; drop our references so that stale elements are not retained.
            Array.Clear(src, 0, (int)sz);
            ao.m_size = 0;
        }
        else
        {
            for (ulong i = 0; i < sz; i++)
            {
                Obj e = src[i];
                dest[i] = e;
                lean_inc(e);
            }
            lean_dec(a);
        }
        return r;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static Obj lean_copy_expand_array_nonlinear(Obj a, bool expand)
    {
        if (lean_array_is_marked_linear(a) && StrRtUtil.AbortOnNonlinearity)
            throw lean_internal_panic("array marked by `Array.markLinear` was used non-linearly");
        return lean_copy_expand_array(a, expand);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_ensure_exclusive_array(Obj a)
    {
        if (lean_is_exclusive(a)) return a;
        return lean_copy_expand_array_nonlinear(a, false);
    }

    public static Obj lean_array_mark_linear(Obj a)
    {
        Obj r = lean_ensure_exclusive_array(a);
        lean_array_mark_linear_core(r);
        return r;
    }

    public static Obj lean_array_propagate_mark(Obj src, Obj dst)
    {
        if (!lean_array_is_marked_linear(src)) return dst;
        return lean_array_mark_linear(dst);
    }

    // ------------------------------------------------------------------
    // High level

    public static Obj lean_array_sz(Obj a)
    {
        Obj r = lean_box(lean_array_size(a));
        lean_dec(a);
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_array_get_size(Obj a) => lean_box((ulong)Unsafe.As<ArrayObj>(a).m_size);

    public static Obj lean_mk_empty_array_with_capacity(Obj capacity)
    {
        if (!lean_is_scalar(capacity)) throw lean_internal_panic_out_of_memory();
        return lean_alloc_array(0, lean_unbox(capacity));
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_array_uget(Obj a, ulong i)
    {
        Obj r = Unsafe.As<ArrayObj>(a).m_data[i];
        lean_inc(r);
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_array_uget_borrowed(Obj a, ulong i) => Unsafe.As<ArrayObj>(a).m_data[i];

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_array_fget(Obj a, Obj i) => lean_array_uget(a, lean_unbox(i));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_array_fget_borrowed(Obj a, Obj i) => Unsafe.As<ArrayObj>(a).m_data[lean_unbox(i)];

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_array_get(Obj def_val, Obj a, Obj i)
    {
        if (lean_is_scalar(i))
        {
            ulong idx = lean_unbox(i);
            var ao = Unsafe.As<ArrayObj>(a);
            if (idx < (ulong)ao.m_size)
            {
                Obj r = ao.m_data[idx];
                lean_inc(r);
                return r;
            }
        }
        /* If `i` is not a scalar, then it must be out of bounds. */
        lean_inc(def_val);
        return lean_array_get_panic(def_val);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_array_get_borrowed(Obj def_val, Obj a, Obj i)
    {
        if (lean_is_scalar(i))
        {
            ulong idx = lean_unbox(i);
            var ao = Unsafe.As<ArrayObj>(a);
            if (idx < (ulong)ao.m_size) return ao.m_data[idx];
        }
        lean_inc(def_val);
        return lean_array_get_panic(def_val);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_array_uset(Obj a, ulong i, Obj v)
    {
        Obj r = lean_ensure_exclusive_array(a);
        Obj[] d = Unsafe.As<ArrayObj>(r).m_data;
        lean_dec(d[i]);
        d[i] = v;
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_array_fset(Obj a, Obj i, Obj v) => lean_array_uset(a, lean_unbox(i), v);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_array_set(Obj a, Obj i, Obj v)
    {
        if (lean_is_scalar(i))
        {
            ulong idx = lean_unbox(i);
            if (idx < (ulong)Unsafe.As<ArrayObj>(a).m_size)
                return lean_array_uset(a, idx, v);
        }
        return lean_array_set_panic(a, v);
    }

    public static Obj lean_array_pop(Obj a)
    {
        Obj r = lean_ensure_exclusive_array(a);
        var ro = Unsafe.As<ArrayObj>(r);
        long sz = ro.m_size;
        if (sz == 0) return r;
        sz--;
        Obj last = ro.m_data[sz];
        ro.m_size = sz;
        ro.m_data[sz] = null; // not needed in C; lets the GC reclaim the element
        lean_dec(last);
        return r;
    }

    public static Obj lean_array_uswap(Obj a, ulong i, ulong j)
    {
        Obj r = lean_ensure_exclusive_array(a);
        Obj[] it = Unsafe.As<ArrayObj>(r).m_data;
        Obj v1 = it[i];
        it[i] = it[j];
        it[j] = v1;
        return r;
    }

    public static Obj lean_array_fswap(Obj a, Obj i, Obj j) => lean_array_uswap(a, lean_unbox(i), lean_unbox(j));

    public static Obj lean_array_swap(Obj a, Obj i, Obj j)
    {
        if (!lean_is_scalar(i) || !lean_is_scalar(j)) return a;
        ulong ui = lean_unbox(i);
        ulong uj = lean_unbox(j);
        ulong sz = (ulong)Unsafe.As<ArrayObj>(a).m_size;
        if (ui >= sz || uj >= sz) return a;
        return lean_array_uswap(a, ui, uj);
    }

    public static Obj lean_array_push(Obj a, Obj v)
    {
        Obj r;
        var ao = Unsafe.As<ArrayObj>(a);
        if (lean_is_exclusive(a))
        {
            if ((ulong)ao.m_data.Length > (ulong)ao.m_size)
                r = a;
            else
                r = lean_copy_expand_array(a, true);
        }
        else
        {
            r = lean_copy_expand_array_nonlinear(a, (ulong)ao.m_data.Length < 2 * (ulong)ao.m_size + 1);
        }
        var ro = Unsafe.As<ArrayObj>(r);
        ro.m_data[ro.m_size] = v;
        ro.m_size++;
        return r;
    }

    public static Obj lean_mk_array(Obj n, Obj v)
    {
        ulong sz;
        if (lean_is_scalar(n))
        {
            sz = lean_unbox(n);
        }
        else
        {
            var big = Unsafe.As<MpzObj>(n).m_value;
            if (big.Sign < 0 || big > ulong.MaxValue) throw lean_internal_panic_out_of_memory();
            sz = (ulong)big;
            lean_dec(n);
        }
        Obj r = lean_alloc_array(sz, sz);
        Obj[] it = Unsafe.As<ArrayObj>(r).m_data;
        for (ulong i = 0; i < sz; i++) it[i] = v;
        if (sz == 0)
            lean_dec(v);
        else if (sz > 1)
            lean_inc_n(v, sz - 1);
        return r;
    }
}
