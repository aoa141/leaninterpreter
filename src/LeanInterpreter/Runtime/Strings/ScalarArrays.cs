// Port of the scalar array / `ByteArray` / `FloatArray` part of lean.h (≈ lines 1213-1410),
// runtime/object.cpp ("ByteArray & FloatArray") and runtime/byteslice.cpp.
//
// Note: the `lean_float_array_*` externs (FloatArray.push/set/get/...) are assigned to the
// numbers area (docs/externs-numbers.txt) and are not defined here.

using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    // ------------------------------------------------------------------
    // Scalar arrays (low level)

    public static bool lean_sarray_is_marked_linear(Obj o) => lean_is_marked_linear_core(o);
    public static void lean_sarray_mark_linear_core(Obj o) => lean_mark_linear_core(o);

    public static Obj lean_copy_sarray(Obj a, ulong cap)
    {
        var ao = Unsafe.As<SArrayObj>(a);
        uint esz = lean_sarray_elem_size(a);
        ulong sz = (ulong)ao.m_size;
        Obj r = lean_alloc_sarray(esz, sz, cap);
        if (lean_sarray_is_marked_linear(a)) lean_sarray_mark_linear_core(r);
        Array.Copy(ao.m_data, Unsafe.As<SArrayObj>(r).m_data, (long)(esz * sz));
        lean_dec(a);
        return r;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static Obj lean_copy_sarray_nonlinear(Obj a, ulong cap)
    {
        if (lean_sarray_is_marked_linear(a) && StrRtUtil.AbortOnNonlinearity)
            throw lean_internal_panic("scalar array marked by `markLinear` was used non-linearly");
        return lean_copy_sarray(a, cap);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_sarray_ensure_exclusive(Obj a)
    {
        if (lean_is_exclusive(a)) return a;
        return lean_copy_sarray_nonlinear(a, lean_sarray_capacity(a));
    }

    public static Obj lean_sarray_mark_linear(Obj a)
    {
        Obj r = lean_sarray_ensure_exclusive(a);
        lean_sarray_mark_linear_core(r);
        return r;
    }

    public static Obj lean_sarray_propagate_mark(Obj src, Obj dst)
    {
        if (!lean_sarray_is_marked_linear(src)) return dst;
        return lean_sarray_mark_linear(dst);
    }

    /// <summary>Ensure that `a` has capacity at least `min_cap`, copying `a` otherwise.
    /// If `exact` is false, double the capacity on copying.</summary>
    public static Obj lean_sarray_ensure_capacity(Obj a, ulong min_cap, bool exact)
    {
        ulong cap = lean_sarray_capacity(a);
        if (min_cap <= cap) return a;
        else if (lean_is_exclusive(a)) return lean_copy_sarray(a, exact ? min_cap : min_cap * 2);
        else return lean_copy_sarray_nonlinear(a, exact ? min_cap : min_cap * 2);
    }

    public static bool lean_sarray_eq_cold(Obj a1, Obj a2)
    {
        var o1 = Unsafe.As<SArrayObj>(a1);
        var o2 = Unsafe.As<SArrayObj>(a2);
        int len = (int)(lean_sarray_elem_size(a1) * (ulong)o1.m_size);
        return new ReadOnlySpan<byte>(o1.m_data, 0, len).SequenceEqual(new ReadOnlySpan<byte>(o2.m_data, 0, len));
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_sarray_eq(Obj a1, Obj a2) =>
        ReferenceEquals(a1, a2) || (Unsafe.As<SArrayObj>(a1).m_size == Unsafe.As<SArrayObj>(a2).m_size && lean_sarray_eq_cold(a1, a2));

    public static byte lean_sarray_dec_eq(Obj a1, Obj a2) => lean_sarray_eq(a1, a2) ? (byte)1 : (byte)0;

    /// <summary>`lean_nat_to_size_t` (object.cpp): consumes `n` if it is a big number.</summary>
    public static ulong lean_nat_to_size_t(Obj n)
    {
        if (lean_is_scalar(n)) return lean_unbox(n);
        var v = Unsafe.As<MpzObj>(n).m_value;
        if (v.Sign < 0 || v > ulong.MaxValue) throw lean_internal_panic_out_of_memory();
        ulong sz = (ulong)v;
        lean_dec(n);
        return sz;
    }

    // ------------------------------------------------------------------
    // ByteArray

    public static Obj lean_byte_array_mk(Obj a)
    {
        var ao = Unsafe.As<ArrayObj>(a);
        ulong sz = (ulong)ao.m_size;
        Obj r = lean_alloc_sarray(1, sz, sz);
        byte[] dest = Unsafe.As<SArrayObj>(r).m_data;
        Obj[] it = ao.m_data;
        for (ulong i = 0; i < sz; i++) dest[i] = (byte)lean_unbox(it[i]);
        lean_dec(a);
        return r;
    }

    public static Obj lean_byte_array_data(Obj a)
    {
        var ao = Unsafe.As<SArrayObj>(a);
        ulong sz = (ulong)ao.m_size;
        Obj r = lean_alloc_array(sz, sz);
        Obj[] dest = Unsafe.As<ArrayObj>(r).m_data;
        byte[] it = ao.m_data;
        for (ulong i = 0; i < sz; i++) dest[i] = lean_box(it[i]);
        lean_dec(a);
        return r;
    }

    public static ulong lean_byte_array_hash(Obj a) => LeanHash.HashStr(ByteArraySpan(a), 11);

    public static Obj lean_mk_empty_byte_array(Obj capacity)
    {
        if (!lean_is_scalar(capacity)) throw lean_internal_panic_out_of_memory();
        return lean_alloc_sarray(1, 0, lean_unbox(capacity));
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_byte_array_size(Obj a) => lean_box((ulong)Unsafe.As<SArrayObj>(a).m_size);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_byte_array_uget(Obj a, ulong i) => Unsafe.As<SArrayObj>(a).m_data[i];

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_byte_array_get(Obj a, Obj i)
    {
        if (lean_is_scalar(i))
        {
            ulong idx = lean_unbox(i);
            var ao = Unsafe.As<SArrayObj>(a);
            return idx < (ulong)ao.m_size ? ao.m_data[idx] : (byte)0;
        }
        /* The index must be out of bounds. Otherwise we would be out of memory. */
        return 0;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_byte_array_fget(Obj a, Obj i) => lean_byte_array_uget(a, lean_unbox(i));

    public static Obj lean_byte_array_push(Obj a, byte b)
    {
        Obj r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(a, lean_sarray_size(a) + 1, /* exact */ false));
        var ro = Unsafe.As<SArrayObj>(r);
        ro.m_data[ro.m_size] = b;
        ro.m_size++;
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_byte_array_uset(Obj a, ulong i, byte v)
    {
        Obj r = lean_sarray_ensure_exclusive(a);
        Unsafe.As<SArrayObj>(r).m_data[i] = v;
        return r;
    }

    public static Obj lean_byte_array_set(Obj a, Obj i, byte b)
    {
        if (!lean_is_scalar(i)) return a;
        ulong idx = lean_unbox(i);
        if (idx >= (ulong)Unsafe.As<SArrayObj>(a).m_size) return a;
        return lean_byte_array_uset(a, idx, b);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_byte_array_fset(Obj a, Obj i, byte b) => lean_byte_array_uset(a, lean_unbox(i), b);

    /// <summary>`src` is borrowed; the other arguments are owned. `exact` is a `Bool`.</summary>
    public static Obj lean_byte_array_copy_slice(Obj src, Obj o_src_off, Obj dest, Obj o_dest_off, Obj o_len, byte exact)
    {
        ulong ssz = lean_sarray_size(src);
        ulong dsz = lean_sarray_size(dest);
        ulong src_off = lean_nat_to_size_t(o_src_off);
        if (src_off > ssz) return dest;
        ulong len = Math.Min(lean_nat_to_size_t(o_len), ssz - src_off);
        ulong dest_off = lean_nat_to_size_t(o_dest_off);
        if (dest_off > dsz) dest_off = dsz;
        ulong new_dsz = Math.Max(dsz, dest_off + len);
        // `src` may be `dest`: read the source buffer before `dest` is possibly consumed.
        byte[] srcData = Unsafe.As<SArrayObj>(src).m_data;
        Obj r = lean_sarray_ensure_exclusive(lean_sarray_ensure_capacity(dest, new_dsz, exact != 0));
        var ro = Unsafe.As<SArrayObj>(r);
        ro.m_size = (long)new_dsz;
        // `r` is exclusive, so the ranges definitely cannot overlap (unless `r` is `src`, then Array.Copy handles it)
        Array.Copy(srcData, (long)src_off, ro.m_data, (long)dest_off, (long)len);
        return r;
    }

    // ------------------------------------------------------------------
    // FloatArray (only the functions not assigned to the numbers area)

    public static Obj lean_mk_empty_float_array(Obj capacity)
    {
        if (!lean_is_scalar(capacity)) throw lean_internal_panic_out_of_memory();
        return lean_alloc_sarray(sizeof(double), 0, lean_unbox(capacity));
    }

    // ------------------------------------------------------------------
    // ByteSlice (byteslice.cpp)

    public static byte lean_byteslice_beq(Obj a, Obj b)
    {
        if (ReferenceEquals(a, b)) return 1;
        Obj bytearray_a = lean_ctor_get(a, 0);
        ulong start_a = lean_unbox(lean_ctor_get(a, 1));
        ulong end_a = lean_unbox(lean_ctor_get(a, 2));
        Obj bytearray_b = lean_ctor_get(b, 0);
        ulong start_b = lean_unbox(lean_ctor_get(b, 1));
        ulong end_b = lean_unbox(lean_ctor_get(b, 2));
        ulong size_a = end_a - start_a;
        ulong size_b = end_b - start_b;
        if (size_a != size_b) return 0;
        if (size_a == 0) return 1;
        var pa = new ReadOnlySpan<byte>(Unsafe.As<SArrayObj>(bytearray_a).m_data, (int)start_a, (int)size_a);
        var pb = new ReadOnlySpan<byte>(Unsafe.As<SArrayObj>(bytearray_b).m_data, (int)start_b, (int)size_b);
        return pa.SequenceEqual(pb) ? (byte)1 : (byte)0;
    }
}
