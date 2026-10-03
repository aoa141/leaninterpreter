// Port of the string part of lean.h (≈ lines 1410-1523) and runtime/object.cpp ("Strings").
//
// Strings are UTF-8 byte buffers with a terminating NUL counted in `m_size`; `m_length` is the
// number of code points and `String.Pos` values are byte offsets.

using System.Globalization;
using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    // ------------------------------------------------------------------
    // Low level

    /* instance : inhabited char := ⟨'A'⟩ */
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static uint lean_char_default_value() => 'A';

    public static ulong lean_utf8_strlen(ReadOnlySpan<byte> str) => LeanUtf8.Strlen(str);
    public static ulong lean_utf8_n_strlen(ReadOnlySpan<byte> str, ulong n) => LeanUtf8.NStrlen(str, n);

    public static bool lean_string_is_marked_linear(Obj o) => lean_is_marked_linear_core(o);
    public static void lean_string_mark_linear_core(Obj o) => lean_mark_linear_core(o);

    static void check_string_linearity(Obj s)
    {
        if (lean_string_is_marked_linear(s) && StrRtUtil.AbortOnNonlinearity)
            throw lean_internal_panic("string marked by `String.markLinear` was used non-linearly");
    }

    public static Obj lean_copy_string(Obj s, ulong cap)
    {
        var so = Unsafe.As<StrObj>(s);
        ulong sz = (ulong)so.m_size;
        var r = Unsafe.As<StrObj>(lean_alloc_string(sz, cap, (ulong)so.m_length));
        if (lean_string_is_marked_linear(s)) lean_string_mark_linear_core(r);
        Array.Copy(so.m_data, r.m_data, (long)sz);
        lean_dec_ref(s);
        return r;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static Obj lean_copy_string_nonlinear(Obj s, ulong cap)
    {
        check_string_linearity(s);
        return lean_copy_string(s, cap);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_string_ensure_exclusive(Obj s)
    {
        if (lean_is_exclusive(s)) return s;
        return lean_copy_string_nonlinear(s, lean_string_capacity(s));
    }

    public static Obj lean_string_mark_linear(Obj s)
    {
        Obj r = lean_string_ensure_exclusive(s);
        lean_string_mark_linear_core(r);
        return r;
    }

    public static Obj lean_string_propagate_mark(Obj src, Obj dst)
    {
        if (!lean_string_is_marked_linear(src)) return dst;
        return lean_string_mark_linear(dst);
    }

    /// <summary>`string_ensure_capacity` (object.cpp). `o` must be exclusive.</summary>
    static Obj string_ensure_capacity(Obj o, ulong extra)
    {
        var so = Unsafe.As<StrObj>(o);
        ulong sz = (ulong)so.m_size;
        ulong cap = (ulong)so.m_data.Length;
        if (sz + extra > cap)
        {
            var n = Unsafe.As<StrObj>(lean_alloc_string(sz, cap + sz + extra, (ulong)so.m_length));
            if (lean_string_is_marked_linear(o)) lean_string_mark_linear_core(n);
            Array.Copy(so.m_data, n.m_data, (long)sz);
            return n;
        }
        return o;
    }

    /// <summary>`mk_capacity` (object.cpp).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static ulong string_mk_capacity(ulong sz) => sz * 2;

    /// <summary>`lean_mk_string_from_bytes_unchecked` with C semantics for the code point count (`utf8_strlen`).</summary>
    static Obj mk_string_from_bytes_unchecked_c(ReadOnlySpan<byte> s) =>
        lean_mk_string_unchecked(s, (ulong)s.Length, LeanUtf8.NStrlen(s, (ulong)s.Length));

    /// <summary>`lean_mk_string_lossy_recover` (object.cpp).</summary>
    static Obj lean_mk_string_lossy_recover(ReadOnlySpan<byte> s, ulong sz, ulong pos, ulong i)
    {
        var str = new List<byte>((int)sz + 8);
        for (ulong k = 0; k < pos; k++) str.Add(s[(int)k]);
        ulong start = pos;
        while (pos < sz)
        {
            if (!LeanUtf8.ValidateOne(s, sz, ref pos))
            {
                for (ulong k = start; k < pos; k++) str.Add(s[(int)k]);
                // U+FFFD REPLACEMENT CHARACTER
                str.Add(0xEF); str.Add(0xBF); str.Add(0xBD);
                do pos++; while (pos < sz && (s[(int)pos] & 0xc0) == 0x80);
                start = pos;
            }
            i++;
        }
        for (ulong k = start; k < pos; k++) str.Add(s[(int)k]);
        var arr = str.ToArray();
        return lean_mk_string_unchecked(arr, (ulong)arr.Length, i);
    }

    /// <summary>`lean_mk_string_from_bytes` with exactly the C replacement strategy for invalid UTF-8.</summary>
    public static Obj lean_mk_string_from_bytes_lossy(ReadOnlySpan<byte> s)
    {
        ulong pos = 0, i = 0;
        ulong sz = (ulong)s.Length;
        if (LeanUtf8.Validate(s, sz, ref pos, ref i))
            return lean_mk_string_unchecked(s, pos, i);
        return lean_mk_string_lossy_recover(s, sz, pos, i);
    }

    public static Obj lean_decode_lossy_utf8(Obj a)
    {
        var sa = Unsafe.As<SArrayObj>(a);
        return lean_mk_string_from_bytes_lossy(new ReadOnlySpan<byte>(sa.m_data, 0, (int)sa.m_size));
    }

    public static Obj lean_string_from_utf8_unchecked(Obj a)
    {
        var sa = Unsafe.As<SArrayObj>(a);
        Obj ret = mk_string_from_bytes_unchecked_c(new ReadOnlySpan<byte>(sa.m_data, 0, (int)sa.m_size));
        lean_dec(a);
        return ret;
    }

    public static byte lean_string_validate_utf8(Obj a)
    {
        var sa = Unsafe.As<SArrayObj>(a);
        ulong pos = 0, i = 0;
        return LeanUtf8.Validate(new ReadOnlySpan<byte>(sa.m_data, 0, (int)sa.m_size), (ulong)sa.m_size, ref pos, ref i) ? (byte)1 : (byte)0;
    }

    public static Obj lean_string_to_utf8(Obj s)
    {
        ulong sz = lean_string_size(s) - 1;
        Obj r = lean_alloc_sarray(1, sz, sz);
        Array.Copy(Unsafe.As<StrObj>(s).m_data, Unsafe.As<SArrayObj>(r).m_data, (long)sz);
        return r;
    }

    // ------------------------------------------------------------------
    // Destructive updates

    public static Obj lean_string_push(Obj s, uint c)
    {
        ulong sz = lean_string_size(s);
        Obj r;
        if (!lean_is_exclusive(s))
            r = lean_copy_string_nonlinear(s, string_mk_capacity(sz + 5));
        else
            r = string_ensure_capacity(s, 5);
        var ro = Unsafe.As<StrObj>(r);
        int consumed = LeanUtf8.PushUnicodeScalar(ro.m_data, (long)sz - 1, c);
        ro.m_size = (long)sz + consumed;
        ro.m_length++;
        ro.m_data[(long)sz + consumed - 1] = 0;
        return r;
    }

    /// <summary>`s1` is owned, `s2` borrowed.</summary>
    public static Obj lean_string_append(Obj s1, Obj s2)
    {
        var o1 = Unsafe.As<StrObj>(s1);
        var o2 = Unsafe.As<StrObj>(s2);
        ulong sz1 = (ulong)o1.m_size;
        ulong sz2 = (ulong)o2.m_size;
        ulong len1 = (ulong)o1.m_length;
        ulong len2 = (ulong)o2.m_length;
        ulong new_len = len1 + len2;
        ulong new_sz = sz1 + sz2 - 1;
        Obj r;
        if (!lean_is_exclusive(s1))
            r = lean_copy_string_nonlinear(s1, string_mk_capacity(new_sz));
        else
            r = string_ensure_capacity(s1, sz2 - 1);
        var ro = Unsafe.As<StrObj>(r);
        // `s2` may be the same object as `s1` only when `s1` is shared (then `r` is a copy).
        Array.Copy(o2.m_data, 0, ro.m_data, (long)sz1 - 1, (long)sz2 - 1);
        ro.m_size = (long)new_sz;
        ro.m_length = (long)new_len;
        ro.m_data[new_sz - 1] = 0;
        return r;
    }

    // ------------------------------------------------------------------
    // Comparison

    public static bool lean_string_eq_cold(Obj s1, Obj s2)
    {
        var o1 = Unsafe.As<StrObj>(s1);
        var o2 = Unsafe.As<StrObj>(s2);
        int n = (int)o1.m_size;
        return new ReadOnlySpan<byte>(o1.m_data, 0, n).SequenceEqual(new ReadOnlySpan<byte>(o2.m_data, 0, n));
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_string_eq(Obj s1, Obj s2) =>
        ReferenceEquals(s1, s2) || (Unsafe.As<StrObj>(s1).m_size == Unsafe.As<StrObj>(s2).m_size && lean_string_eq_cold(s1, s2));

    public static bool lean_string_ne(Obj s1, Obj s2) => !lean_string_eq(s1, s2);

    public static bool lean_string_lt(Obj s1, Obj s2) =>
        lean_string_span(s1).SequenceCompareTo(lean_string_span(s2)) < 0;

    /// <summary>Constructor indices of `Ordering`: lt = 0, eq = 1, gt = 2.</summary>
    public static byte lean_string_compare(Obj s1, Obj s2)
    {
        int r = lean_string_span(s1).SequenceCompareTo(lean_string_span(s2));
        return r < 0 ? (byte)0 : r > 0 ? (byte)2 : (byte)1;
    }

    public static byte lean_string_dec_eq(Obj s1, Obj s2) => lean_string_eq(s1, s2) ? (byte)1 : (byte)0;
    public static byte lean_string_dec_lt(Obj s1, Obj s2) => lean_string_lt(s1, s2) ? (byte)1 : (byte)0;

    public static ulong lean_string_hash(Obj s) => LeanHash.HashStr(lean_string_span(s), 11);

    public static Obj lean_string_of_usize(ulong n)
    {
        string t = n.ToString(CultureInfo.InvariantCulture);
        var b = new byte[t.Length];
        for (int i = 0; i < t.Length; i++) b[i] = (byte)t[i];
        return lean_mk_string_unchecked(b, (ulong)b.Length, (ulong)b.Length);
    }

    public static byte lean_string_memcmp(Obj s1, Obj s2, Obj lstart, Obj rstart, Obj len)
    {
        // Thanks to the proof arguments we know that lstart, rstart and len are all scalars.
        int n = (int)lean_unbox(len);
        var l = new ReadOnlySpan<byte>(Unsafe.As<StrObj>(s1).m_data, (int)lean_unbox(lstart), n);
        var r = new ReadOnlySpan<byte>(Unsafe.As<StrObj>(s2).m_data, (int)lean_unbox(rstart), n);
        return l.SequenceEqual(r) ? (byte)1 : (byte)0;
    }

    // ------------------------------------------------------------------
    // List Char conversions

    public static Obj lean_string_length(Obj s) => lean_box(lean_string_len(s));
    public static Obj lean_string_utf8_byte_size(Obj s) => lean_box(lean_string_size(s) - 1);

    public static Obj lean_string_mk(Obj cs)
    {
        // First pass: compute the size.
        long sz = 0;
        ulong len = 0;
        Obj o = cs;
        while (!lean_is_scalar(o))
        {
            sz += LeanUtf8.ScalarSize(StrRtUtil.UnboxUInt32(lean_ctor_get(o, 0)));
            o = lean_ctor_get(o, 1);
            len++;
        }
        var r = Unsafe.As<StrObj>(lean_alloc_string((ulong)sz + 1, (ulong)sz + 1, len));
        long pos = 0;
        o = cs;
        while (!lean_is_scalar(o))
        {
            pos += LeanUtf8.PushUnicodeScalar(r.m_data, pos, StrRtUtil.UnboxUInt32(lean_ctor_get(o, 0)));
            o = lean_ctor_get(o, 1);
        }
        r.m_data[sz] = 0;
        lean_dec(cs);
        return r;
    }

    public static Obj lean_string_data(Obj s)
    {
        var so = Unsafe.As<StrObj>(s);
        ulong size = (ulong)so.m_size - 1;
        var str = new ReadOnlySpan<byte>(so.m_data, 0, (int)size);
        var tmp = new List<uint>((int)Math.Min((ulong)so.m_length, int.MaxValue));
        ulong i = 0;
        while (i < size) tmp.Add(LeanUtf8.NextUtf8(str, size, ref i));
        lean_dec_ref(s);
        Obj r = StrRtUtil.BoxUInt32(0);
        for (int k = tmp.Count - 1; k >= 0; k--)
        {
            Obj new_r = lean_alloc_ctor(1, 2, 0);
            lean_ctor_set(new_r, 0, StrRtUtil.BoxUInt32(tmp[k]));
            lean_ctor_set(new_r, 1, r);
            r = new_r;
        }
        return r;
    }

    // ------------------------------------------------------------------
    // Positions

    static bool lean_string_utf8_get_core(byte[] str, ulong size, ulong i, out uint result)
    {
        uint c = str[i];
        /* zero continuation (0 to 0x7F) */
        if ((c & 0x80) == 0)
        {
            result = c;
            return true;
        }
        /* one continuation (0x80 to 0x7FF) */
        if ((c & 0xe0) == 0xc0 && i + 1 < size)
        {
            uint c1 = str[i + 1];
            result = ((c & 0x1f) << 6) | (c1 & 0x3f);
            if (result >= 0x80) return true;
        }
        /* two continuations (0x800 to 0xD7FF and 0xE000 to 0xFFFF) */
        if ((c & 0xf0) == 0xe0 && i + 2 < size)
        {
            uint c1 = str[i + 1];
            uint c2 = str[i + 2];
            result = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
            if (result >= 0x800 && (result < 0xD800 || result > 0xDFFF)) return true;
        }
        /* three continuations (0x10000 to 0x10FFFF) */
        if ((c & 0xf8) == 0xf0 && i + 3 < size)
        {
            uint c1 = str[i + 1];
            uint c2 = str[i + 2];
            uint c3 = str[i + 3];
            result = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
            if (result >= 0x10000 && result <= 0x10FFFF) return true;
        }
        /* invalid UTF-8 encoded string */
        result = 0;
        return false;
    }

    public static uint lean_string_utf8_get(Obj s, Obj i0)
    {
        /* If `i0` is not a scalar, then it must be > LEAN_MAX_SMALL_NAT and not a valid index. */
        if (!lean_is_scalar(i0)) return lean_char_default_value();
        ulong i = lean_unbox(i0);
        var so = Unsafe.As<StrObj>(s);
        ulong size = (ulong)so.m_size - 1;
        if (i >= size) return lean_char_default_value();
        if (lean_string_utf8_get_core(so.m_data, size, i, out uint result)) return result;
        return lean_char_default_value();
    }

    public static uint lean_string_utf8_get_fast_cold(byte[] str, ulong i, ulong size, byte c0)
    {
        uint c = c0;
        /* one continuation (0x80 to 0x7FF) */
        if ((c & 0xe0) == 0xc0 && i + 1 < size)
        {
            uint c1 = str[i + 1];
            uint result = ((c & 0x1f) << 6) | (c1 & 0x3f);
            if (result >= 0x80) return result;
        }
        /* two continuations (0x800 to 0xD7FF and 0xE000 to 0xFFFF) */
        if ((c & 0xf0) == 0xe0 && i + 2 < size)
        {
            uint c1 = str[i + 1];
            uint c2 = str[i + 2];
            uint result = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
            if (result >= 0x800 && (result < 0xD800 || result > 0xDFFF)) return result;
        }
        /* three continuations (0x10000 to 0x10FFFF) */
        if ((c & 0xf8) == 0xf0 && i + 3 < size)
        {
            uint c1 = str[i + 1];
            uint c2 = str[i + 2];
            uint c3 = str[i + 3];
            uint result = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
            if (result >= 0x10000 && result <= 0x10FFFF) return result;
        }
        /* invalid UTF-8 encoded string */
        return lean_char_default_value();
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static uint lean_string_utf8_get_fast(Obj s, Obj i)
    {
        var so = Unsafe.As<StrObj>(s);
        ulong idx = lean_unbox(i);
        byte c = so.m_data[idx];
        if ((c & 0x80) == 0) return c;
        return lean_string_utf8_get_fast_cold(so.m_data, idx, (ulong)so.m_size, c);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_string_get_byte_fast(Obj s, Obj i) => Unsafe.As<StrObj>(s).m_data[lean_unbox(i)];

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_string_uget_byte_fast(Obj s, ulong i) => Unsafe.As<StrObj>(s).m_data[i];

    public static Obj lean_string_utf8_get_opt(Obj s, Obj i0)
    {
        if (!lean_is_scalar(i0)) return lean_box(0);
        ulong i = lean_unbox(i0);
        var so = Unsafe.As<StrObj>(s);
        ulong size = (ulong)so.m_size - 1;
        if (i >= size) return lean_box(0);
        if (lean_string_utf8_get_core(so.m_data, size, i, out uint result))
        {
            Obj new_r = lean_alloc_ctor(1, 1, 0);
            lean_ctor_set(new_r, 0, StrRtUtil.BoxUInt32(result));
            return new_r;
        }
        return lean_box(0);
    }

    static uint lean_string_utf8_get_panic()
    {
        lean_panic_fn(lean_box(0), lean_mk_ascii_string_unchecked("Error: invalid `String.Pos` at `String.get!`"));
        return lean_char_default_value();
    }

    public static uint lean_string_utf8_get_bang(Obj s, Obj i0)
    {
        if (!lean_is_scalar(i0)) return lean_string_utf8_get_panic();
        ulong i = lean_unbox(i0);
        var so = Unsafe.As<StrObj>(s);
        ulong size = (ulong)so.m_size - 1;
        if (i >= size) return lean_string_utf8_get_panic();
        if (lean_string_utf8_get_core(so.m_data, size, i, out uint result)) return result;
        return lean_string_utf8_get_panic();
    }

    public static Obj lean_string_utf8_next(Obj s, Obj i0)
    {
        if (!lean_is_scalar(i0)) return StrRtUtil.NatSucc(i0);
        ulong i = lean_unbox(i0);
        var so = Unsafe.As<StrObj>(s);
        ulong size = (ulong)so.m_size - 1;
        /* `c.utf8ByteSize` is 1 when `i` is not a valid position in the reference implementation. */
        if (i >= size) return lean_usize_to_nat(i + 1);
        uint c = so.m_data[i];
        if ((c & 0x80) == 0) return lean_box(i + 1);
        if ((c & 0xe0) == 0xc0) return lean_box(i + 2);
        if ((c & 0xf0) == 0xe0) return lean_box(i + 3);
        if ((c & 0xf8) == 0xf0) return lean_box(i + 4);
        /* invalid UTF-8 encoded string */
        return lean_box(i + 1);
    }

    public static Obj lean_string_utf8_next_fast_cold(ulong i, byte c)
    {
        if ((c & 0xe0) == 0xc0) return lean_box(i + 2);
        if ((c & 0xf0) == 0xe0) return lean_box(i + 3);
        if ((c & 0xf8) == 0xf0) return lean_box(i + 4);
        /* invalid UTF-8 encoded string */
        return lean_box(i + 1);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_string_utf8_next_fast(Obj s, Obj i)
    {
        ulong idx = lean_unbox(i);
        byte c = Unsafe.As<StrObj>(s).m_data[idx];
        if ((c & 0x80) == 0) return lean_box(idx + 1);
        return lean_string_utf8_next_fast_cold(idx, c);
    }

    public static byte lean_string_is_valid_pos(Obj s, Obj i0)
    {
        if (!lean_is_scalar(i0)) return 0;
        ulong i = lean_unbox(i0);
        var so = Unsafe.As<StrObj>(s);
        ulong sz = (ulong)so.m_size - 1;
        if (i > sz) return 0;
        if (i == sz) return 1;
        return LeanUtf8.IsUtf8FirstByte(so.m_data[i]) ? (byte)1 : (byte)0;
    }

    public static Obj lean_string_utf8_extract_fast(Obj s, Obj b0, Obj e0)
    {
        ulong b = lean_unbox(b0);
        ulong e = lean_unbox(e0);
        if (b >= e) return lean_mk_string_unchecked(ReadOnlySpan<byte>.Empty, 0, 0);
        return mk_string_from_bytes_unchecked_c(new ReadOnlySpan<byte>(Unsafe.As<StrObj>(s).m_data, (int)b, (int)(e - b)));
    }

    public static Obj lean_string_utf8_extract(Obj s, Obj b0, Obj e0)
    {
        /* Replace non-scalar values with SIZE_MAX: non-scalar values are out of bounds here. */
        ulong b = lean_is_scalar(b0) ? lean_unbox(b0) : ulong.MaxValue;
        ulong e = lean_is_scalar(e0) ? lean_unbox(e0) : ulong.MaxValue;
        var so = Unsafe.As<StrObj>(s);
        byte[] str = so.m_data;
        ulong sz = (ulong)so.m_size - 1;
        if (b >= e || b >= sz) return lean_mk_string_unchecked(ReadOnlySpan<byte>.Empty, 0, 0);
        /* In the reference implementation if `b` is not pointing to a valid UTF8
           character start position, the result is the empty string. */
        if (!LeanUtf8.IsUtf8FirstByte(str[b])) return lean_mk_string_unchecked(ReadOnlySpan<byte>.Empty, 0, 0);
        if (e > sz) e = sz;
        /* In the reference implementation if `e` is not pointing to a valid UTF8
           character start position, it is assumed to be at the end. */
        if (e < sz && !LeanUtf8.IsUtf8FirstByte(str[e])) e = sz;
        ulong new_sz = e - b;
        return mk_string_from_bytes_unchecked_c(new ReadOnlySpan<byte>(str, (int)b, (int)new_sz));
    }

    public static Obj lean_string_utf8_prev(Obj s, Obj i0)
    {
        if (!lean_is_scalar(i0)) return StrRtUtil.NatPred(i0);
        ulong i = lean_unbox(i0);
        var so = Unsafe.As<StrObj>(s);
        ulong sz = (ulong)so.m_size - 1;
        if (i == 0) return lean_box(0);
        else if (i > sz) return lean_box(i - 1);
        i--;
        byte[] str = so.m_data;
        while (!LeanUtf8.IsUtf8FirstByte(str[i]))
        {
            if (i == 0) break; // C asserts `i > 0`
            i--;
        }
        return lean_box(i);
    }

    public static Obj lean_string_utf8_set(Obj s, Obj i0, uint c)
    {
        if (!lean_is_scalar(i0)) return s;
        ulong i = lean_unbox(i0);
        var so = Unsafe.As<StrObj>(s);
        ulong sz = (ulong)so.m_size - 1;
        if (i >= sz) return s;
        byte[] str = so.m_data;
        if (str[i] < 128 && c < 128)
        {
            Obj r = lean_string_ensure_exclusive(s);
            Unsafe.As<StrObj>(r).m_data[i] = (byte)c;
            return r;
        }
        if (!LeanUtf8.IsUtf8FirstByte(str[i])) return s;
        if (!lean_is_exclusive(s)) check_string_linearity(s);
        ulong len = (ulong)so.m_length;
        bool marked = lean_string_is_marked_linear(s);
        // new_s.replace(i, get_utf8_char_size_at(new_s, i), tmp)
        uint old_sz = LeanUtf8.GetUtf8FirstByteOpt(str[i]);
        if (old_sz == 0) old_sz = 1;
        ulong n_old = Math.Min(old_sz, sz - i);
        int n_new = LeanUtf8.ScalarSize(c);
        ulong new_size = sz - n_old + (ulong)n_new;
        var buf = new byte[new_size];
        Array.Copy(str, 0, buf, 0, (long)i);
        LeanUtf8.PushUnicodeScalar(buf, (long)i, c);
        Array.Copy(str, (long)(i + n_old), buf, (long)i + n_new, (long)(sz - i - n_old));
        lean_dec(s);
        Obj res = lean_mk_string_unchecked(buf, new_size, len);
        if (marked) lean_string_mark_linear_core(res);
        return res;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_string_utf8_at_end(Obj s, Obj i) =>
        (!lean_is_scalar(i) || lean_unbox(i) >= lean_string_size(s) - 1) ? (byte)1 : (byte)0;

    // ------------------------------------------------------------------
    // String.Slice

    public static ulong lean_slice_size(Obj slice)
    {
        Obj start = lean_ctor_get(slice, 1);
        Obj end = lean_ctor_get(slice, 2);
        return lean_unbox(end) - lean_unbox(start);
    }

    static ReadOnlySpan<byte> lean_slice_span(Obj slice)
    {
        Obj str = lean_ctor_get(slice, 0);
        ulong off = lean_unbox(lean_ctor_get(slice, 1));
        return new ReadOnlySpan<byte>(Unsafe.As<StrObj>(str).m_data, (int)off, (int)lean_slice_size(slice));
    }

    public static ulong lean_slice_hash(Obj s) => LeanHash.HashStr(lean_slice_span(s), 11);

    public static byte lean_slice_dec_lt(Obj s1, Obj s2) =>
        lean_slice_span(s1).SequenceCompareTo(lean_slice_span(s2)) < 0 ? (byte)1 : (byte)0;
}
