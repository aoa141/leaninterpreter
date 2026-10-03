// Port of runtime/utf8.{h,cpp} plus private helpers of the strings_arrays area.

using System.Numerics;
using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

/// <summary>Port of `runtime/utf8.cpp` (operates on UTF-8 byte spans).</summary>
public static class LeanUtf8
{
    /// <summary>`get_utf8_size`.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static uint GetUtf8Size(byte c)
    {
        if ((c & 0x80) == 0) return 1;
        else if ((c & 0xE0) == 0xC0) return 2;
        else if ((c & 0xF0) == 0xE0) return 3;
        else if ((c & 0xF8) == 0xF0) return 4;
        else if ((c & 0xFC) == 0xF8) return 5;
        else if ((c & 0xFE) == 0xFC) return 6;
        else if (c == 0xFF) return 1;
        else return 1; /* invalid */
    }

    /// <summary>`get_utf8_first_byte_opt`: number of bytes of the scalar starting with `c`, or 0 if `c` is not a first byte.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static uint GetUtf8FirstByteOpt(byte c)
    {
        if ((c & 0x80) == 0) return 1;
        else if ((c & 0xe0) == 0xc0) return 2;
        else if ((c & 0xf0) == 0xe0) return 3;
        else if ((c & 0xf8) == 0xf0) return 4;
        else return 0;
    }

    /// <summary>`is_utf8_first_byte` (object.cpp).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool IsUtf8FirstByte(byte c) =>
        (c & 0x80) == 0 || (c & 0xe0) == 0xc0 || (c & 0xf0) == 0xe0 || (c & 0xf8) == 0xf0;

    /// <summary>`lean_utf8_n_strlen` / `utf8_strlen(str, sz)`.</summary>
    public static ulong NStrlen(ReadOnlySpan<byte> str, ulong sz)
    {
        ulong r = 0;
        ulong i = 0;
        while (i < sz)
        {
            // C reads `str[i]`, which may be the terminating NUL (or beyond `sz`) for truncated sequences;
            // we only need the lead byte, which is always in range here.
            uint d = GetUtf8Size(str[(int)i]);
            r++;
            i += d;
        }
        return r;
    }

    /// <summary>`lean_utf8_strlen` (stops at the first NUL byte or at the end of the span).</summary>
    public static ulong Strlen(ReadOnlySpan<byte> str)
    {
        ulong r = 0;
        int i = 0;
        while (i < str.Length && str[i] != 0)
        {
            uint sz = GetUtf8Size(str[i]);
            r++;
            i += (int)sz;
        }
        return r;
    }

    /// <summary>`next_utf8(str, size, i)`.</summary>
    public static uint NextUtf8(ReadOnlySpan<byte> str, ulong size, ref ulong i)
    {
        uint c = str[(int)i];
        /* zero continuation (0 to 0x7F) */
        if ((c & 0x80) == 0)
        {
            i++;
            return c;
        }
        /* one continuation (0x80 to 0x7FF) */
        if ((c & 0xe0) == 0xc0 && i + 1 < size)
        {
            uint c1 = str[(int)i + 1];
            uint r = ((c & 0x1f) << 6) | (c1 & 0x3f);
            if (r >= 0x80)
            {
                i += 2;
                return r;
            }
        }
        /* two continuations (0x800 to 0xD7FF and 0xE000 to 0xFFFF) */
        if ((c & 0xf0) == 0xe0 && i + 2 < size)
        {
            uint c1 = str[(int)i + 1];
            uint c2 = str[(int)i + 2];
            uint r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
            if (r >= 0x800 && (r < 0xD800 || r > 0xDFFF))
            {
                i += 3;
                return r;
            }
        }
        /* three continuations (0x10000 to 0x10FFFF) */
        if ((c & 0xf8) == 0xf0 && i + 3 < size)
        {
            uint c1 = str[(int)i + 1];
            uint c2 = str[(int)i + 2];
            uint c3 = str[(int)i + 3];
            uint r = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
            if (r >= 0x10000 && r <= 0x10FFFF)
            {
                i += 4;
                return r;
            }
        }
        /* invalid UTF-8 encoded string */
        i++;
        return c;
    }

    /// <summary>`validate_utf8_one`.</summary>
    public static bool ValidateOne(ReadOnlySpan<byte> str, ulong size, ref ulong pos)
    {
        uint c = str[(int)pos];
        if ((c & 0x80) == 0)
        {
            pos++;
        }
        else if ((c & 0xe0) == 0xc0)
        {
            if (pos + 1 >= size) return false;
            uint c1 = str[(int)pos + 1];
            if ((c1 & 0xc0) != 0x80) return false;
            uint r = ((c & 0x1f) << 6) | (c1 & 0x3f);
            if (r < 0x80) return false;
            pos += 2;
        }
        else if ((c & 0xf0) == 0xe0)
        {
            if (pos + 2 >= size) return false;
            uint c1 = str[(int)pos + 1];
            uint c2 = str[(int)pos + 2];
            if ((c1 & 0xc0) != 0x80 || (c2 & 0xc0) != 0x80) return false;
            uint r = ((c & 0x0f) << 12) | ((c1 & 0x3f) << 6) | (c2 & 0x3f);
            if (r < 0x800 || (r >= 0xD800 && r <= 0xDFFF)) return false;
            pos += 3;
        }
        else if ((c & 0xf8) == 0xf0)
        {
            if (pos + 3 >= size) return false;
            uint c1 = str[(int)pos + 1];
            uint c2 = str[(int)pos + 2];
            uint c3 = str[(int)pos + 3];
            if ((c1 & 0xc0) != 0x80 || (c2 & 0xc0) != 0x80 || (c3 & 0xc0) != 0x80) return false;
            uint r = ((c & 0x07) << 18) | ((c1 & 0x3f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
            if (r < 0x10000 || r > 0x10FFFF) return false;
            pos += 4;
        }
        else
        {
            return false;
        }
        return true;
    }

    /// <summary>`validate_utf8`: `pos` is advanced to the first invalid position, `i` counts the valid code points.</summary>
    public static bool Validate(ReadOnlySpan<byte> str, ulong size, ref ulong pos, ref ulong i)
    {
        while (pos < size)
        {
            if (!ValidateOne(str, size, ref pos)) return false;
            i++;
        }
        return true;
    }

    /// <summary>Number of bytes `push_unicode_scalar` writes for `code`.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static int ScalarSize(uint code) => code < 0x80 ? 1 : code < 0x800 ? 2 : code < 0x10000 ? 3 : 4;

    /// <summary>`push_unicode_scalar(char * d, code)`: store `code` at `d[off..]`, return the number of bytes written.</summary>
    public static int PushUnicodeScalar(byte[] d, long off, uint code)
    {
        if (code < 0x80)
        {
            d[off] = (byte)code;
            return 1;
        }
        else if (code < 0x800)
        {
            d[off] = (byte)(((code >> 6) & 0x1F) | 0xC0);
            d[off + 1] = (byte)((code & 0x3F) | 0x80);
            return 2;
        }
        else if (code < 0x10000)
        {
            d[off] = (byte)(((code >> 12) & 0x0F) | 0xE0);
            d[off + 1] = (byte)(((code >> 6) & 0x3F) | 0x80);
            d[off + 2] = (byte)((code & 0x3F) | 0x80);
            return 3;
        }
        else
        {
            d[off] = (byte)(((code >> 18) & 0x07) | 0xF0);
            d[off + 1] = (byte)(((code >> 12) & 0x3F) | 0x80);
            d[off + 2] = (byte)(((code >> 6) & 0x3F) | 0x80);
            d[off + 3] = (byte)((code & 0x3F) | 0x80);
            return 4;
        }
    }
}

/// <summary>Private helpers of the strings_arrays area (things owned by other areas are re-implemented here).</summary>
internal static class StrRtUtil
{
    /// <summary>`should_abort_on_nonlinearity()`.</summary>
    internal static bool AbortOnNonlinearity => LeanContext.Proc.GetEnv("LEAN_ABORT_ON_NONLINEAR") != null;

    /// <summary>C pointer equality for `lean_object*` values (tagged scalars compare by value).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static bool PtrEq(Obj a, Obj b)
    {
        if (ReferenceEquals(a, b)) return true;
        return a.m_tag == LeanRt.LeanBoxTag && b.m_tag == LeanRt.LeanBoxTag &&
               Unsafe.As<Box>(a).m_value == Unsafe.As<Box>(b).m_value;
    }

    /// <summary>`lean_nat_add(a, lean_box(1))` for a borrowed `a`.</summary>
    internal static Obj NatSucc(Obj a) => LeanRt.lean_big_to_nat(LeanRt.lean_nat_to_big(a) + BigInteger.One);

    /// <summary>`lean_nat_sub(a, lean_box(1))` for a borrowed `a` (truncated at 0).</summary>
    internal static Obj NatPred(Obj a)
    {
        var v = LeanRt.lean_nat_to_big(a);
        return v.IsZero ? LeanRt.lean_box(0) : LeanRt.lean_big_to_nat(v - BigInteger.One);
    }

    /// <summary>`lean_nat_eq` (both borrowed).</summary>
    internal static bool NatEq(Obj a, Obj b)
    {
        bool sa = LeanRt.lean_is_scalar(a), sb = LeanRt.lean_is_scalar(b);
        if (sa && sb) return LeanRt.lean_unbox(a) == LeanRt.lean_unbox(b);
        if (sa != sb) return false;
        return Unsafe.As<MpzObj>(a).m_value == Unsafe.As<MpzObj>(b).m_value;
    }

    /// <summary>`lean_box_uint32` on a 64-bit platform.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static Obj BoxUInt32(uint v) => LeanRt.lean_box(v);

    /// <summary>`lean_unbox_uint32` on a 64-bit platform.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static uint UnboxUInt32(Obj o) => (uint)LeanRt.lean_unbox(o);
}
