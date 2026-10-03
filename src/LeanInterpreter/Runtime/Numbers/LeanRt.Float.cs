// Port of the Float / Float32 sections of `lean.h` and `runtime/object.cpp`, the boxing primitives
// for UInt32/UInt64/USize/Float/Float32, the C math functions used as externs by `Float` and
// `Float32`, and `FloatArray`.

using System.Numerics;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;

namespace LeanInterpreter.Runtime;

internal static class FloatInternal
{
    const ulong QuietNaN64 = 0x7ff8000000000000UL;
    const uint QuietNaN32 = 0x7fc00000U;

    /// <summary>`std::numeric_limits&lt;double&gt;::quiet_NaN()` (positive quiet NaN, unlike .NET's `double.NaN`).</summary>
    public static readonly double NaN64 = BitConverter.UInt64BitsToDouble(QuietNaN64);
    public static readonly float NaN32 = BitConverter.UInt32BitsToSingle(QuietNaN32);

    static readonly BigInteger s_million = new BigInteger(1000000);

    /// <summary>
    /// Exactly `printf("%f", a)` (i.e. `std::to_string(double)`): six fractional digits, exact decimal
    /// expansion of the binary value, round-half-to-even. `a` must be finite.
    /// </summary>
    public static string FormatF6(double a)
    {
        ulong bits = BitConverter.DoubleToUInt64Bits(a);
        bool neg = (bits >> 63) != 0;
        int bexp = (int)((bits >> 52) & 0x7FF);
        ulong frac = bits & 0xFFFFFFFFFFFFFUL;
        BigInteger m;
        int e;
        if (bexp == 0) { m = frac; e = -1074; }
        else { m = frac | (1UL << 52); e = bexp - 1075; }
        // value = m * 2^e; compute N = round_half_even(value * 10^6)
        BigInteger n;
        if (m.IsZero) n = BigInteger.Zero;
        else if (e >= 0) n = (m << e) * s_million;
        else
        {
            BigInteger num = m * s_million;
            BigInteger den = BigInteger.One << -e;
            n = BigInteger.DivRem(num, den, out BigInteger r);
            int c = (r << 1).CompareTo(den);
            if (c > 0 || (c == 0 && !n.IsEven)) n += 1;
        }
        BigInteger ip = BigInteger.DivRem(n, s_million, out BigInteger fp);
        var sb = new StringBuilder();
        if (neg) sb.Append('-');
        sb.Append(ip.ToString(System.Globalization.CultureInfo.InvariantCulture));
        sb.Append('.');
        sb.Append(((int)fp).ToString("D6", System.Globalization.CultureInfo.InvariantCulture));
        return sb.ToString();
    }

    public static string ToStringC(double a)
    {
        if (double.IsNaN(a)) return "NaN";
        if (double.IsPositiveInfinity(a)) return "inf";
        if (double.IsNegativeInfinity(a)) return "-inf";
        return FormatF6(a);
    }

    /// <summary>C `frexp` for doubles.</summary>
    public static double Frexp(double a, out int exp)
    {
        exp = 0;
        if (a == 0 || !double.IsFinite(a)) return a;
        ulong bits = BitConverter.DoubleToUInt64Bits(a);
        int bexp = (int)((bits >> 52) & 0x7FF);
        if (bexp == 0)
        {
            // subnormal: normalize first
            a *= 18014398509481984.0; // 2^54
            bits = BitConverter.DoubleToUInt64Bits(a);
            bexp = (int)((bits >> 52) & 0x7FF);
            exp = -54;
        }
        exp += bexp - 1022;
        bits = (bits & ~(0x7FFUL << 52)) | (1022UL << 52);
        return BitConverter.UInt64BitsToDouble(bits);
    }

    /// <summary>C `frexpf`.</summary>
    public static float Frexp(float a, out int exp)
    {
        exp = 0;
        if (a == 0 || !float.IsFinite(a)) return a;
        uint bits = BitConverter.SingleToUInt32Bits(a);
        int bexp = (int)((bits >> 23) & 0xFF);
        if (bexp == 0)
        {
            a *= 33554432.0f; // 2^25
            bits = BitConverter.SingleToUInt32Bits(a);
            bexp = (int)((bits >> 23) & 0xFF);
            exp = -25;
        }
        exp += bexp - 126;
        bits = (bits & ~(0xFFU << 23)) | (126U << 23);
        return BitConverter.UInt32BitsToSingle(bits);
    }

    /// <summary>Correctly rounded `(double)v` for unsigned 64-bit values.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static double U64ToDouble(ulong v)
    {
        if (v <= long.MaxValue) return (double)(long)v;
        // halve with a sticky bit, convert (exactly rounded once), then double
        return (double)(long)((v >> 1) | (v & 1)) * 2.0;
    }

    /// <summary>Correctly rounded `(float)v` for unsigned 64-bit values (avoids double rounding).</summary>
    public static float U64ToFloat(ulong v)
    {
        if (v < (1UL << 53)) return (float)(double)v; // exact in double: single rounding
        int s = 64 - BitOperations.LeadingZeroCount(v) - 53;
        ulong mask = (1UL << s) - 1;
        ulong w = (v >> s) | ((v & mask) != 0 ? 1UL : 0UL);
        return MathF.ScaleB((float)(double)w, s);
    }

    /// <summary>Correctly rounded `(float)v` for signed 64-bit values.</summary>
    public static float I64ToFloat(long v)
    {
        if (v >= 0) return U64ToFloat((ulong)v);
        return -U64ToFloat(0UL - (ulong)v);
    }
}

public static unsafe partial class LeanRt
{
    // ------------------------------------------------------------------
    // Boxing primitives

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_box_uint32(uint v) => lean_box(v);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static uint lean_unbox_uint32(Obj o) => (uint)lean_unbox(o);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_box_uint64(ulong v)
    {
        var r = lean_alloc_ctor(0, 0, 8);
        lean_ctor_set_uint64_s(r, 0, v);
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong lean_unbox_uint64(Obj o) => lean_ctor_get_uint64_s(o, 0);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_box_usize(ulong v)
    {
        var r = lean_alloc_ctor(0, 0, 8);
        lean_ctor_set_uint64_s(r, 0, v);
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong lean_unbox_usize(Obj o) => lean_ctor_get_uint64_s(o, 0);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_box_float(double v)
    {
        var r = lean_alloc_ctor(0, 0, 8);
        lean_ctor_set_float_s(r, 0, v);
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static double lean_unbox_float(Obj o) => lean_ctor_get_float_s(o, 0);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_box_float32(float v)
    {
        var r = lean_alloc_ctor(0, 0, 4);
        lean_ctor_set_float32_s(r, 0, v);
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static float lean_unbox_float32(Obj o) => lean_ctor_get_float32_s(o, 0);

    // ------------------------------------------------------------------
    // Float (object.cpp)

    public static Obj lean_float_to_string(double a) => lean_mk_string(FloatInternal.ToStringC(a));

    public static double lean_float_scaleb(double a, Obj b)
    {
        if (lean_is_scalar(b)) return Math.ScaleB(a, lean_scalar_to_int(b));
        if (a == 0 || Unsafe.As<MpzObj>(b).m_value.Sign < 0) return 0;
        return a * double.PositiveInfinity;
    }

    public static byte lean_float_isnan(double a) => double.IsNaN(a) ? (byte)1 : (byte)0;
    public static byte lean_float_isfinite(double a) => double.IsFinite(a) ? (byte)1 : (byte)0;
    public static byte lean_float_isinf(double a) => double.IsInfinity(a) ? (byte)1 : (byte)0;

    public static Obj lean_float_frexp(double a)
    {
        var r = lean_alloc_ctor(0, 2, 0);
        double m = FloatInternal.Frexp(a, out int exp);
        lean_ctor_set(r, 0, lean_box_float(m));
        lean_ctor_set(r, 1, double.IsFinite(a) ? lean_int_to_int(exp) : lean_box(0));
        return r;
    }

    public static double lean_float_of_bits(ulong u)
    {
        double ret = BitConverter.UInt64BitsToDouble(u);
        if (double.IsNaN(ret)) return FloatInternal.NaN64;
        return ret;
    }

    public static ulong lean_float_to_bits(double d)
    {
        if (double.IsNaN(d)) return 0x7ff8000000000000UL;
        return BitConverter.DoubleToUInt64Bits(d);
    }

    // ------------------------------------------------------------------
    // Float32 (object.cpp)

    public static Obj lean_float32_to_string(float a) => lean_mk_string(FloatInternal.ToStringC((double)a));

    public static float lean_float32_scaleb(float a, Obj b)
    {
        if (lean_is_scalar(b)) return MathF.ScaleB(a, lean_scalar_to_int(b));
        if (a == 0 || Unsafe.As<MpzObj>(b).m_value.Sign < 0) return 0;
        return (float)(a * double.PositiveInfinity);
    }

    public static byte lean_float32_isnan(float a) => float.IsNaN(a) ? (byte)1 : (byte)0;
    public static byte lean_float32_isfinite(float a) => float.IsFinite(a) ? (byte)1 : (byte)0;
    public static byte lean_float32_isinf(float a) => float.IsInfinity(a) ? (byte)1 : (byte)0;

    public static Obj lean_float32_frexp(float a)
    {
        var r = lean_alloc_ctor(0, 2, 0);
        float m = FloatInternal.Frexp(a, out int exp);
        lean_ctor_set(r, 0, lean_box_float32(m));
        lean_ctor_set(r, 1, float.IsFinite(a) ? lean_int_to_int(exp) : lean_box(0));
        return r;
    }

    public static float lean_float32_of_bits(uint u)
    {
        float ret = BitConverter.UInt32BitsToSingle(u);
        if (float.IsNaN(ret)) ret = FloatInternal.NaN32;
        return ret;
    }

    public static uint lean_float32_to_bits(float d)
    {
        if (float.IsNaN(d)) return 0x7fc00000U;
        return BitConverter.SingleToUInt32Bits(d);
    }

    // ------------------------------------------------------------------
    // Float primitives (lean.h). Out-of-range conversions saturate; NaN converts to 0.

    public static byte lean_float_to_uint8(double a) => 0.0 <= a ? (a < 256.0 ? (byte)a : byte.MaxValue) : (byte)0;
    public static ushort lean_float_to_uint16(double a) => 0.0 <= a ? (a < 65536.0 ? (ushort)a : ushort.MaxValue) : (ushort)0;
    public static uint lean_float_to_uint32(double a) => 0.0 <= a ? (a < 4294967296.0 ? (uint)a : uint.MaxValue) : 0U;
    public static ulong lean_float_to_uint64(double a) => 0.0 <= a ? (a < 18446744073709551616.0 ? (ulong)a : ulong.MaxValue) : 0UL;
    public static ulong lean_float_to_usize(double a) => lean_float_to_uint64(a);

    public static byte lean_float_to_int8(double a)
    {
        sbyte result;
        if (double.IsNaN(a)) result = 0;
        else result = -129.0 < a ? (a < 128.0 ? (sbyte)a : sbyte.MaxValue) : sbyte.MinValue;
        return unchecked((byte)result);
    }

    public static ushort lean_float_to_int16(double a)
    {
        short result;
        if (double.IsNaN(a)) result = 0;
        else result = -32769.0 < a ? (a < 32768.0 ? (short)a : short.MaxValue) : short.MinValue;
        return unchecked((ushort)result);
    }

    public static uint lean_float_to_int32(double a)
    {
        int result;
        if (double.IsNaN(a)) result = 0;
        else result = -2147483649.0 < a ? (a < 2147483648.0 ? (int)a : int.MaxValue) : int.MinValue;
        return unchecked((uint)result);
    }

    public static ulong lean_float_to_int64(double a)
    {
        long result;
        if (double.IsNaN(a)) result = 0;
        else result = -9223372036854775809.0 < a ? (a < 9223372036854775808.0 ? (long)a : long.MaxValue) : long.MinValue;
        return unchecked((ulong)result);
    }

    public static ulong lean_float_to_isize(double a) => lean_float_to_int64(a);

    public static double lean_float_add(double a, double b) => a + b;
    public static double lean_float_sub(double a, double b) => a - b;
    public static double lean_float_mul(double a, double b) => a * b;
    public static double lean_float_div(double a, double b) => a / b;
    public static double lean_float_negate(double a) => -a;
    public static byte lean_float_beq(double a, double b) => a == b ? (byte)1 : (byte)0;
    public static byte lean_float_decLe(double a, double b) => a <= b ? (byte)1 : (byte)0;
    public static byte lean_float_decLt(double a, double b) => a < b ? (byte)1 : (byte)0;

    public static double lean_uint8_to_float(byte a) => a;
    public static double lean_uint16_to_float(ushort a) => a;
    public static double lean_uint32_to_float(uint a) => a;
    public static double lean_uint64_to_float(ulong a) => FloatInternal.U64ToDouble(a);
    public static double lean_usize_to_float(ulong a) => FloatInternal.U64ToDouble(a);
    public static double lean_int8_to_float(byte a) => unchecked((sbyte)a);
    public static double lean_int16_to_float(ushort a) => unchecked((short)a);
    public static double lean_int32_to_float(uint a) => unchecked((int)a);
    public static double lean_int64_to_float(ulong a) => unchecked((long)a);
    public static double lean_isize_to_float(ulong a) => unchecked((long)a);

    // IEEE 754-2019 minimum/maximum (fallback implementation of lean.h)
    public static double lean_float_minimum(double a, double b)
    {
        if (double.IsNaN(a) || double.IsNaN(b)) return a + b;
        if (a == b) return double.IsNegative(a) ? a : b;
        return a < b ? a : b;
    }

    public static double lean_float_minimum_number(double a, double b)
    {
        if (double.IsNaN(a) || double.IsNaN(b))
        {
            if (double.IsNaN(a) && double.IsNaN(b)) return a + b;
            return double.IsNaN(a) ? b : a;
        }
        if (a == b) return double.IsNegative(a) ? a : b;
        return a < b ? a : b;
    }

    public static double lean_float_maximum(double a, double b)
    {
        if (double.IsNaN(a) || double.IsNaN(b)) return a + b;
        if (a == b) return double.IsNegative(a) ? b : a;
        return a > b ? a : b;
    }

    public static double lean_float_maximum_number(double a, double b)
    {
        if (double.IsNaN(a) || double.IsNaN(b))
        {
            if (double.IsNaN(a) && double.IsNaN(b)) return a + b;
            return double.IsNaN(a) ? b : a;
        }
        if (a == b) return double.IsNegative(a) ? b : a;
        return a > b ? a : b;
    }

    // ------------------------------------------------------------------
    // Float32 primitives (lean.h)

    public static byte lean_float32_to_uint8(float a) => 0.0 <= a ? (a < 256.0 ? (byte)a : byte.MaxValue) : (byte)0;
    public static ushort lean_float32_to_uint16(float a) => 0.0 <= a ? (a < 65536.0 ? (ushort)a : ushort.MaxValue) : (ushort)0;
    public static uint lean_float32_to_uint32(float a) => 0.0 <= a ? (a < 4294967296.0 ? (uint)a : uint.MaxValue) : 0U;
    public static ulong lean_float32_to_uint64(float a) => 0.0 <= a ? (a < 18446744073709551616.0 ? (ulong)a : ulong.MaxValue) : 0UL;
    public static ulong lean_float32_to_usize(float a) => lean_float32_to_uint64(a);

    public static byte lean_float32_to_int8(float a)
    {
        sbyte result;
        if (float.IsNaN(a)) result = 0;
        else result = -129.0 < a ? (a < 128.0 ? (sbyte)a : sbyte.MaxValue) : sbyte.MinValue;
        return unchecked((byte)result);
    }

    public static ushort lean_float32_to_int16(float a)
    {
        short result;
        if (float.IsNaN(a)) result = 0;
        else result = -32769.0 < a ? (a < 32768.0 ? (short)a : short.MaxValue) : short.MinValue;
        return unchecked((ushort)result);
    }

    public static uint lean_float32_to_int32(float a)
    {
        int result;
        if (float.IsNaN(a)) result = 0;
        else result = -2147483649.0 < a ? (a < 2147483648.0 ? (int)a : int.MaxValue) : int.MinValue;
        return unchecked((uint)result);
    }

    public static ulong lean_float32_to_int64(float a)
    {
        long result;
        if (float.IsNaN(a)) result = 0;
        else result = -9223372036854775809.0 < a ? (a < 9223372036854775808.0 ? (long)a : long.MaxValue) : long.MinValue;
        return unchecked((ulong)result);
    }

    public static ulong lean_float32_to_isize(float a) => lean_float32_to_int64(a);

    public static float lean_float32_add(float a, float b) => a + b;
    public static float lean_float32_sub(float a, float b) => a - b;
    public static float lean_float32_mul(float a, float b) => a * b;
    public static float lean_float32_div(float a, float b) => a / b;
    public static float lean_float32_negate(float a) => -a;
    public static byte lean_float32_beq(float a, float b) => a == b ? (byte)1 : (byte)0;
    public static byte lean_float32_decLe(float a, float b) => a <= b ? (byte)1 : (byte)0;
    public static byte lean_float32_decLt(float a, float b) => a < b ? (byte)1 : (byte)0;

    public static float lean_uint8_to_float32(byte a) => a;
    public static float lean_uint16_to_float32(ushort a) => a;
    public static float lean_uint32_to_float32(uint a) => (float)(double)a; // exact in double: single rounding
    public static float lean_uint64_to_float32(ulong a) => FloatInternal.U64ToFloat(a);
    public static float lean_usize_to_float32(ulong a) => FloatInternal.U64ToFloat(a);
    public static float lean_int8_to_float32(byte a) => unchecked((sbyte)a);
    public static float lean_int16_to_float32(ushort a) => unchecked((short)a);
    public static float lean_int32_to_float32(uint a) => (float)(double)unchecked((int)a);
    public static float lean_int64_to_float32(ulong a) => FloatInternal.I64ToFloat(unchecked((long)a));
    public static float lean_isize_to_float32(ulong a) => FloatInternal.I64ToFloat(unchecked((long)a));
    public static float lean_float_to_float32(double a) => (float)a;
    public static double lean_float32_to_float(float a) => a;

    public static float lean_float32_minimum(float a, float b)
    {
        if (float.IsNaN(a) || float.IsNaN(b)) return a + b;
        if (a == b) return float.IsNegative(a) ? a : b;
        return a < b ? a : b;
    }

    public static float lean_float32_minimum_number(float a, float b)
    {
        if (float.IsNaN(a) || float.IsNaN(b))
        {
            if (float.IsNaN(a) && float.IsNaN(b)) return a + b;
            return float.IsNaN(a) ? b : a;
        }
        if (a == b) return float.IsNegative(a) ? a : b;
        return a < b ? a : b;
    }

    public static float lean_float32_maximum(float a, float b)
    {
        if (float.IsNaN(a) || float.IsNaN(b)) return a + b;
        if (a == b) return float.IsNegative(a) ? b : a;
        return a > b ? a : b;
    }

    public static float lean_float32_maximum_number(float a, float b)
    {
        if (float.IsNaN(a) || float.IsNaN(b))
        {
            if (float.IsNaN(a) && float.IsNaN(b)) return a + b;
            return float.IsNaN(a) ? b : a;
        }
        if (a == b) return float.IsNegative(a) ? b : a;
        return a > b ? a : b;
    }

    // ------------------------------------------------------------------
    // C math library functions used as `@[extern]` implementations of `Float`/`Float32`.
    // .NET's Math/MathF call into the platform C runtime for these.

    public static double sin(double x) => Math.Sin(x);
    public static double cos(double x) => Math.Cos(x);
    public static double tan(double x) => Math.Tan(x);
    public static double asin(double x) => Math.Asin(x);
    public static double acos(double x) => Math.Acos(x);
    public static double atan(double x) => Math.Atan(x);
    public static double exp(double x) => Math.Exp(x);
    public static double log(double x) => Math.Log(x);
    public static double pow(double x, double y) => Math.Pow(x, y);
    public static double sqrt(double x) => Math.Sqrt(x);
    public static double cbrt(double x) => Math.Cbrt(x);
    public static double ceil(double x) => Math.Ceiling(x);
    public static double floor(double x) => Math.Floor(x);
    /// <summary>C `round`: halfway cases away from zero.</summary>
    public static double round(double x) => Math.Round(x, MidpointRounding.AwayFromZero);
    public static double fabs(double x) => Math.Abs(x);
    public static double fma(double x, double y, double z) => Math.FusedMultiplyAdd(x, y, z);

    public static float sinf(float x) => MathF.Sin(x);
    public static float cosf(float x) => MathF.Cos(x);
    public static float tanf(float x) => MathF.Tan(x);
    public static float asinf(float x) => MathF.Asin(x);
    public static float acosf(float x) => MathF.Acos(x);
    public static float atanf(float x) => MathF.Atan(x);
    public static float expf(float x) => MathF.Exp(x);
    public static float logf(float x) => MathF.Log(x);
    public static float powf(float x, float y) => MathF.Pow(x, y);
    public static float sqrtf(float x) => MathF.Sqrt(x);
    public static float cbrtf(float x) => MathF.Cbrt(x);
    public static float ceilf(float x) => MathF.Ceiling(x);
    public static float floorf(float x) => MathF.Floor(x);
    public static float roundf(float x) => MathF.Round(x, MidpointRounding.AwayFromZero);
    public static float fabsf(float x) => MathF.Abs(x);
    public static float fmaf(float x, float y, float z) => MathF.FusedMultiplyAdd(x, y, z);

    // ------------------------------------------------------------------
    // FloatArray (lean.h / object.cpp). Elements are stored little-endian in `SArrayObj.m_data`.

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Span<double> FloatArraySpan(Obj a) => MemoryMarshal.Cast<byte, double>(Unsafe.As<SArrayObj>(a).m_data.AsSpan());

    /// <summary>`lean_copy_sarray` (private copy for the numbers area). Consumes `a`.</summary>
    static Obj NumbersCopySArray(Obj a, ulong cap)
    {
        var src = Unsafe.As<SArrayObj>(a);
        uint esz = lean_sarray_elem_size(a);
        ulong sz = (ulong)src.m_size;
        var r = lean_alloc_sarray(esz, sz, cap);
        if ((a.m_other & LEAN_LINEAR_MARK_MASK) != 0) r.m_other |= LEAN_LINEAR_MARK_MASK;
        Array.Copy(src.m_data, Unsafe.As<SArrayObj>(r).m_data, (long)(esz * sz));
        lean_dec(a);
        return r;
    }

    static Obj NumbersCopySArrayNonlinear(Obj a, ulong cap)
    {
        if ((a.m_other & LEAN_LINEAR_MARK_MASK) != 0 && LeanContext.Proc.GetEnv("LEAN_ABORT_ON_NONLINEAR") != null)
            throw lean_internal_panic("scalar array marked by `markLinear` was used non-linearly");
        return NumbersCopySArray(a, cap);
    }

    static Obj NumbersSArrayEnsureExclusive(Obj a)
    {
        if (lean_is_exclusive(a)) return a;
        return NumbersCopySArrayNonlinear(a, lean_sarray_capacity(a));
    }

    static Obj NumbersSArrayEnsureCapacity(Obj a, ulong min_cap, bool exact)
    {
        ulong cap = lean_sarray_capacity(a);
        if (min_cap <= cap) return a;
        if (lean_is_exclusive(a)) return NumbersCopySArray(a, exact ? min_cap : min_cap * 2);
        return NumbersCopySArrayNonlinear(a, exact ? min_cap : min_cap * 2);
    }

    /// <summary>`FloatArray.mk` (consumes `a`, an `Array Float` of boxed floats).</summary>
    public static Obj lean_float_array_mk(Obj a)
    {
        ulong sz = lean_array_size(a);
        var r = lean_alloc_sarray(8, sz, sz);
        var src = lean_array_cptr(a);
        var dest = FloatArraySpan(r);
        for (ulong i = 0; i < sz; i++) dest[(int)i] = lean_unbox_float(src[i]);
        lean_dec(a);
        return r;
    }

    /// <summary>`FloatArray.data` (consumes `a`).</summary>
    public static Obj lean_float_array_data(Obj a)
    {
        ulong sz = lean_sarray_size(a);
        var r = lean_alloc_array(sz, sz);
        var src = FloatArraySpan(a);
        var dest = lean_array_cptr(r);
        for (ulong i = 0; i < sz; i++) dest[i] = lean_box_float(src[(int)i]);
        lean_dec(a);
        return r;
    }

    public static Obj lean_float_array_size(Obj a) => lean_box(lean_sarray_size(a));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static double lean_float_array_uget(Obj a, ulong i) => FloatArraySpan(a)[(int)i];

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static double lean_float_array_fget(Obj a, Obj i) => lean_float_array_uget(a, lean_unbox(i));

    public static double lean_float_array_get(Obj a, Obj i)
    {
        if (lean_is_scalar(i))
        {
            ulong idx = lean_unbox(i);
            return idx < lean_sarray_size(a) ? lean_float_array_uget(a, idx) : 0.0;
        }
        /* The index must be out of bounds. Otherwise we would be out of memory. */
        return 0.0;
    }

    /// <summary>`FloatArray.push` (consumes `a`).</summary>
    public static Obj lean_float_array_push(Obj a, double d)
    {
        var r = NumbersSArrayEnsureExclusive(NumbersSArrayEnsureCapacity(a, lean_sarray_size(a) + 1, false));
        var s = Unsafe.As<SArrayObj>(r);
        FloatArraySpan(r)[(int)s.m_size] = d;
        s.m_size++;
        return r;
    }

    /// <summary>`FloatArray.uset` (consumes `a`).</summary>
    public static Obj lean_float_array_uset(Obj a, ulong i, double d)
    {
        var r = NumbersSArrayEnsureExclusive(a);
        FloatArraySpan(r)[(int)i] = d;
        return r;
    }

    public static Obj lean_float_array_fset(Obj a, Obj i, double d) => lean_float_array_uset(a, lean_unbox(i), d);

    public static Obj lean_float_array_set(Obj a, Obj i, double d)
    {
        if (!lean_is_scalar(i)) return a;
        ulong idx = lean_unbox(i);
        if (idx >= lean_sarray_size(a)) return a;
        return lean_float_array_uset(a, idx, d);
    }
}
