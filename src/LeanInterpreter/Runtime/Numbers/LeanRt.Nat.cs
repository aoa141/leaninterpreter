// Port of the natural number and integer sections of `lean.h` and the corresponding out-of-line
// functions of `runtime/object.cpp` (`lean_nat_big_*`, `lean_int_big_*`, ...). Big values are
// `MpzObj` holding a `System.Numerics.BigInteger`; semantics follow `runtime/mpz.cpp` (GMP build).
//
// Representation invariants (as in C, 64-bit):
//  * a `Nat` <= LEAN_MAX_SMALL_NAT (2^63-1) is always a `Box`, otherwise an `MpzObj`;
//  * an `Int` in [INT_MIN, INT_MAX] (32-bit) is always `lean_box((uint)(int)v)`, otherwise an `MpzObj`.

using System.Numerics;
using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

/// <summary>Private helpers of the numbers area.</summary>
internal static class NumbersInternal
{
    /// <summary>`v mod 2^64` (two's complement for negative values), i.e. `mpz::mod64`.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong Mod64(BigInteger v) => (ulong)(v & ulong.MaxValue);

    public static BigInteger MpzValue(Obj o) => Unsafe.As<MpzObj>(o).m_value;

    /// <summary>`mpz_to_nat`: normalize a non-negative big integer to a `Nat` object.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj ToNat(BigInteger v) => LeanRt.lean_big_to_nat(v);

    /// <summary>`mpz_to_int`: normalize a big integer to an `Int` object.</summary>
    public static Obj ToInt(BigInteger v)
    {
        if (v < int.MinValue || v > int.MaxValue) return LeanRt.lean_alloc_mpz(v);
        return LeanRt.lean_box((uint)(int)v);
    }

    /// <summary>Value of an `Int` object as a big integer.</summary>
    public static BigInteger IntToBig(Obj o) =>
        LeanRt.lean_is_scalar(o) ? new BigInteger(LeanRt.lean_scalar_to_int(o)) : MpzValue(o);

    /// <summary>`mpz::ediv` (Euclidean division derived from truncated division).</summary>
    public static BigInteger EDiv(BigInteger n, BigInteger d)
    {
        BigInteger q = BigInteger.DivRem(n, d, out BigInteger r);
        if (r.Sign < 0)
            q = d.Sign > 0 ? q - 1 : q + 1;
        return q;
    }

    /// <summary>`mpz::emod`.</summary>
    public static BigInteger EMod(BigInteger n, BigInteger d)
    {
        BigInteger r = BigInteger.Remainder(n, d);
        if (r.Sign < 0)
            r = d.Sign > 0 ? r + d : r - d;
        return r;
    }

    /// <summary>`mpz::log2` (0 for non-positive values).</summary>
    public static ulong Log2(BigInteger v) => v.Sign <= 0 ? 0 : (ulong)(v.GetBitLength() - 1);
}

public static unsafe partial class LeanRt
{
    // ------------------------------------------------------------------
    // Natural numbers: conversions

    public static Obj lean_big_usize_to_nat(ulong n) => n <= LEAN_MAX_SMALL_NAT ? lean_box(n) : lean_alloc_mpz(n);

    public static Obj lean_big_uint64_to_nat(ulong n) => n <= LEAN_MAX_SMALL_NAT ? lean_box(n) : lean_alloc_mpz(n);

    // ------------------------------------------------------------------
    // Natural numbers: out-of-line (big) cases

    public static Obj lean_nat_big_succ(Obj a) => lean_alloc_mpz(NumbersInternal.MpzValue(a) + 1);

    public static Obj lean_nat_big_add(Obj a1, Obj a2) =>
        NumbersInternal.ToNat(lean_nat_to_big(a1) + lean_nat_to_big(a2));

    public static Obj lean_nat_big_sub(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1))
            return lean_box(0);
        else if (lean_is_scalar(a2))
            return NumbersInternal.ToNat(NumbersInternal.MpzValue(a1) - lean_unbox(a2));
        else
        {
            BigInteger v1 = NumbersInternal.MpzValue(a1), v2 = NumbersInternal.MpzValue(a2);
            if (v1 < v2) return lean_box(0);
            return NumbersInternal.ToNat(v1 - v2);
        }
    }

    public static Obj lean_nat_big_mul(Obj a1, Obj a2) =>
        NumbersInternal.ToNat(lean_nat_to_big(a1) * lean_nat_to_big(a2));

    public static Obj lean_nat_overflow_mul(ulong a1, ulong a2) =>
        NumbersInternal.ToNat(new BigInteger(a1) * a2);

    public static Obj lean_nat_big_div(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1))
            return lean_box(0);
        else if (lean_is_scalar(a2))
        {
            ulong n2 = lean_unbox(a2);
            return n2 == 0 ? a2 : NumbersInternal.ToNat(NumbersInternal.MpzValue(a1) / n2);
        }
        else
            return NumbersInternal.ToNat(NumbersInternal.MpzValue(a1) / NumbersInternal.MpzValue(a2));
    }

    public static Obj lean_nat_big_div_exact(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1))
            return lean_box(0);
        else if (lean_is_scalar(a2))
        {
            ulong n2 = lean_unbox(a2);
            if (n2 == 0) return lean_box(0); // precondition violated; avoid a DivideByZeroException
            return NumbersInternal.ToNat(NumbersInternal.MpzValue(a1) / n2);
        }
        else
            return NumbersInternal.ToNat(NumbersInternal.MpzValue(a1) / NumbersInternal.MpzValue(a2));
    }

    public static Obj lean_nat_big_mod(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1))
            return a1;
        else if (lean_is_scalar(a2))
        {
            ulong n2 = lean_unbox(a2);
            if (n2 == 0)
            {
                lean_inc(a1);
                return a1;
            }
            return NumbersInternal.ToNat(NumbersInternal.MpzValue(a1) % n2);
        }
        else
            return NumbersInternal.ToNat(NumbersInternal.MpzValue(a1) % NumbersInternal.MpzValue(a2));
    }

    public static bool lean_nat_big_eq(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) || lean_is_scalar(a2)) return false;
        return NumbersInternal.MpzValue(a1) == NumbersInternal.MpzValue(a2);
    }

    public static bool lean_nat_big_le(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1)) return true;
        if (lean_is_scalar(a2)) return false;
        return NumbersInternal.MpzValue(a1) <= NumbersInternal.MpzValue(a2);
    }

    public static bool lean_nat_big_lt(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1)) return true;
        if (lean_is_scalar(a2)) return false;
        return NumbersInternal.MpzValue(a1) < NumbersInternal.MpzValue(a2);
    }

    public static Obj lean_nat_big_land(Obj a1, Obj a2) =>
        NumbersInternal.ToNat(lean_nat_to_big(a1) & lean_nat_to_big(a2));

    public static Obj lean_nat_big_lor(Obj a1, Obj a2) =>
        NumbersInternal.ToNat(lean_nat_to_big(a1) | lean_nat_to_big(a2));

    public static Obj lean_nat_big_xor(Obj a1, Obj a2) =>
        NumbersInternal.ToNat(lean_nat_to_big(a1) ^ lean_nat_to_big(a2));

    // ------------------------------------------------------------------
    // Natural numbers: lean.h fast paths (all arguments borrowed)

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_succ(Obj a)
    {
        if (lean_is_scalar(a)) return lean_usize_to_nat(lean_unbox(a) + 1);
        return lean_nat_big_succ(a);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_add(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
            return lean_usize_to_nat(lean_unbox(a1) + lean_unbox(a2));
        return lean_nat_big_add(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_sub(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            ulong n1 = lean_unbox(a1), n2 = lean_unbox(a2);
            return n1 < n2 ? lean_box(0) : lean_box(n1 - n2);
        }
        return lean_nat_big_sub(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_mul(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            ulong n1 = lean_unbox(a1);
            if (n1 == 0) return a1;
            ulong n2 = lean_unbox(a2);
            ulong hi = Math.BigMul(n1, n2, out ulong r);
            if (hi == 0 && r <= LEAN_MAX_SMALL_NAT) return lean_box(r);
            return lean_nat_overflow_mul(n1, n2);
        }
        return lean_nat_big_mul(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_div(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            ulong n1 = lean_unbox(a1), n2 = lean_unbox(a2);
            return n2 == 0 ? lean_box(0) : lean_box(n1 / n2);
        }
        return lean_nat_big_div(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_div_exact(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            ulong n1 = lean_unbox(a1), n2 = lean_unbox(a2);
            return n2 == 0 ? lean_box(0) : lean_box(n1 / n2);
        }
        return lean_nat_big_div_exact(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_mod(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            ulong n1 = lean_unbox(a1), n2 = lean_unbox(a2);
            return n2 == 0 ? lean_box(n1) : lean_box(n1 % n2);
        }
        return lean_nat_big_mod(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_nat_eq(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2)) return lean_unbox(a1) == lean_unbox(a2);
        return lean_nat_big_eq(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_nat_dec_eq(Obj a1, Obj a2) => lean_nat_eq(a1, a2) ? (byte)1 : (byte)0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_nat_ne(Obj a1, Obj a2) => !lean_nat_eq(a1, a2);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_nat_le(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2)) return lean_unbox(a1) <= lean_unbox(a2);
        return lean_nat_big_le(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_nat_dec_le(Obj a1, Obj a2) => lean_nat_le(a1, a2) ? (byte)1 : (byte)0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_nat_lt(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2)) return lean_unbox(a1) < lean_unbox(a2);
        return lean_nat_big_lt(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_nat_dec_lt(Obj a1, Obj a2) => lean_nat_lt(a1, a2) ? (byte)1 : (byte)0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_land(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2)) return lean_box(lean_unbox(a1) & lean_unbox(a2));
        return lean_nat_big_land(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_lor(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2)) return lean_box(lean_unbox(a1) | lean_unbox(a2));
        return lean_nat_big_lor(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_lxor(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2)) return lean_box(lean_unbox(a1) ^ lean_unbox(a2));
        return lean_nat_big_xor(a1, a2);
    }

    public static Obj lean_nat_shiftl(Obj a1, Obj a2)
    {
        // Special case for shifted value is 0.
        if (lean_is_scalar(a1) && lean_unbox(a1) == 0) return lean_box(0);
        if (!lean_is_scalar(a2) || lean_unbox(a2) > uint.MaxValue)
            throw lean_internal_panic("Nat.shiftl exponent is too big");
        ulong s = lean_unbox(a2);
        if (lean_is_scalar(a1) && s < 63)
        {
            // fast path: the result still fits in a small nat
            ulong v = lean_unbox(a1);
            if ((v >> (int)(63 - s)) == 0)
                return lean_box(v << (int)s);
        }
        if (s > int.MaxValue) throw lean_internal_panic_out_of_memory();
        return NumbersInternal.ToNat(lean_nat_to_big(a1) << (int)s);
    }

    public static Obj lean_nat_big_shiftr(Obj a1, Obj a2)
    {
        if (!lean_is_scalar(a2)) return lean_box(0); // This large of an exponent must be 0.
        BigInteger a = lean_nat_to_big(a1);
        ulong s = lean_unbox(a2);
        if (s > uint.MaxValue)
        {
            if (NumbersInternal.Log2(a) >= s)
                throw lean_internal_panic("Nat.shiftr exponent is too big");
            return lean_box(0);
        }
        if ((long)s >= a.GetBitLength()) return lean_box(0);
        return NumbersInternal.ToNat(a >> (int)s);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_shiftr(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            ulong s1 = lean_unbox(a1), s2 = lean_unbox(a2);
            ulong r = s2 < 64 ? s1 >> (int)s2 : 0;
            return lean_box(r);
        }
        return lean_nat_big_shiftr(a1, a2);
    }

    public static Obj lean_nat_pow(Obj a1, Obj a2)
    {
        if (!lean_is_scalar(a2) || lean_unbox(a2) > uint.MaxValue)
        {
            // The exponent does not fit in a machine word, so the result would
            // overflow memory for any base `>= 2`. `0 ^ e = 0` and `1 ^ e = 1` (e > 0).
            if (lean_is_scalar(a1))
            {
                ulong b = lean_unbox(a1);
                if (b == 0) return lean_box(0);
                if (b == 1) return lean_box(1);
            }
            throw lean_internal_panic("Nat.pow exponent is too big");
        }
        ulong e = lean_unbox(a2);
        BigInteger bb = lean_nat_to_big(a1);
        if (e > int.MaxValue)
        {
            if (bb.IsZero) return lean_box(0);
            if (bb.IsOne) return lean_box(1);
            throw lean_internal_panic_out_of_memory();
        }
        return NumbersInternal.ToNat(BigInteger.Pow(bb, (int)e));
    }

    public static Obj lean_nat_powmod(Obj b, Obj e, Obj m)
    {
        if (lean_is_scalar(m) && lean_unbox(m) == 0)
            return lean_nat_pow(b, e);
        return NumbersInternal.ToNat(BigInteger.ModPow(lean_nat_to_big(b), lean_nat_to_big(e), lean_nat_to_big(m)));
    }

    public static Obj lean_nat_gcd(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            ulong x = lean_unbox(a1), y = lean_unbox(a2);
            while (y != 0) { ulong t = x % y; x = y; y = t; }
            return lean_box(x);
        }
        return NumbersInternal.ToNat(BigInteger.GreatestCommonDivisor(lean_nat_to_big(a1), lean_nat_to_big(a2)));
    }

    public static Obj lean_nat_log2(Obj a)
    {
        if (lean_is_scalar(a))
            return lean_box((ulong)BitOperations.Log2(lean_unbox(a)));
        return lean_box(NumbersInternal.Log2(NumbersInternal.MpzValue(a)));
    }

    /// <summary>Upper bound on the size in bytes of the representation of `a` (raw value, not a `Nat`).</summary>
    public static ulong lean_nat_size_in_bytes(Obj a)
    {
        if (lean_is_scalar(a)) return 8;
        // number of 64-bit limbs * 8 (as with GMP)
        long bits = NumbersInternal.MpzValue(a).GetBitLength();
        return (ulong)((bits + 63) / 64) * 8;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_pred(Obj n) => lean_nat_sub(n, lean_box(1));

    // ------------------------------------------------------------------
    // Integers: conversions

    public const int LEAN_MAX_SMALL_INT = int.MaxValue;
    public const int LEAN_MIN_SMALL_INT = int.MinValue;

    public static Obj lean_big_int_to_int(int n) => lean_alloc_mpz(n);

    public static Obj lean_big_size_t_to_int(ulong n) => lean_alloc_mpz(n);

    public static Obj lean_big_int64_to_int(long n)
    {
        if (LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT) return lean_box((uint)(int)n);
        return lean_alloc_mpz(n);
    }

    public static Obj lean_cstr_to_int(string n) =>
        NumbersInternal.ToInt(BigInteger.Parse(n, System.Globalization.CultureInfo.InvariantCulture));

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_int_to_int(int n) => lean_box((uint)n);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_int64_to_int(long n)
    {
        if (LEAN_MIN_SMALL_INT <= n && n <= LEAN_MAX_SMALL_INT) return lean_box((uint)(int)n);
        return lean_big_int64_to_int(n);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static long lean_scalar_to_int64(Obj a) => (int)(uint)lean_unbox(a);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static int lean_scalar_to_int(Obj a) => (int)(uint)lean_unbox(a);

    /// <summary>`Int.ofNat` (consumes `a`).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_nat_to_int(Obj a)
    {
        if (lean_is_scalar(a))
        {
            ulong v = lean_unbox(a);
            if (v <= LEAN_MAX_SMALL_INT) return a;
            return lean_big_size_t_to_int(v);
        }
        return a;
    }

    /// <summary>Consumes `a` (must be a big non-negative integer).</summary>
    public static Obj lean_big_int_to_nat(Obj a)
    {
        BigInteger m = NumbersInternal.MpzValue(a);
        lean_dec(a);
        return NumbersInternal.ToNat(m);
    }

    /// <summary>Consumes `a` (must be non-negative).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_int_to_nat(Obj a)
    {
        if (lean_is_scalar(a)) return a;
        return lean_big_int_to_nat(a);
    }

    // ------------------------------------------------------------------
    // Integers: out-of-line (big) cases

    public static Obj lean_int_big_neg(Obj a) => NumbersInternal.ToInt(-NumbersInternal.MpzValue(a));

    public static Obj lean_int_big_add(Obj a1, Obj a2) =>
        NumbersInternal.ToInt(NumbersInternal.IntToBig(a1) + NumbersInternal.IntToBig(a2));

    public static Obj lean_int_big_sub(Obj a1, Obj a2) =>
        NumbersInternal.ToInt(NumbersInternal.IntToBig(a1) - NumbersInternal.IntToBig(a2));

    public static Obj lean_int_big_mul(Obj a1, Obj a2) =>
        NumbersInternal.ToInt(NumbersInternal.IntToBig(a1) * NumbersInternal.IntToBig(a2));

    public static Obj lean_int_big_div(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1))
            return NumbersInternal.ToInt(BigInteger.Divide(lean_scalar_to_int(a1), NumbersInternal.MpzValue(a2)));
        else if (lean_is_scalar(a2))
        {
            int d = lean_scalar_to_int(a2);
            if (d == 0) return a2;
            return NumbersInternal.ToInt(BigInteger.Divide(NumbersInternal.MpzValue(a1), d));
        }
        else
            return NumbersInternal.ToInt(BigInteger.Divide(NumbersInternal.MpzValue(a1), NumbersInternal.MpzValue(a2)));
    }

    public static Obj lean_int_big_div_exact(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1))
        {
            // a1 is scalar, a2 isn't but a2 divides a1:
            // 1. a1 = 0 -> 0, or 2. a1 = LEAN_MIN_SMALL_INT and a2 = -a1 -> -1
            int n = lean_scalar_to_int(a1);
            return n == 0 ? a1 : lean_box(unchecked((uint)-1));
        }
        else if (lean_is_scalar(a2))
        {
            int d = lean_scalar_to_int(a2);
            if (d == 0) return lean_box(0); // precondition violated
            return NumbersInternal.ToInt(BigInteger.Divide(NumbersInternal.MpzValue(a1), d));
        }
        else
            return NumbersInternal.ToInt(BigInteger.Divide(NumbersInternal.MpzValue(a1), NumbersInternal.MpzValue(a2)));
    }

    public static Obj lean_int_big_mod(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1))
            return NumbersInternal.ToInt(BigInteger.Remainder(lean_scalar_to_int(a1), NumbersInternal.MpzValue(a2)));
        else if (lean_is_scalar(a2))
        {
            int i2 = lean_scalar_to_int(a2);
            if (i2 == 0)
            {
                lean_inc(a1);
                return a1;
            }
            return NumbersInternal.ToInt(BigInteger.Remainder(NumbersInternal.MpzValue(a1), i2));
        }
        else
            return NumbersInternal.ToInt(BigInteger.Remainder(NumbersInternal.MpzValue(a1), NumbersInternal.MpzValue(a2)));
    }

    public static Obj lean_int_big_ediv(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1))
            return NumbersInternal.ToInt(NumbersInternal.EDiv(lean_scalar_to_int(a1), NumbersInternal.MpzValue(a2)));
        else if (lean_is_scalar(a2))
        {
            int d = lean_scalar_to_int(a2);
            if (d == 0) return a2;
            return NumbersInternal.ToInt(NumbersInternal.EDiv(NumbersInternal.MpzValue(a1), d));
        }
        else
            return NumbersInternal.ToInt(NumbersInternal.EDiv(NumbersInternal.MpzValue(a1), NumbersInternal.MpzValue(a2)));
    }

    public static Obj lean_int_big_emod(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1))
            return NumbersInternal.ToInt(NumbersInternal.EMod(lean_scalar_to_int(a1), NumbersInternal.MpzValue(a2)));
        else if (lean_is_scalar(a2))
        {
            int i2 = lean_scalar_to_int(a2);
            if (i2 == 0)
            {
                lean_inc(a1);
                return a1;
            }
            return NumbersInternal.ToInt(NumbersInternal.EMod(NumbersInternal.MpzValue(a1), i2));
        }
        else
            return NumbersInternal.ToInt(NumbersInternal.EMod(NumbersInternal.MpzValue(a1), NumbersInternal.MpzValue(a2)));
    }

    public static bool lean_int_big_eq(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) || lean_is_scalar(a2)) return false;
        return NumbersInternal.MpzValue(a1) == NumbersInternal.MpzValue(a2);
    }

    public static bool lean_int_big_le(Obj a1, Obj a2) => NumbersInternal.IntToBig(a1) <= NumbersInternal.IntToBig(a2);

    public static bool lean_int_big_lt(Obj a1, Obj a2) => NumbersInternal.IntToBig(a1) < NumbersInternal.IntToBig(a2);

    public static bool lean_int_big_nonneg(Obj a) => NumbersInternal.MpzValue(a).Sign >= 0;

    // ------------------------------------------------------------------
    // Integers: lean.h fast paths (arguments borrowed unless stated otherwise)

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_int_neg(Obj a)
    {
        if (lean_is_scalar(a)) return lean_int64_to_int(-lean_scalar_to_int64(a));
        return lean_int_big_neg(a);
    }

    /// <summary>`Int.negSucc` (consumes `a`).</summary>
    public static Obj lean_int_neg_succ_of_nat(Obj a)
    {
        Obj s = lean_nat_succ(a); lean_dec(a);
        Obj i = lean_nat_to_int(s); /* `lean_nat_to_int` consumes the argument */
        Obj r = lean_int_neg(i); lean_dec(i);
        return r;
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_int_add(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
            return lean_int64_to_int(lean_scalar_to_int64(a1) + lean_scalar_to_int64(a2));
        return lean_int_big_add(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_int_sub(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
            return lean_int64_to_int(lean_scalar_to_int64(a1) - lean_scalar_to_int64(a2));
        return lean_int_big_sub(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_int_mul(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
            return lean_int64_to_int(lean_scalar_to_int64(a1) * lean_scalar_to_int64(a2));
        return lean_int_big_mul(a1, a2);
    }

    public static Obj lean_int_div(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            long v1 = lean_scalar_to_int(a1);
            long v2 = lean_scalar_to_int(a2);
            if (v2 == 0) return lean_box(0);
            return lean_int64_to_int(v1 / v2);
        }
        return lean_int_big_div(a1, a2);
    }

    public static Obj lean_int_div_exact(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            long v1 = lean_scalar_to_int(a1);
            long v2 = lean_scalar_to_int(a2);
            if (v2 == 0) return lean_box(0);
            return lean_int64_to_int(v1 / v2);
        }
        return lean_int_big_div_exact(a1, a2);
    }

    public static Obj lean_int_mod(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            long v1 = lean_scalar_to_int64(a1);
            long v2 = lean_scalar_to_int64(a2);
            if (v2 == 0) return a1;
            return lean_int64_to_int(v1 % v2);
        }
        return lean_int_big_mod(a1, a2);
    }

    public static Obj lean_int_ediv(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            long n = lean_scalar_to_int(a1);
            long d = lean_scalar_to_int(a2);
            if (d == 0) return lean_box(0);
            long q = n / d;
            long r = n % d;
            if (r < 0) q = d > 0 ? q - 1 : q + 1;
            return lean_int64_to_int(q);
        }
        return lean_int_big_ediv(a1, a2);
    }

    public static Obj lean_int_emod(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2))
        {
            long n = lean_scalar_to_int64(a1);
            long d = lean_scalar_to_int64(a2);
            if (d == 0) return a1;
            long r = n % d;
            if (r < 0) r = d > 0 ? r + d : r - d;
            return lean_int64_to_int(r);
        }
        return lean_int_big_emod(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_int_eq(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2)) return lean_unbox(a1) == lean_unbox(a2);
        return lean_int_big_eq(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_int_ne(Obj a1, Obj a2) => !lean_int_eq(a1, a2);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_int_le(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2)) return lean_scalar_to_int(a1) <= lean_scalar_to_int(a2);
        return lean_int_big_le(a1, a2);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_int_lt(Obj a1, Obj a2)
    {
        if (lean_is_scalar(a1) && lean_is_scalar(a2)) return lean_scalar_to_int(a1) < lean_scalar_to_int(a2);
        return lean_int_big_lt(a1, a2);
    }

    /// <summary>`Int.natAbs` (borrowed argument).</summary>
    public static Obj lean_nat_abs(Obj i)
    {
        if (lean_int_lt(i, lean_box(0)))
            return lean_int_to_nat(lean_int_neg(i));
        lean_inc(i);
        return lean_int_to_nat(i);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_int_dec_eq(Obj a1, Obj a2) => lean_int_eq(a1, a2) ? (byte)1 : (byte)0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_int_dec_le(Obj a1, Obj a2) => lean_int_le(a1, a2) ? (byte)1 : (byte)0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_int_dec_lt(Obj a1, Obj a2) => lean_int_lt(a1, a2) ? (byte)1 : (byte)0;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_int_dec_nonneg(Obj a)
    {
        if (lean_is_scalar(a)) return lean_scalar_to_int(a) >= 0 ? (byte)1 : (byte)0;
        return lean_int_big_nonneg(a) ? (byte)1 : (byte)0;
    }
}
