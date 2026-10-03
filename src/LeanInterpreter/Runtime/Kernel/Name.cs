// Port of util/name.{h,cpp}: hierarchical names.
//
// inductive Name | anonymous | str (p : Name) (s : String) | num (p : Name) (i : Nat)
// with the computed field `hash : UInt64` stored in the scalar area of `str`/`num`.

using System.Runtime.CompilerServices;
using System.Text;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

public readonly struct Name : IEquatable<Name>
{
    public readonly Obj Raw;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public Name(Obj raw) { Raw = raw; }

    public static Name Anonymous => new Name(lean_box(0));

    public bool IsNull => Raw == null;
    public bool IsAnonymous => lean_is_scalar(Raw);
    public bool IsString => !lean_is_scalar(Raw) && Raw.m_tag == 1;
    public bool IsNumeral => !lean_is_scalar(Raw) && Raw.m_tag == 2;
    public bool IsAtomic => IsAnonymous || lean_is_scalar(lean_ctor_get(Raw, 0));

    public Name GetPrefix() => IsAnonymous ? this : new Name(lean_ctor_get(Raw, 0));
    /// <summary>The `String` object of a string component (borrowed).</summary>
    public Obj GetStringObj() => lean_ctor_get(Raw, 1);
    /// <summary>The `Nat` object of a numeric component (borrowed).</summary>
    public Obj GetNumeralObj() => lean_ctor_get(Raw, 1);
    public string GetString() => lean_string_to_net(GetStringObj());

    public static ulong HashOf(Obj n) => lean_is_scalar(n) ? 1723UL : lean_ctor_get_uint64_s(n, 0);
    public ulong Hash => HashOf(Raw);

    // ---------------------------------------------------------------------------------------
    // Equality and order

    public static bool StringEq(Obj s1, Obj s2)
    {
        if (ReferenceEquals(s1, s2)) return true;
        var a = (StrObj)s1; var b = (StrObj)s2;
        if (a.m_size != b.m_size) return false;
        return new ReadOnlySpan<byte>(a.m_data, 0, (int)a.m_size - 1).SequenceEqual(new ReadOnlySpan<byte>(b.m_data, 0, (int)b.m_size - 1));
    }

    /// <summary>`lean_string_lt` (byte-wise lexicographic order).</summary>
    public static bool StringLt(Obj s1, Obj s2)
    {
        var a = lean_string_span(s1); var b = lean_string_span(s2);
        int r = a.SequenceCompareTo(b);
        return r < 0;
    }

    /// <summary>Port of `lean_name_eq`.</summary>
    public static bool Eq(Obj n1, Obj n2)
    {
        if (ReferenceEquals(n1, n2)) return true;
        if (lean_is_scalar(n1) != lean_is_scalar(n2)) return false;
        if (lean_is_scalar(n1)) return true; // both anonymous
        if (lean_ctor_get_uint64_s(n1, 0) != lean_ctor_get_uint64_s(n2, 0)) return false;
        while (true)
        {
            if (n1.m_tag != n2.m_tag) return false;
            if (n1.m_tag == 1)
            {
                if (!StringEq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1))) return false;
            }
            else
            {
                if (!Nat.Eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1))) return false;
            }
            n1 = lean_ctor_get(n1, 0);
            n2 = lean_ctor_get(n2, 0);
            if (ReferenceEquals(n1, n2)) return true;
            if (lean_is_scalar(n1) != lean_is_scalar(n2)) return false;
            if (lean_is_scalar(n1)) return true;
        }
    }

    public static bool operator ==(Name a, Name b) => Eq(a.Raw, b.Raw);
    public static bool operator !=(Name a, Name b) => !Eq(a.Raw, b.Raw);
    public bool Equals(Name o) => Eq(Raw, o.Raw);
    public override bool Equals(object obj) => obj is Name n && Eq(Raw, n.Raw);
    public override int GetHashCode() => (int)(uint)Hash;

    static List<Obj> CopyLimbs(Obj p)
    {
        var limbs = new List<Obj>();
        while (!lean_is_scalar(p)) { limbs.Add(p); p = lean_ctor_get(p, 0); }
        limbs.Reverse();
        return limbs;
    }

    /// <summary>`name::cmp_core`: total order on names.</summary>
    public static int CmpCore(Obj i1, Obj i2)
    {
        var limbs1 = CopyLimbs(i1);
        var limbs2 = CopyLimbs(i2);
        int k = 0;
        for (; k < limbs1.Count && k < limbs2.Count; k++)
        {
            Obj a = limbs1[k], b = limbs2[k];
            int k1 = a.m_tag, k2 = b.m_tag;
            if (k1 != k2) return k1 == 1 ? 1 : -1;
            if (k1 == 1)
            {
                Obj s1 = lean_ctor_get(a, 1), s2 = lean_ctor_get(b, 1);
                if (StringLt(s1, s2)) return -1;
                if (StringLt(s2, s1)) return 1;
            }
            else
            {
                Obj v1 = lean_ctor_get(a, 1), v2 = lean_ctor_get(b, 1);
                if (Nat.Lt(v1, v2)) return -1;
                if (Nat.Lt(v2, v1)) return 1;
            }
        }
        if (k == limbs1.Count && k == limbs2.Count) return 0;
        return k == limbs1.Count ? -1 : 1;
    }

    public static int Cmp(Name a, Name b) => CmpCore(a.Raw, b.Raw);
    public static bool operator <(Name a, Name b) => CmpCore(a.Raw, b.Raw) < 0;
    public static bool operator >(Name a, Name b) => CmpCore(a.Raw, b.Raw) > 0;

    /// <summary>`quick_cmp`.</summary>
    public static int QuickCmp(Name a, Name b)
    {
        if (ReferenceEquals(a.Raw, b.Raw)) return 0;
        uint h1 = (uint)a.Hash, h2 = (uint)b.Hash;
        if (h1 != h2) return h1 < h2 ? -1 : 1;
        if (a == b) return 0;
        return Cmp(a, b);
    }

    /// <summary>`is_prefix_of(n1, n2)`: true iff `n1` is a prefix of `n2`.</summary>
    public static bool IsPrefixOf(Name n1, Name n2)
    {
        if (n2.IsAtomic) return n1 == n2;
        var limbs1 = CopyLimbs(n1.Raw);
        var limbs2 = CopyLimbs(n2.Raw);
        if (limbs1.Count > limbs2.Count) return false;
        if (limbs1.Count == limbs2.Count && n1.Hash != n2.Hash) return false;
        for (int k = 0; k < limbs1.Count; k++)
        {
            Obj i1 = limbs1[k], i2 = limbs2[k];
            if (i1.m_tag != i2.m_tag) return false;
            if (i1.m_tag == 1)
            {
                if (!StringEq(lean_ctor_get(i1, 1), lean_ctor_get(i2, 1))) return false;
            }
            else if (!Nat.Eq(lean_ctor_get(i1, 1), lean_ctor_get(i2, 1)))
                return false;
        }
        return true;
    }

    public Name GetRoot()
    {
        Name n = this;
        while (!n.GetPrefix().IsAnonymous) n = n.GetPrefix();
        return n;
    }

    // ---------------------------------------------------------------------------------------
    // Constructors (through the Lean exports `lean_name_mk_string` / `lean_name_mk_numeral`)

    public static Name Mk(Name prefix, string s) => new Name(KX.NameMkString(RC.Own(prefix.Raw), lean_mk_string(s)));
    public static Name Mk(Name prefix, ulong k) => new Name(KX.NameMkNumeral(RC.Own(prefix.Raw), Nat.Of(k)));
    /// <summary>`name(prefix, string_ref)`.</summary>
    public static Name MkStr(Name prefix, Obj str) => new Name(KX.NameMkString(RC.Own(prefix.Raw), RC.Own(str)));
    /// <summary>`name(prefix, nat)`.</summary>
    public static Name MkNum(Name prefix, Obj nat) => new Name(KX.NameMkNumeral(RC.Own(prefix.Raw), RC.Own(nat)));

    /// <summary>`name{"a", "b", ...}`.</summary>
    public static Name Mk(params string[] parts)
    {
        Name r = Anonymous;
        foreach (var p in parts) r = Mk(r, p);
        return r;
    }

    /// <summary>`name(char const *)`: a single string component (no splitting at dots).</summary>
    public static Name Str(string s) => Mk(Anonymous, s);

    /// <summary>`operator+`: concatenate names.</summary>
    public static Name operator +(Name n1, Name n2)
    {
        if (n2.IsAnonymous) return n1;
        if (n1.IsAnonymous) return n2;
        Name prefix = !n2.IsAtomic ? n1 + n2.GetPrefix() : n1;
        if (n2.IsString) return MkStr(prefix, n2.GetStringObj());
        return MkNum(prefix, n2.GetNumeralObj());
    }

    public Name AppendAfter(string s) => new Name(KX.NameAppendAfter(RC.Own(Raw), lean_mk_string(s)));
    public Name AppendAfter(uint i) => new Name(KX.NameAppendIndexAfter(RC.Own(Raw), lean_box(i)));

    /// <summary>If `prefix` is a prefix of this name, replace it with `newPrefix`.</summary>
    public Name ReplacePrefix(Name prefix, Name newPrefix)
    {
        if (this == prefix) return newPrefix;
        if (IsAnonymous) return this;
        Name p = GetPrefix().ReplacePrefix(prefix, newPrefix);
        if (ReferenceEquals(p.Raw, lean_ctor_get(Raw, 0))) return this;
        if (IsString) return MkStr(p, GetStringObj());
        return MkNum(p, GetNumeralObj());
    }

    // ---------------------------------------------------------------------------------------
    // Printing (`display_name`)

    static void DisplayCore(StringBuilder sb, Obj n)
    {
        Obj pre = lean_ctor_get(n, 0);
        if (!lean_is_scalar(pre))
        {
            DisplayCore(sb, pre);
            sb.Append('.');
        }
        if (n.m_tag == 1)
        {
            string str = lean_string_to_net(lean_ctor_get(n, 1));
            if (str.Length == 0) sb.Append("«»");
            else sb.Append(str);
        }
        else
        {
            sb.Append(Nat.ToDecimal(lean_ctor_get(n, 1)));
        }
    }

    public static void Display(StringBuilder sb, Obj n)
    {
        if (lean_is_scalar(n)) sb.Append("[anonymous]");
        else DisplayCore(sb, n);
    }

    public override string ToString()
    {
        if (Raw == null) return "<null>";
        var sb = new StringBuilder();
        Display(sb, Raw);
        return sb.ToString();
    }
}

/// <summary>Port of util/name_generator.cpp.</summary>
internal sealed class NameGenerator
{
    Name m_prefix;
    uint m_nextIdx;

    public NameGenerator(Name prefix) { m_prefix = prefix; m_nextIdx = 0; }
    /// <summary>`name_generator()`: uses the `_uniq` prefix.</summary>
    public NameGenerator() : this(KConsts.TmpPrefix) { }

    public Name Prefix => m_prefix;

    public Name Next()
    {
        if (m_nextIdx == uint.MaxValue)
        {
            m_prefix = Name.Mk(m_prefix, m_nextIdx);
            m_nextIdx = 0;
        }
        Name r = Name.Mk(m_prefix, m_nextIdx);
        m_nextIdx++;
        return r;
    }

    public NameGenerator Clone() => new NameGenerator(m_prefix) { m_nextIdx = m_nextIdx };
}
