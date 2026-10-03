// Port of kernel/level.{h,cpp}: universe levels.
//
// inductive Level | zero | succ (l) | max (l1 l2) | imax (l1 l2) | param (n : Name) | mvar (id : LMVarId)
// with the computed field `data : Level.Data` (UInt64, scalar offset 0 of non-nullary ctors).
// `zero` is represented by `lean_box(0)`.

using System.Runtime.CompilerServices;
using System.Text;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

public enum LevelKind : byte { Zero, Succ, Max, IMax, Param, MVar }

public readonly struct Level : IEquatable<Level>
{
    public readonly Obj Raw;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public Level(Obj raw) { Raw = raw; }

    public bool IsNull => Raw == null;

    public LevelKind Kind
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => lean_is_scalar(Raw) ? LevelKind.Zero : (LevelKind)Raw.m_tag;
    }

    /// <summary>`Level.data` of `zero`: `mkData 2221 0 false false`.</summary>
    public const ulong ZeroData = 2221;

    public static ulong DataOf(Obj l) => lean_is_scalar(l) ? ZeroData : lean_ctor_get_uint64_s(l, 0);
    public ulong Data => DataOf(Raw);
    public uint Hash => (uint)Data;
    public uint Depth => (uint)(Data >> 40);
    public bool HasMVar => ((Data >> 32) & 1) == 1;
    public bool HasParam => ((Data >> 33) & 1) == 1;

    public bool IsZero => Kind == LevelKind.Zero;
    public bool IsSucc => Kind == LevelKind.Succ;
    public bool IsMax => Kind == LevelKind.Max;
    public bool IsIMax => Kind == LevelKind.IMax;
    public bool IsParam => Kind == LevelKind.Param;
    public bool IsMVar => Kind == LevelKind.MVar;

    public Level SuccOf => new Level(lean_ctor_get(Raw, 0));
    public Level Lhs => new Level(lean_ctor_get(Raw, 0));
    public Level Rhs => new Level(lean_ctor_get(Raw, 1));
    /// <summary>`param_id` / `mvar_id` / `level_id`.</summary>
    public Name Id => new Name(lean_ctor_get(Raw, 0));

    public static bool IsEqp(Level a, Level b) => ReferenceEquals(a.Raw, b.Raw);

    // ---------------------------------------------------------------------------------------
    // Constructors

    public static Level Zero => new Level(lean_box(0));
    public static Level One => KConsts.LevelOne;

    public static Level MkSucc(Level l) => new Level(KX.LevelMkSucc(RC.Own(l.Raw)));
    public static Level MkMaxCore(Level l1, Level l2) => new Level(KX.LevelMkMax(RC.Own(l1.Raw), RC.Own(l2.Raw)));
    public static Level MkIMaxCore(Level l1, Level l2) => new Level(KX.LevelMkIMax(RC.Own(l1.Raw), RC.Own(l2.Raw)));
    public static Level MkParam(Name n) => new Level(KX.LevelMkParam(RC.Own(n.Raw)));

    public static Level MkSucc(Level l, uint k)
    {
        while (k > 0) { --k; l = MkSucc(l); }
        return l;
    }

    // ---------------------------------------------------------------------------------------
    // Basic predicates

    public static bool IsExplicit(Level l)
    {
        while (true)
        {
            switch (l.Kind)
            {
                case LevelKind.Zero: return true;
                case LevelKind.Succ: l = l.SuccOf; continue;
                default: return false;
            }
        }
    }

    /// <summary>Convert `succ^k l` into `(l, k)`.</summary>
    public static (Level, uint) ToOffset(Level l)
    {
        uint k = 0;
        while (l.IsSucc) { l = l.SuccOf; k++; }
        return (l, k);
    }

    public static bool IsOne(Level l) => l == One;

    public static bool IsNotZero(Level l)
    {
        switch (l.Kind)
        {
            case LevelKind.Zero: case LevelKind.Param: case LevelKind.MVar: return false;
            case LevelKind.Succ: return true;
            case LevelKind.Max: return IsNotZero(l.Lhs) || IsNotZero(l.Rhs);
            case LevelKind.IMax: return IsNotZero(l.Rhs);
        }
        throw lean_internal_panic_unreachable();
    }

    public static bool NormalizesToZero(Level l)
    {
        switch (l.Kind)
        {
            case LevelKind.Zero: return true;
            case LevelKind.Param: case LevelKind.MVar: case LevelKind.Succ: return false;
            case LevelKind.Max: return NormalizesToZero(l.Lhs) && NormalizesToZero(l.Rhs);
            case LevelKind.IMax: return NormalizesToZero(l.Rhs);
        }
        throw lean_internal_panic_unreachable();
    }

    public static Level MkMax(Level l1, Level l2)
    {
        if (IsExplicit(l1) && IsExplicit(l2))
            return l1.Depth >= l2.Depth ? l1 : l2;
        if (l1 == l2) return l1;
        if (l1.IsZero) return l2;
        if (l2.IsZero) return l1;
        if (l2.IsMax && (l2.Lhs == l1 || l2.Rhs == l1)) return l2;
        if (l1.IsMax && (l1.Lhs == l2 || l1.Rhs == l2)) return l1;
        var p1 = ToOffset(l1);
        var p2 = ToOffset(l2);
        if (p1.Item1 == p2.Item1)
            return p1.Item2 > p2.Item2 ? l1 : l2;
        return MkMaxCore(l1, l2);
    }

    public static Level MkIMax(Level l1, Level l2)
    {
        if (IsNotZero(l2)) return MkMax(l1, l2);
        if (l2.IsZero) return l2;
        if (l1.IsZero || IsOne(l1)) return l2;
        if (l1 == l2) return l1;
        return MkIMaxCore(l1, l2);
    }

    // ---------------------------------------------------------------------------------------
    // Structural equality

    public static bool Eq(Level l1, Level l2)
    {
        if (l1.Kind != l2.Kind) return false;
        if (l1.Hash != l2.Hash) return false;
        if (IsEqp(l1, l2)) return true;
        switch (l1.Kind)
        {
            case LevelKind.Zero: return true;
            case LevelKind.Param: case LevelKind.MVar: return l1.Id == l2.Id;
            default:
                if (l1.Depth != l2.Depth) return false;
                break;
        }
        switch (l1.Kind)
        {
            case LevelKind.Max: case LevelKind.IMax:
                return Eq(l1.Lhs, l2.Lhs) && Eq(l1.Rhs, l2.Rhs);
            case LevelKind.Succ:
                return Eq(l1.SuccOf, l2.SuccOf);
        }
        throw lean_internal_panic_unreachable();
    }

    public static bool operator ==(Level a, Level b) => Eq(a, b);
    public static bool operator !=(Level a, Level b) => !Eq(a, b);
    public bool Equals(Level o) => Eq(this, o);
    public override bool Equals(object obj) => obj is Level l && Eq(this, l);
    public override int GetHashCode() => (int)Hash;

    /// <summary>Equality of lists of levels (`list_ref<level>::operator==`).</summary>
    public static bool ListEq(Obj ls1, Obj ls2)
    {
        while (!lean_is_scalar(ls1) && !lean_is_scalar(ls2))
        {
            if (ReferenceEquals(ls1, ls2)) return true;
            if (!Eq(new Level(lean_ctor_get(ls1, 0)), new Level(lean_ctor_get(ls2, 0)))) return false;
            ls1 = lean_ctor_get(ls1, 1);
            ls2 = lean_ctor_get(ls2, 1);
        }
        return lean_is_scalar(ls1) && lean_is_scalar(ls2);
    }

    // ---------------------------------------------------------------------------------------
    // Total order

    public static bool IsLt(Level a, Level b, bool useHash)
    {
        if (IsEqp(a, b)) return false;
        uint da = a.Depth, db = b.Depth;
        if (da < db) return true;
        if (da > db) return false;
        if (a.Kind != b.Kind) return a.Kind < b.Kind;
        if (useHash)
        {
            if (a.Hash < b.Hash) return true;
            if (a.Hash > b.Hash) return false;
        }
        if (a == b) return false;
        switch (a.Kind)
        {
            case LevelKind.Param: case LevelKind.MVar:
                return a.Id < b.Id;
            case LevelKind.Max: case LevelKind.IMax:
                if (a.Lhs != b.Lhs) return IsLt(a.Lhs, b.Lhs, useHash);
                return IsLt(a.Rhs, b.Rhs, useHash);
            case LevelKind.Succ:
                return IsLt(a.SuccOf, b.SuccOf, useHash);
        }
        throw lean_internal_panic_unreachable();
    }

    public static bool IsLt(Obj las, Obj lbs, bool useHash)
    {
        while (true)
        {
            if (KList.IsNil(las)) return !KList.IsNil(lbs);
            if (KList.IsNil(lbs)) return false;
            var a = new Level(KList.Head(las)); var b = new Level(KList.Head(lbs));
            if (a == b) { las = KList.Tail(las); lbs = KList.Tail(lbs); continue; }
            return IsLt(a, b, useHash);
        }
    }

    // ---------------------------------------------------------------------------------------
    // Traversals

    public static void ForEach(Level l, Func<Level, bool> f)
    {
        if (!f(l)) return;
        switch (l.Kind)
        {
            case LevelKind.Succ: ForEach(l.SuccOf, f); break;
            case LevelKind.Max: case LevelKind.IMax: ForEach(l.Lhs, f); ForEach(l.Rhs, f); break;
        }
    }

    /// <summary>`replace_level_fn`: `f` returns a null-`Raw` level for "none".</summary>
    public static Level Replace(Level l, Func<Level, Level> f)
    {
        Level r = f(l);
        if (!r.IsNull) return r;
        switch (l.Kind)
        {
            case LevelKind.Succ:
                return UpdateSucc(l, Replace(l.SuccOf, f));
            case LevelKind.Max: case LevelKind.IMax:
            {
                Level l1 = Replace(l.Lhs, f);
                Level l2 = Replace(l.Rhs, f);
                return UpdateMax(l, l1, l2);
            }
            default:
                return l;
        }
    }

    public static Name? GetUndefParam(Level l, Obj lparams)
    {
        Name? r = null;
        ForEach(l, x =>
        {
            if (!x.HasParam || r.HasValue) return false;
            if (x.IsParam && !NameListContains(lparams, x.Id)) r = x.Id;
            return true;
        });
        return r;
    }

    internal static bool NameListContains(Obj names, Name n)
    {
        for (Obj it = names; !lean_is_scalar(it); it = lean_ctor_get(it, 1))
            if (new Name(lean_ctor_get(it, 0)) == n) return true;
        return false;
    }

    public static Level UpdateSucc(Level l, Level newArg)
    {
        if (IsEqp(l.SuccOf, newArg)) return l;
        return MkSucc(newArg);
    }

    public static Level UpdateMax(Level l, Level newLhs, Level newRhs)
    {
        if (IsEqp(l.Lhs, newLhs) && IsEqp(l.Rhs, newRhs)) return l;
        if (l.IsMax) return MkMax(newLhs, newRhs);
        return MkIMax(newLhs, newRhs);
    }

    /// <summary>Instantiate the level parameters `ps` (List Name) with `ls` (List Level).</summary>
    public static Level Instantiate(Level l, Obj ps, Obj ls)
    {
        return Replace(l, x =>
        {
            if (!x.HasParam) return x;
            if (x.IsParam)
            {
                Name id = x.Id;
                Obj it1 = ps, it2 = ls;
                while (!lean_is_scalar(it1) && !lean_is_scalar(it2))
                {
                    if (new Name(lean_ctor_get(it1, 0)) == id) return new Level(lean_ctor_get(it2, 0));
                    it1 = lean_ctor_get(it1, 1);
                    it2 = lean_ctor_get(it2, 1);
                }
                return x;
            }
            return default;
        });
    }

    // ---------------------------------------------------------------------------------------
    // Normalization

    static bool IsNormLt(Level a, Level b)
    {
        if (IsEqp(a, b)) return false;
        var p1 = ToOffset(a);
        var p2 = ToOffset(b);
        Level l1 = p1.Item1, l2 = p2.Item1;
        if (l1 != l2)
        {
            if (l1.Kind != l2.Kind) return l1.Kind < l2.Kind;
            switch (l1.Kind)
            {
                case LevelKind.Param: case LevelKind.MVar:
                    return l1.Id < l2.Id;
                case LevelKind.Max: case LevelKind.IMax:
                    if (l1.Lhs != l2.Lhs) return IsNormLt(l1.Lhs, l2.Lhs);
                    return IsNormLt(l1.Rhs, l2.Rhs);
            }
            throw lean_internal_panic_unreachable();
        }
        return p1.Item2 < p2.Item2;
    }

    static void PushMaxArgs(Level l, List<Level> r)
    {
        if (l.IsMax) { PushMaxArgs(l.Lhs, r); PushMaxArgs(l.Rhs, r); }
        else r.Add(l);
    }

    static Level MkMax(List<Level> args)
    {
        int nargs = args.Count;
        if (nargs == 1) return args[0];
        Level r = MkMax(args[nargs - 2], args[nargs - 1]);
        int i = nargs - 2;
        while (i > 0) { --i; r = MkMax(args[i], r); }
        return r;
    }

    /// <summary>`std::sort` with the strict weak order `is_norm_lt`.</summary>
    static void SortNorm(List<Level> args)
    {
        // Insertion sort would be stable; std::sort is not, but equivalent elements (w.r.t.
        // `is_norm_lt`) are structurally equal, so the result does not depend on the algorithm.
        args.Sort((x, y) => IsNormLt(x, y) ? -1 : (IsNormLt(y, x) ? 1 : 0));
    }

    public static Level Normalize(Level l)
    {
        var p = ToOffset(l);
        Level r = p.Item1;
        switch (r.Kind)
        {
            case LevelKind.Zero: case LevelKind.Param: case LevelKind.MVar:
                return l;
            case LevelKind.IMax:
            {
                Level l1 = Normalize(r.Lhs);
                Level l2 = Normalize(r.Rhs);
                return MkSucc(MkIMax(l1, l2), p.Item2);
            }
            case LevelKind.Max:
            {
                var todo = new List<Level>();
                var args = new List<Level>();
                PushMaxArgs(r, todo);
                foreach (var a in todo) PushMaxArgs(Normalize(a), args);
                SortNorm(args);
                var rargs = new List<Level>();
                int i = 0;
                if (IsExplicit(args[i]))
                {
                    while (i + 1 < args.Count && IsExplicit(args[i + 1])) i++;
                    uint k = ToOffset(args[i]).Item2;
                    int j = i + 1;
                    for (; j < args.Count; j++)
                        if (ToOffset(args[j]).Item2 >= k) break;
                    if (j < args.Count) i++;
                }
                rargs.Add(args[i]);
                var pPrev = ToOffset(args[i]);
                i++;
                for (; i < args.Count; i++)
                {
                    var pCurr = ToOffset(args[i]);
                    if (pPrev.Item1 == pCurr.Item1)
                    {
                        if (pPrev.Item2 < pCurr.Item2)
                        {
                            pPrev = pCurr;
                            rargs.RemoveAt(rargs.Count - 1);
                            rargs.Add(args[i]);
                        }
                    }
                    else
                    {
                        pPrev = pCurr;
                        rargs.Add(args[i]);
                    }
                }
                for (int m = 0; m < rargs.Count; m++) rargs[m] = MkSucc(rargs[m], p.Item2);
                return MkMax(rargs);
            }
        }
        throw lean_internal_panic_unreachable();
    }

    public static bool IsEquivalent(Level lhs, Level rhs)
    {
        KernelLimits.CheckSystem("level constraints");
        return lhs == rhs || Normalize(lhs) == Normalize(rhs);
    }

    public static bool IsGeqCore(Level l1, Level l2)
    {
        if (l1 == l2 || l2.IsZero) return true;
        if (l2.IsMax) return IsGeq(l1, l2.Lhs) && IsGeq(l1, l2.Rhs);
        if (l1.IsMax && (IsGeq(l1.Lhs, l2) || IsGeq(l1.Rhs, l2))) return true;
        if (l2.IsIMax) return IsGeq(l1, l2.Lhs) && IsGeq(l1, l2.Rhs);
        if (l1.IsIMax) return IsGeq(l1.Rhs, l2);
        var p1 = ToOffset(l1);
        var p2 = ToOffset(l2);
        if (p1.Item1 == p2.Item1 || p2.Item1.IsZero) return p1.Item2 >= p2.Item2;
        if (p1.Item2 == p2.Item2 && p1.Item2 > 0) return IsGeq(p1.Item1, p2.Item1);
        return false;
    }

    public static bool IsGeq(Level l1, Level l2) => IsGeqCore(Normalize(l1), Normalize(l2));

    /// <summary>Convert a list of level parameter names into a list of levels (owned list).</summary>
    public static Obj LParamsToLevels(Obj ps)
    {
        var ls = new List<Obj>();
        foreach (var p in KList.Iter(ps)) ls.Add(MkParam(new Name(p)).Raw);
        return KList.OfBorrowed(ls);
    }

    // ---------------------------------------------------------------------------------------
    // Printing

    static void PrintChild(StringBuilder sb, Level l)
    {
        if (IsExplicit(l) || l.IsParam || l.IsMVar) Print(sb, l);
        else { sb.Append('('); Print(sb, l); sb.Append(')'); }
    }

    public static void Print(StringBuilder sb, Level l)
    {
        if (IsExplicit(l)) { sb.Append(l.Depth); return; }
        switch (l.Kind)
        {
            case LevelKind.Param: Name.Display(sb, l.Id.Raw); break;
            case LevelKind.MVar: sb.Append('?'); Name.Display(sb, l.Id.Raw); break;
            case LevelKind.Succ: sb.Append("succ "); PrintChild(sb, l.SuccOf); break;
            case LevelKind.Max: case LevelKind.IMax:
                sb.Append(l.IsMax ? "max " : "imax ");
                PrintChild(sb, l.Lhs);
                while (l.Rhs.Kind == l.Kind)
                {
                    l = l.Rhs;
                    sb.Append(' ');
                    PrintChild(sb, l.Lhs);
                }
                sb.Append(' ');
                PrintChild(sb, l.Rhs);
                break;
        }
    }

    public override string ToString()
    {
        if (Raw == null) return "<null>";
        var sb = new StringBuilder();
        Print(sb, this);
        return sb.ToString();
    }
}
