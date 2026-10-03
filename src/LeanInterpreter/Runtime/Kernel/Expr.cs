// Port of kernel/expr.{h,cpp}: expressions.
//
// inductive Expr
// | bvar (idx : Nat) | fvar (id : FVarId) | mvar (id : MVarId) | sort (u : Level)
// | const (n : Name) (us : List Level) | app (f a : Expr)
// | lam (n : Name) (t b : Expr) (bi : BinderInfo) | forallE (n : Name) (t b : Expr) (bi : BinderInfo)
// | letE (n : Name) (t v b : Expr) (nondep : Bool) | lit (l : Literal) | mdata (d : MData) (e : Expr)
// | proj (s : Name) (i : Nat) (e : Expr)
// with the computed field `data : Expr.Data` (UInt64 at scalar offset 0); `bi`/`nondep` are
// stored as UInt8 at scalar offset 8.

using System.Runtime.CompilerServices;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

public enum ExprKind : byte { BVar, FVar, MVar, Sort, Const, App, Lambda, Pi, Let, Lit, MData, Proj }

public enum BinderInfo : byte { Default, Implicit, StrictImplicit, InstImplicit }

public readonly struct Expr : IEquatable<Expr>
{
    public readonly Obj Raw;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public Expr(Obj raw) { Raw = raw; }

    /// <summary>`none_expr()`.</summary>
    public static Expr None => default;
    public bool IsNull => Raw == null;
    public bool IsSome => Raw != null;

    public ExprKind Kind
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => (ExprKind)Raw.m_tag;
    }

    // ---------------------------------------------------------------------------------------
    // Cached data

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong DataOf(Obj e) => lean_ctor_get_uint64_s(e, 0);
    public ulong Data => DataOf(Raw);
    public uint Hash => (uint)Data;
    public bool HasFVar => ((Data >> 40) & 1) == 1;
    public bool HasExprMVar => ((Data >> 41) & 1) == 1;
    public bool HasUnivMVar => ((Data >> 42) & 1) == 1;
    public bool HasMVar => ((Data >> 41) & 3) != 0;
    public bool HasUnivParam => ((Data >> 43) & 1) == 1;
    public uint LooseBVarRange => (uint)(Data >> 44);
    public bool HasLooseBVars => LooseBVarRange > 0;

    // ---------------------------------------------------------------------------------------
    // Testers

    public bool IsBVar => Kind == ExprKind.BVar;
    public bool IsFVar => Kind == ExprKind.FVar;
    public bool IsMVar => Kind == ExprKind.MVar;
    public bool IsSort => Kind == ExprKind.Sort;
    public bool IsConst => Kind == ExprKind.Const;
    public bool IsApp => Kind == ExprKind.App;
    public bool IsLambda => Kind == ExprKind.Lambda;
    public bool IsPi => Kind == ExprKind.Pi;
    public bool IsLet => Kind == ExprKind.Let;
    public bool IsLit => Kind == ExprKind.Lit;
    public bool IsMData => Kind == ExprKind.MData;
    public bool IsProj => Kind == ExprKind.Proj;
    public bool IsBinding => IsLambda || IsPi;
    public bool IsNatLit => IsLit && lean_obj_tag(lean_ctor_get(Raw, 0)) == 0;
    public bool IsStringLit => IsLit && lean_obj_tag(lean_ctor_get(Raw, 0)) == 1;

    public bool IsConstOf(Name n) => IsConst && ConstName == n;
    public bool IsBVarIdx(ulong i) => IsBVar && Nat.Eq(BVarIdx, i);

    public static bool IsAtomic(Expr e)
    {
        switch (e.Kind)
        {
            case ExprKind.Const: case ExprKind.Sort: case ExprKind.BVar:
            case ExprKind.Lit: case ExprKind.MVar: case ExprKind.FVar:
                return true;
            default:
                return false;
        }
    }

    // ---------------------------------------------------------------------------------------
    // Accessors

    /// <summary>Literal object (`Literal.natVal n` tag 0 / `Literal.strVal s` tag 1).</summary>
    public Obj LitValue => lean_ctor_get(Raw, 0);
    /// <summary>The `Nat` of a nat literal.</summary>
    public Obj LitNat => lean_ctor_get(lean_ctor_get(Raw, 0), 0);
    /// <summary>The `String` of a string literal.</summary>
    public Obj LitString => lean_ctor_get(lean_ctor_get(Raw, 0), 0);
    public Obj MDataData => lean_ctor_get(Raw, 0);
    public Expr MDataExpr => new Expr(lean_ctor_get(Raw, 1));
    public Name ProjSName => new Name(lean_ctor_get(Raw, 0));
    public Obj ProjIdx => lean_ctor_get(Raw, 1);
    public Expr ProjExpr => new Expr(lean_ctor_get(Raw, 2));
    public Obj BVarIdx => lean_ctor_get(Raw, 0);
    public Name FVarName => new Name(lean_ctor_get(Raw, 0));
    public Name MVarName => new Name(lean_ctor_get(Raw, 0));
    public Level SortLevel => new Level(lean_ctor_get(Raw, 0));
    public Name ConstName => new Name(lean_ctor_get(Raw, 0));
    public Obj ConstLevels => lean_ctor_get(Raw, 1);
    public Expr AppFn => new Expr(lean_ctor_get(Raw, 0));
    public Expr AppArg => new Expr(lean_ctor_get(Raw, 1));
    public Name BindingName => new Name(lean_ctor_get(Raw, 0));
    public Expr BindingDomain => new Expr(lean_ctor_get(Raw, 1));
    public Expr BindingBody => new Expr(lean_ctor_get(Raw, 2));
    public BinderInfo BindingInfo => (BinderInfo)lean_ctor_get_uint8_s(Raw, 8);
    public Name LetName => new Name(lean_ctor_get(Raw, 0));
    public Expr LetType => new Expr(lean_ctor_get(Raw, 1));
    public Expr LetValue => new Expr(lean_ctor_get(Raw, 2));
    public Expr LetBody => new Expr(lean_ctor_get(Raw, 3));
    public bool LetNonDep => lean_ctor_get_uint8_s(Raw, 8) != 0;

    public static bool IsEqp(Expr a, Expr b) => ReferenceEquals(a.Raw, b.Raw);

    // ---------------------------------------------------------------------------------------
    // Equality (structural, binder information ignored; see ExprEqFn)

    public static bool operator ==(Expr a, Expr b) => ExprEqFn.IsEqual(a, b);
    public static bool operator !=(Expr a, Expr b) => !ExprEqFn.IsEqual(a, b);
    public bool Equals(Expr o) => ExprEqFn.IsEqual(this, o);
    public override bool Equals(object obj) => obj is Expr e && ExprEqFn.IsEqual(this, e);
    public override int GetHashCode() => (int)Hash;

    public override string ToString() => Raw == null ? "<null>" : ExprPrinter.ToString(this);

    // ---------------------------------------------------------------------------------------
    // Constructors (through the Lean exports)

    /// <summary>`literal(nat)`: `Literal.natVal v` (takes a borrowed nat).</summary>
    public static Obj MkNatLiteral(Obj nat) => RC.MkCnstr(0, RC.Own(nat));

    public static Expr MkLit(Obj literal) => new Expr(KX.ExprMkLit(RC.Own(literal)));
    public static Expr MkNatLit(Obj nat) => new Expr(KX.ExprMkLit(MkNatLiteral(nat)));
    public static Expr MkMData(Obj kvmap, Expr e) => new Expr(KX.ExprMkMData(RC.Own(kvmap), RC.Own(e.Raw)));
    public static Expr MkProj(Name s, Obj idx, Expr e) => new Expr(KX.ExprMkProj(RC.Own(s.Raw), RC.Own(idx), RC.Own(e.Raw)));
    public static Expr MkProj(Name s, ulong idx, Expr e) => new Expr(KX.ExprMkProj(RC.Own(s.Raw), Nat.Of(idx), RC.Own(e.Raw)));
    public static Expr MkBVar(Obj idx) => new Expr(KX.ExprMkBVar(RC.Own(idx)));
    public static Expr MkBVar(ulong idx) => new Expr(KX.ExprMkBVar(Nat.Of(idx)));
    public static Expr MkFVar(Name n) => new Expr(KX.ExprMkFVar(RC.Own(n.Raw)));
    public static Expr MkConst(Name n, Obj levels) => new Expr(KX.ExprMkConst(RC.Own(n.Raw), RC.Own(levels)));
    public static Expr MkConst(Name n) => new Expr(KX.ExprMkConst(RC.Own(n.Raw), lean_box(0)));
    public static Expr MkConst(Name n, params Level[] ls) => new Expr(KX.ExprMkConst(RC.Own(n.Raw), KList.OfBorrowed(ls)));
    public static Expr MkApp(Expr f, Expr a) => new Expr(KX.ExprMkApp(RC.Own(f.Raw), RC.Own(a.Raw)));
    public static Expr MkSort(Level l) => new Expr(KX.ExprMkSort(RC.Own(l.Raw)));
    public static Expr MkLambda(Name n, Expr t, Expr e, BinderInfo bi = BinderInfo.Default) =>
        new Expr(KX.ExprMkLambda(RC.Own(n.Raw), RC.Own(t.Raw), RC.Own(e.Raw), (byte)bi));
    public static Expr MkPi(Name n, Expr t, Expr e, BinderInfo bi = BinderInfo.Default) =>
        new Expr(KX.ExprMkForall(RC.Own(n.Raw), RC.Own(t.Raw), RC.Own(e.Raw), (byte)bi));
    public static Expr MkBinding(ExprKind k, Name n, Expr t, Expr e, BinderInfo bi = BinderInfo.Default) =>
        k == ExprKind.Pi ? MkPi(n, t, e, bi) : MkLambda(n, t, e, bi);
    public static Expr MkArrow(Expr t, Expr e) => MkPi(KConsts.DefaultName, t, e, BinderInfo.Default);
    public static Expr MkLet(Name n, Expr t, Expr v, Expr b, bool nondep = false) =>
        new Expr(KX.ExprMkLet(RC.Own(n.Raw), RC.Own(t.Raw), RC.Own(v.Raw), RC.Own(b.Raw), nondep ? (byte)1 : (byte)0));
    public static Expr MkProp() => KConsts.Prop;

    public static Expr MkApp(Expr f, IReadOnlyList<Expr> args) => MkApp(f, args.Count, args, 0);

    public static Expr MkApp(Expr f, int numArgs, IReadOnlyList<Expr> args, int offset)
    {
        Expr r = f;
        for (int i = 0; i < numArgs; i++) r = MkApp(r, args[offset + i]);
        return r;
    }

    public static Expr MkApp(Expr f, params Expr[] args) => MkApp(f, args.Length, args, 0);

    /// <summary>`mk_app(num_args, args)` with `num_args >= 2`.</summary>
    public static Expr MkAppN(IReadOnlyList<Expr> args) => MkApp(MkApp(args[0], args[1]), args.Count - 2, args, 2);

    public static Expr MkRevApp(Expr f, int numArgs, IReadOnlyList<Expr> args, int offset = 0)
    {
        Expr r = f;
        int i = numArgs;
        while (i > 0) { --i; r = MkApp(r, args[offset + i]); }
        return r;
    }

    public static Expr MkRevApp(Expr f, IReadOnlyList<Expr> args) => MkRevApp(f, args.Count, args, 0);

    // ---------------------------------------------------------------------------------------
    // Application helpers

    /// <summary>Store the arguments of `e` in `args` and return the head function.</summary>
    public static Expr GetAppArgs(Expr e, List<Expr> args)
    {
        int sz = args.Count;
        Expr it = e;
        while (it.IsApp) { args.Add(it.AppArg); it = it.AppFn; }
        args.Reverse(sz, args.Count - sz);
        return it;
    }

    public static Expr GetAppRevArgs(Expr e, List<Expr> args)
    {
        Expr it = e;
        while (it.IsApp) { args.Add(it.AppArg); it = it.AppFn; }
        return it;
    }

    public static Expr GetAppFn(Expr e)
    {
        Obj it = e.Raw;
        while (it.m_tag == (byte)ExprKind.App) it = lean_ctor_get(it, 0);
        return new Expr(it);
    }

    public static uint GetAppNumArgs(Expr e)
    {
        Obj it = e.Raw;
        uint n = 0;
        while (it.m_tag == (byte)ExprKind.App) { it = lean_ctor_get(it, 0); n++; }
        return n;
    }

    public static bool IsArrow(Expr t)
    {
        if (!t.IsPi) return false;
        if (t.HasLooseBVars) return !HasLooseBVar(t.BindingBody, 0);
        return !t.BindingBody.HasLooseBVars;
    }

    public static Expr LitType(Obj literal) => new Expr(KX.LitType(RC.Own(literal)));

    public static Expr ConsumeTypeAnnotations(Expr e) => new Expr(KX.ExprConsumeTypeAnnotations(RC.Own(e.Raw)));

    // ---------------------------------------------------------------------------------------
    // Update

    public static Expr UpdateMData(Expr e, Expr t) => !IsEqp(e.MDataExpr, t) ? MkMData(e.MDataData, t) : e;
    public static Expr UpdateProj(Expr e, Expr t) => !IsEqp(e.ProjExpr, t) ? MkProj(e.ProjSName, e.ProjIdx, t) : e;

    public static Expr UpdateApp(Expr e, Expr newFn, Expr newArg)
    {
        if (!IsEqp(e.AppFn, newFn) || !IsEqp(e.AppArg, newArg)) return MkApp(newFn, newArg);
        return e;
    }

    public static Expr UpdateBinding(Expr e, Expr newDomain, Expr newBody)
    {
        if (!IsEqp(e.BindingDomain, newDomain) || !IsEqp(e.BindingBody, newBody))
            return MkBinding(e.Kind, e.BindingName, newDomain, newBody, e.BindingInfo);
        return e;
    }

    public static Expr UpdateBinding(Expr e, Expr newDomain, Expr newBody, BinderInfo bi)
    {
        if (!IsEqp(e.BindingDomain, newDomain) || !IsEqp(e.BindingBody, newBody) || bi != e.BindingInfo)
            return MkBinding(e.Kind, e.BindingName, newDomain, newBody, bi);
        return e;
    }

    public static Expr UpdateSort(Expr e, Level newLevel) => !Level.IsEqp(e.SortLevel, newLevel) ? MkSort(newLevel) : e;

    public static Expr UpdateConst(Expr e, Obj newLevels) => !ReferenceEquals(e.ConstLevels, newLevels) ? MkConst(e.ConstName, newLevels) : e;

    public static Expr UpdateLet(Expr e, Expr newType, Expr newValue, Expr newBody)
    {
        if (!IsEqp(e.LetType, newType) || !IsEqp(e.LetValue, newValue) || !IsEqp(e.LetBody, newBody))
            return MkLet(e.LetName, newType, newValue, newBody, e.LetNonDep);
        return e;
    }

    // ---------------------------------------------------------------------------------------
    // Loose bound variables

    /// <summary>Return true iff `e` contains the loose bound variable `#i`.</summary>
    public static bool HasLooseBVar(Expr e, uint i)
    {
        if (!e.HasLooseBVars) return false;
        bool found = false;
        ForEachFn.ForEachOffset(e, (x, offset) =>
        {
            if (found) return false;
            uint ni = i + offset;
            if (ni < i) return false; // overflow
            if (ni >= x.LooseBVarRange) return false;
            if (x.IsBVar && Nat.Eq(x.BVarIdx, ni)) found = true;
            return true;
        });
        return found;
    }

    /// <summary>Lower the loose bound variables `>= s` in `e` by `d`.</summary>
    public static Expr LowerLooseBVars(Expr e, uint s, uint d)
    {
        if (d == 0 || s >= e.LooseBVarRange) return e;
        return ReplaceFn.Replace(e, (x, offset) =>
        {
            uint s1 = s + offset;
            if (s1 < s) return x;
            if (s1 >= x.LooseBVarRange) return x;
            if (x.IsBVar && Nat.Ge(x.BVarIdx, s1))
                return MkBVar(Nat.Sub(x.BVarIdx, d));
            return None;
        });
    }

    public static Expr LowerLooseBVars(Expr e, uint d) => LowerLooseBVars(e, d, d);

    /// <summary>Lift loose bound variables `>= s` in `e` by `d`.</summary>
    public static Expr LiftLooseBVars(Expr e, uint s, uint d)
    {
        if (d == 0 || s >= e.LooseBVarRange) return e;
        return ReplaceFn.Replace(e, (x, offset) =>
        {
            uint s1 = s + offset;
            if (s1 < s) return x;
            if (s1 >= x.LooseBVarRange) return x;
            if (x.IsBVar && Nat.Ge(x.BVarIdx, s + offset))
                return MkBVar(Nat.Add(x.BVarIdx, d));
            return None;
        });
    }

    public static Expr LiftLooseBVars(Expr e, uint d) => LiftLooseBVars(e, 0, d);

    // ---------------------------------------------------------------------------------------
    // Implicit argument inference

    static bool HasLooseBVarsInDomain(Expr b, uint vidx, bool strict)
    {
        if (b.IsPi)
        {
            if (HasLooseBVar(b.BindingDomain, vidx))
            {
                if (IsExplicitBinder(b.BindingInfo)) return true;
                if (HasLooseBVarsInDomain(b.BindingBody, 0, strict)) return true;
            }
            return HasLooseBVarsInDomain(b.BindingBody, vidx + 1, strict);
        }
        if (!strict) return HasLooseBVar(b, vidx);
        return false;
    }

    public static bool IsExplicitBinder(BinderInfo bi) => bi != BinderInfo.Implicit && bi != BinderInfo.StrictImplicit && bi != BinderInfo.InstImplicit;

    public static Expr InferImplicit(Expr t, uint numParams, bool strict)
    {
        if (numParams == 0) return t;
        if (t.IsPi)
        {
            Expr newBody = InferImplicit(t.BindingBody, numParams - 1, strict);
            if (!IsExplicitBinder(t.BindingInfo))
                return UpdateBinding(t, t.BindingDomain, newBody);
            if (HasLooseBVarsInDomain(newBody, 0, strict))
                return UpdateBinding(t, t.BindingDomain, newBody, BinderInfo.Implicit);
            return UpdateBinding(t, t.BindingDomain, newBody);
        }
        return t;
    }

    public static Expr InferImplicit(Expr t, bool strict) => InferImplicit(t, uint.MaxValue, strict);

    // ---------------------------------------------------------------------------------------
    // Data computation (`lean_expr_mk_data`, `lean_expr_mk_app_data`)

    public static ulong MkData(ulong hash, Obj bvarRange, uint approxDepth, byte hasFVar, byte hasExprMVar, byte hasLevelMVar, byte hasLevelParam)
    {
        if (approxDepth > 255) approxDepth = 255;
        if (!lean_is_scalar(bvarRange)) throw lean_internal_panic("too many bound variables");
        ulong range = lean_unbox(bvarRange);
        if (range > 1048575) throw lean_internal_panic("too many bound variables");
        uint r = (uint)range;
        uint h = (uint)hash;
        return ((ulong)h) + (((ulong)approxDepth) << 32) + (((ulong)hasFVar) << 40)
            + (((ulong)hasExprMVar) << 41) + (((ulong)hasLevelMVar) << 42) + (((ulong)hasLevelParam) << 43)
            + (((ulong)r) << 44);
    }

    static ushort GetApproxDepth(ulong data) => (ushort)((data >> 32) & 255);
    static uint GetBVarRange(ulong data) => (uint)(data >> 44);

    public static ulong MkAppData(ulong fData, ulong aData)
    {
        ushort depth = (ushort)(Math.Max(GetApproxDepth(fData), GetApproxDepth(aData)) + 1);
        if (depth > 255) depth = 255;
        uint range = Math.Max(GetBVarRange(fData), GetBVarRange(aData));
        uint h = (uint)LeanHash.Mix(fData, aData);
        return ((fData | aData) & (((ulong)15) << 40)) | ((ulong)h) | (((ulong)depth) << 32) | (((ulong)range) << 44);
    }
}

/// <summary>Structural equality comparer for expressions (`expr_hash`, `std::equal_to<expr>`).</summary>
internal sealed class ExprComparer : IEqualityComparer<Expr>
{
    public static readonly ExprComparer Instance = new();
    public bool Equals(Expr a, Expr b) => ExprEqFn.IsEqual(a, b);
    public int GetHashCode(Expr e) => (int)e.Hash;
}

/// <summary>Structural equality comparer for pairs of expressions (`expr_pair_hash`, `expr_pair_eq`).</summary>
internal sealed class ExprPairComparer : IEqualityComparer<(Expr, Expr)>
{
    public static readonly ExprPairComparer Instance = new();
    public bool Equals((Expr, Expr) a, (Expr, Expr) b) => ExprEqFn.IsEqual(a.Item1, b.Item1) && ExprEqFn.IsEqual(a.Item2, b.Item2);
    public int GetHashCode((Expr, Expr) p) => (int)(uint)LeanHash.Mix(p.Item1.Hash, p.Item2.Hash);
}
