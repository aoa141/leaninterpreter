// Port of kernel/type_checker.{h,cpp}.

using System.Numerics;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

/// <summary>Three-valued result (`lbool`).</summary>
internal enum LBool : sbyte { False = -1, Undef = 0, True = 1 }

/// <summary>Lean type checker. Dispose to release the references to the environment and local context.</summary>
internal sealed class TypeChecker : IDisposable
{
    /// <summary>`type_checker::state`.</summary>
    public sealed class State
    {
        /// <summary>Owned reference to the environment.</summary>
        public Obj EnvObj;
        public readonly NameGenerator NGen;
        public readonly Dictionary<Expr, Expr>[] InferType =
            { new Dictionary<Expr, Expr>(ExprComparer.Instance), new Dictionary<Expr, Expr>(ExprComparer.Instance) };
        public readonly Dictionary<Expr, Expr> WhnfCore = new(ExprComparer.Instance);
        public readonly Dictionary<Expr, Expr> Whnf = new(ExprComparer.Instance);
        public readonly HashSet<(Expr, Expr)> Success = new(ExprPairComparer.Instance);
        public readonly HashSet<(Expr, Expr)> Failure = new(ExprPairComparer.Instance);
        public readonly Dictionary<Expr, Expr> Unfold = new(ExprComparer.Instance);

        public State(Environment env)
        {
            EnvObj = RC.Own(env.Raw);
            NGen = new NameGenerator(KConsts.KernelFresh);
        }
    }

    enum ReductionStatus { Continue, DefUnknown, DefEqual, DefDiff }

    const ulong NatMaxSizeDefault = 128UL * 1024 * 1024;    // 128 MB

    /// <summary>
    /// Upper bound (in bytes) on the numerals the kernel computes (`LEAN_NAT_MAX_SIZE`), as read
    /// from the environment of the OS process when the kernel was first used. The kernel itself
    /// uses <see cref="CurrentNatMaxSize"/>.
    /// </summary>
    public static readonly ulong NatMaxSize = ReadNatSizeEnv("LEAN_NAT_MAX_SIZE", NatMaxSizeDefault);

    /// <summary>
    /// `g_nat_max_size`: natively read from the environment once per process
    /// (`initialize_type_checker`). LeanInterpreter runs many Lean programs in one OS process, each with
    /// its own (logical) environment, so the limit is the one of the current logical process.
    /// </summary>
    internal static ulong CurrentNatMaxSize => LeanInterpreter.Runtime.LeanContext.Proc.NatMaxSize(NatMaxSizeDefault);

    readonly State m_st;
    readonly Diagnostics m_diag;
    /// <summary>Owned local context object.</summary>
    Obj m_lctx;
    readonly DefinitionSafety m_definitionSafety;
    bool m_eagerReduce;
    /// <summary>When non-null, `check` makes sure all level parameters are in this list.</summary>
    Obj m_lparams;
    bool m_disposed;

    public TypeChecker(Environment env, Obj lctx, Diagnostics diag = null, DefinitionSafety ds = DefinitionSafety.Safe)
    {
        m_st = new State(env);
        m_diag = diag;
        m_lctx = RC.Own(lctx);
        m_definitionSafety = ds;
    }

    public TypeChecker(Environment env, Diagnostics diag = null, DefinitionSafety ds = DefinitionSafety.Safe)
    {
        m_st = new State(env);
        m_diag = diag;
        m_lctx = KX.MkEmptyLocalCtx(lean_box(0));
        m_definitionSafety = ds;
    }

    public void Dispose()
    {
        if (m_disposed) return;
        m_disposed = true;
        lean_dec(m_lctx);
        lean_dec(m_st.EnvObj);
    }

    public Environment Env => new Environment(m_st.EnvObj);
    public Obj LCtx => m_lctx;

    // ---------------------------------------------------------------------------------------
    // Local context helpers (`m_lctx.mk_local_decl`, `flet<local_ctx>`)

    Expr MkLocalDecl(Name un, Expr type, BinderInfo bi)
    {
        Name n = m_st.NGen.Next();
        m_lctx = KX.LocalCtxMkLocalDecl(m_lctx, RC.Own(n.Raw), RC.Own(un.Raw), RC.Own(type.Raw), (byte)bi);
        return Expr.MkFVar(n);
    }

    Expr MkLetDecl(Name un, Expr type, Expr value)
    {
        Name n = m_st.NGen.Next();
        m_lctx = KX.LocalCtxMkLetDecl(m_lctx, RC.Own(n.Raw), RC.Own(un.Raw), RC.Own(type.Raw), RC.Own(value.Raw), 0);
        return Expr.MkFVar(n);
    }

    LocalDecl FindLocalDecl(Expr e)
    {
        Obj o = KX.LocalCtxFind(RC.Own(m_lctx), RC.Own(e.FVarName.Raw));
        if (lean_is_scalar(o)) return default;
        return new LocalDecl(lean_ctor_get(o, 0));
    }

    Obj SaveLCtx() { lean_inc(m_lctx); return m_lctx; }

    void RestoreLCtx(Obj saved)
    {
        lean_dec(m_lctx);
        m_lctx = saved;
    }

    Expr MkPi(List<Expr> fvars, Expr e, bool removeDeadLet = false)
    {
        var lctx = new LocalCtx(m_lctx); // borrowed view: only used for lookups
        return lctx.MkPi(fvars, e, removeDeadLet);
    }

    // ---------------------------------------------------------------------------------------

    Expr EnsureSortCore(Expr e, Expr s)
    {
        if (e.IsSort) return e;
        Expr newE = Whnf(e);
        if (newE.IsSort) return newE;
        throw new TypeExpectedException(m_st.EnvObj, m_lctx, s);
    }

    Expr EnsurePiCore(Expr e, Expr s)
    {
        if (e.IsPi) return e;
        Expr newE = Whnf(e);
        if (newE.IsPi) return newE;
        throw new FunctionExpectedException(m_st.EnvObj, m_lctx, s);
    }

    void CheckLevel(Level l)
    {
        if (m_lparams != null)
        {
            Name? n2 = Level.GetUndefParam(l, m_lparams);
            if (n2.HasValue)
                throw new KernelException(m_st.EnvObj, "invalid reference to undefined universe level parameter '" + n2.Value + "'");
        }
    }

    Expr InferFVar(Expr e)
    {
        LocalDecl decl = FindLocalDecl(e);
        if (!decl.IsNull) return decl.Type;
        throw new KernelException(m_st.EnvObj, "unknown free variable");
    }

    Expr InferConstant(Expr e, bool inferOnly)
    {
        ConstantInfo info = Env.Get(e.ConstName);
        Obj ps = info.LParams;
        Obj ls = e.ConstLevels;
        int nps = KList.Length(ps), nls = KList.Length(ls);
        if (nps != nls)
            throw new KernelException(m_st.EnvObj, "incorrect number of universe levels parameters for '" + e.ConstName + "', #" + nps + " expected, #" + nls + " provided");
        if (!inferOnly)
        {
            if (info.IsUnsafe && m_definitionSafety != DefinitionSafety.Unsafe)
                throw new KernelException(m_st.EnvObj, "invalid declaration, it uses unsafe declaration '" + e.ConstName + "'");
            if (info.IsDefinition && info.ToDefinitionVal().Safety == DefinitionSafety.Partial && m_definitionSafety == DefinitionSafety.Safe)
                throw new KernelException(m_st.EnvObj, "invalid declaration, safe declaration must not contain partial declaration '" + e.ConstName + "'");
            foreach (var l in KList.Iter(ls)) CheckLevel(new Level(l));
        }
        return Inst.InstantiateTypeLParams(info, ls);
    }

    Expr InferLambda(Expr e0, bool inferOnly)
    {
        Obj saved = SaveLCtx();
        try
        {
            var fvars = new List<Expr>();
            Expr e = e0;
            while (e.IsLambda)
            {
                Expr d = Inst.InstantiateRev(e.BindingDomain, fvars.Count, fvars);
                if (!inferOnly)
                    EnsureSortCore(InferTypeCore(d, inferOnly), d);
                Expr fvar = MkLocalDecl(e.BindingName, d, e.BindingInfo);
                fvars.Add(fvar);
                e = e.BindingBody;
            }
            Expr r = InferTypeCore(Inst.InstantiateRev(e, fvars.Count, fvars), inferOnly);
            r = Inst.CheapBetaReduce(r);
            return MkPi(fvars, r);
        }
        finally { RestoreLCtx(saved); }
    }

    Expr InferPi(Expr e0, bool inferOnly)
    {
        Obj saved = SaveLCtx();
        try
        {
            var fvars = new List<Expr>();
            var us = new List<Level>();
            Expr e = e0;
            while (e.IsPi)
            {
                Expr d = Inst.InstantiateRev(e.BindingDomain, fvars.Count, fvars);
                Expr t1 = EnsureSortCore(InferTypeCore(d, inferOnly), d);
                us.Add(t1.SortLevel);
                Expr fvar = MkLocalDecl(e.BindingName, d, e.BindingInfo);
                fvars.Add(fvar);
                e = e.BindingBody;
            }
            e = Inst.InstantiateRev(e, fvars.Count, fvars);
            Expr s = EnsureSortCore(InferTypeCore(e, inferOnly), e);
            Level r = s.SortLevel;
            int i = fvars.Count;
            while (i > 0)
            {
                --i;
                r = Level.MkIMax(us[i], r);
            }
            return Expr.MkSort(r);
        }
        finally { RestoreLCtx(saved); }
    }

    static bool IsEagerReduce(Expr e) => Expr.GetAppFn(e).IsConstOf(KConsts.EagerReduce) && Expr.GetAppNumArgs(e) == 2;

    Expr InferApp(Expr e, bool inferOnly)
    {
        if (!inferOnly)
        {
            Expr fType = EnsurePiCore(InferTypeCore(e.AppFn, inferOnly), e);
            Expr aType = InferTypeCore(e.AppArg, inferOnly);
            Expr dType = fType.BindingDomain;
            if (IsEagerReduce(e.AppArg))
            {
                bool old = m_eagerReduce;
                m_eagerReduce = true;
                try
                {
                    if (!IsDefEq(aType, dType))
                        throw new AppTypeMismatchException(m_st.EnvObj, m_lctx, e, fType, aType);
                }
                finally { m_eagerReduce = old; }
            }
            else if (!IsDefEq(aType, dType))
            {
                throw new AppTypeMismatchException(m_st.EnvObj, m_lctx, e, fType, aType);
            }
            return Inst.Instantiate(fType.BindingBody, e.AppArg);
        }
        else
        {
            var args = new List<Expr>();
            Expr f = Expr.GetAppArgs(e, args);
            Expr fType = InferTypeCore(f, true);
            int j = 0;
            int nargs = args.Count;
            for (int i = 0; i < nargs; i++)
            {
                if (fType.IsPi)
                {
                    fType = fType.BindingBody;
                }
                else
                {
                    fType = Inst.InstantiateRev(fType, i - j, args, j);
                    fType = EnsurePiCore(fType, e);
                    fType = fType.BindingBody;
                    j = i;
                }
            }
            return Inst.InstantiateRev(fType, nargs - j, args, j);
        }
    }

    Expr InferLet(Expr e0, bool inferOnly)
    {
        Obj saved = SaveLCtx();
        try
        {
            var fvars = new List<Expr>();
            Expr e = e0;
            while (e.IsLet)
            {
                Expr type = Inst.InstantiateRev(e.LetType, fvars.Count, fvars);
                Expr val = Inst.InstantiateRev(e.LetValue, fvars.Count, fvars);
                if (!inferOnly)
                {
                    EnsureSortCore(InferTypeCore(type, inferOnly), type);
                    Expr valType = InferTypeCore(val, inferOnly);
                    if (!IsDefEq(valType, type))
                        throw new DefTypeMismatchException(m_st.EnvObj, m_lctx, e.LetName, valType, type);
                }
                Expr fvar = MkLetDecl(e.LetName, type, val);
                fvars.Add(fvar);
                e = e.LetBody;
            }
            Expr r = InferTypeCore(Inst.InstantiateRev(e, fvars.Count, fvars), inferOnly);
            r = Inst.CheapBetaReduce(r);
            return MkPi(fvars, r, true);
        }
        finally { RestoreLCtx(saved); }
    }

    /// <summary>Store the projection index in `result`; false if it does not fit in 32 bits.</summary>
    static bool ToProjIdx(Obj idx, out uint result)
    {
        result = 0;
        if (!lean_is_scalar(idx)) return false;
        ulong v = lean_unbox(idx);
        if (v > uint.MaxValue) return false;
        result = (uint)v;
        return true;
    }

    Expr InferProj(Expr e, bool inferOnly)
    {
        Expr type = Whnf(InferTypeCore(e.ProjExpr, inferOnly));
        if (!ToProjIdx(e.ProjIdx, out uint idx))
            throw new InvalidProjException(m_st.EnvObj, m_lctx, e);
        var args = new List<Expr>();
        Expr I = Expr.GetAppArgs(type, args);
        if (!I.IsConst)
            throw new InvalidProjException(m_st.EnvObj, m_lctx, e);
        Name IName = I.ConstName;
        if (IName != e.ProjSName)
            throw new InvalidProjException(m_st.EnvObj, m_lctx, e);
        ConstantInfo IInfo = Env.Get(IName);
        if (!IInfo.IsInductive)
            throw new InvalidProjException(m_st.EnvObj, m_lctx, e);
        InductiveVal IVal = IInfo.ToInductiveVal();
        if (KList.Length(IVal.Cnstrs) != 1 || args.Count != IVal.NParams + IVal.NIndices)
            throw new InvalidProjException(m_st.EnvObj, m_lctx, e);

        ConstantInfo cInfo = Env.Get(new Name(KList.Head(IVal.Cnstrs)));
        Expr r = Inst.InstantiateTypeLParams(cInfo, I.ConstLevels);
        for (int i = 0; i < IVal.NParams; i++)
        {
            r = Whnf(r);
            if (!r.IsPi) throw new InvalidProjException(m_st.EnvObj, m_lctx, e);
            r = Inst.Instantiate(r.BindingBody, args[i]);
        }
        bool isPropType = IsProp(type);
        for (uint i = 0; i < idx; i++)
        {
            r = Whnf(r);
            if (!r.IsPi) throw new InvalidProjException(m_st.EnvObj, m_lctx, e);
            if (r.BindingBody.HasLooseBVars)
            {
                if (isPropType && !IsProp(r.BindingDomain))
                    throw new InvalidProjException(m_st.EnvObj, m_lctx, e);
                r = Inst.Instantiate(r.BindingBody, Expr.MkProj(IName, i, e.ProjExpr));
            }
            else
            {
                r = r.BindingBody;
            }
        }
        r = Whnf(r);
        if (!r.IsPi) throw new InvalidProjException(m_st.EnvObj, m_lctx, e);
        r = r.BindingDomain;
        if (isPropType && !IsProp(r))
            throw new InvalidProjException(m_st.EnvObj, m_lctx, e);
        return r;
    }

    static void CheckNatSize(Environment env, ulong numBytes)
    {
        if (numBytes > CurrentNatMaxSize)
            throw new KernelException(env.Raw, "the kernel refused a `Nat` numeral because its size exceeds the maximum; increase the LEAN_NAT_MAX_SIZE environment variable to allow it");
    }

    static ulong GetCountArg(Environment env, Obj count, string op)
    {
        if (!lean_is_scalar(count) || lean_unbox(count) > uint.MaxValue)
            throw new KernelException(env.Raw, "the kernel refused to evaluate `" + op + "` because its second argument does not fit in a 32-bit unsigned integer");
        return lean_unbox(count);
    }

    Expr InferLit(Expr e)
    {
        if (e.IsNatLit) CheckNatSize(Env, Nat.SizeInBytes(e.LitNat));
        return Expr.LitType(e.LitValue);
    }

    /// <summary>Return the type of `e`; if `inferOnly` is false, also check that `e` is type correct.</summary>
    Expr InferTypeCore(Expr e, bool inferOnly)
    {
        if (e.HasLooseBVars)
            throw new KernelException(m_st.EnvObj, "type checker does not support loose bound variables, replace them with free variables before invoking it");

        KernelLimits.EnterRecDepth();
        try
        {
            KernelLimits.CheckSystem("type checker", true);

            var cache = m_st.InferType[inferOnly ? 1 : 0];
            if (cache.TryGetValue(e, out var cached)) return cached;

            Expr r;
            switch (e.Kind)
            {
                case ExprKind.Lit: r = InferLit(e); break;
                case ExprKind.MData: r = InferTypeCore(e.MDataExpr, inferOnly); break;
                case ExprKind.Proj: r = InferProj(e, inferOnly); break;
                case ExprKind.FVar: r = InferFVar(e); break;
                case ExprKind.MVar: throw new KernelException(m_st.EnvObj, "kernel type checker does not support meta variables");
                case ExprKind.BVar: throw lean_internal_panic_unreachable();
                case ExprKind.Sort:
                    if (!inferOnly) CheckLevel(e.SortLevel);
                    r = Expr.MkSort(Level.MkSucc(e.SortLevel));
                    break;
                case ExprKind.Const: r = InferConstant(e, inferOnly); break;
                case ExprKind.Lambda: r = InferLambda(e, inferOnly); break;
                case ExprKind.Pi: r = InferPi(e, inferOnly); break;
                case ExprKind.App: r = InferApp(e, inferOnly); break;
                case ExprKind.Let: r = InferLet(e, inferOnly); break;
                default: throw lean_internal_panic_unreachable();
            }
            cache.TryAdd(e, r);
            return r;
        }
        finally { KernelLimits.LeaveRecDepth(); }
    }

    Expr InferType(Expr e) => InferTypeCore(e, true);

    // ---------------------------------------------------------------------------------------
    // Public API

    public Expr Infer(Expr t) => InferType(t);

    public Expr Check(Expr e, Obj lps)
    {
        Obj old = m_lparams;
        m_lparams = lps;
        try { return InferTypeCore(e, false); }
        finally { m_lparams = old; }
    }

    /// <summary>`check(e)`: like `Check` but ignores undefined universes.</summary>
    public Expr Check(Expr e)
    {
        Obj old = m_lparams;
        m_lparams = null;
        try { return InferTypeCore(e, false); }
        finally { m_lparams = old; }
    }

    public Expr EnsureSort(Expr e, Expr s) => EnsureSortCore(e, s);
    public Expr EnsureSort(Expr e) => EnsureSortCore(e, e);
    public Expr EnsureType(Expr e) => EnsureSort(Infer(e), e);

    public bool IsProp(Expr e)
    {
        Expr s = EnsureSort(InferType(e));
        return Level.NormalizesToZero(s.SortLevel);
    }

    // ---------------------------------------------------------------------------------------
    // Weak head normal form

    Expr ReduceRecursor(Expr e, bool cheapRec, bool cheapProj)
    {
        if (Env.IsQuotInitialized)
        {
            Expr r = Quot.QuotReduceRec(e, x => Whnf(x));
            if (r.IsSome) return r;
        }
        Expr r2 = Inductive.InductiveReduceRec(Env, e,
            x => cheapRec ? WhnfCore(x, cheapRec, cheapProj) : Whnf(x),
            x => Infer(x),
            (a, b) => IsDefEq(a, b),
            x => IsProp(x));
        if (r2.IsSome) return r2;
        return Expr.None;
    }

    Expr WhnfFVar(Expr e, bool cheapRec, bool cheapProj)
    {
        LocalDecl decl = FindLocalDecl(e);
        if (!decl.IsNull)
        {
            Expr v = decl.Value;
            if (v.IsSome) return WhnfCore(v, cheapRec, cheapProj);
        }
        return e;
    }

    Expr ReduceProjCore(Expr c, Name sname, uint idx)
    {
        if (c.IsStringLit)
            c = Whnf(Inductive.StringLitToConstructor(c));
        var args = new List<Expr>();
        Expr mk = Expr.GetAppArgs(c, args);
        if (!mk.IsConst) return Expr.None;
        ConstantInfo mkInfo = Env.Get(mk.ConstName);
        if (!mkInfo.IsConstructor) return Expr.None;
        ConstructorVal mkVal = mkInfo.ToConstructorVal();
        if (mkVal.Induct != sname) return Expr.None;
        uint nparams = mkVal.NParams;
        if ((ulong)nparams + idx < (ulong)args.Count)
            return args[(int)(nparams + idx)];
        return Expr.None;
    }

    Expr ReduceProj(Expr e, bool cheapRec, bool cheapProj)
    {
        if (!ToProjIdx(e.ProjIdx, out uint idx)) return Expr.None;
        Expr c = cheapProj ? WhnfCore(e.ProjExpr, cheapRec, cheapProj) : Whnf(e.ProjExpr);
        return ReduceProjCore(c, e.ProjSName, idx);
    }

    bool IsLetFVar(Expr e)
    {
        LocalDecl decl = FindLocalDecl(e);
        return !decl.IsNull && decl.Value.IsSome;
    }

    /// <summary>Weak head normal form core procedure (no delta reduction, no normalizer extensions).</summary>
    public Expr WhnfCore(Expr e, bool cheapRec = false, bool cheapProj = false)
    {
        KernelLimits.EnterRecDepth();
        try
        {
            KernelLimits.CheckSystem("type checker: whnf", true);

            switch (e.Kind)
            {
                case ExprKind.BVar: case ExprKind.Sort: case ExprKind.MVar:
                case ExprKind.Pi: case ExprKind.Const: case ExprKind.Lambda:
                case ExprKind.Lit:
                    return e;
                case ExprKind.MData:
                    return WhnfCore(e.MDataExpr, cheapRec, cheapProj);
                case ExprKind.FVar:
                    if (IsLetFVar(e)) break;
                    return e;
            }

            if (m_st.WhnfCore.TryGetValue(e, out var cached)) return cached;

            Expr r;
            switch (e.Kind)
            {
                case ExprKind.FVar:
                    return WhnfFVar(e, cheapRec, cheapProj);
                case ExprKind.Proj:
                {
                    Expr m = ReduceProj(e, cheapRec, cheapProj);
                    r = m.IsSome ? WhnfCore(m, cheapRec, cheapProj) : e;
                    break;
                }
                case ExprKind.App:
                {
                    var args = new List<Expr>();
                    Expr f0 = Expr.GetAppRevArgs(e, args);
                    Expr f = WhnfCore(f0, cheapRec, cheapProj);
                    if (f.IsLambda)
                    {
                        int m = 1;
                        int numArgs = args.Count;
                        while (f.BindingBody.IsLambda && m < numArgs)
                        {
                            f = f.BindingBody;
                            m++;
                        }
                        r = WhnfCore(Expr.MkRevApp(Inst.Instantiate(f.BindingBody, (uint)m, args, numArgs - m), numArgs - m, args), cheapRec, cheapProj);
                    }
                    else if (f == f0)
                    {
                        Expr red = ReduceRecursor(e, cheapRec, cheapProj);
                        if (red.IsSome)
                        {
                            if (m_diag != null)
                            {
                                Expr fn = Expr.GetAppFn(e);
                                if (fn.IsConst) m_diag.RecordUnfold(fn.ConstName);
                            }
                            return WhnfCore(red, cheapRec, cheapProj);
                        }
                        return e;
                    }
                    else
                    {
                        r = WhnfCore(Expr.MkRevApp(f, args), cheapRec, cheapProj);
                    }
                    break;
                }
                case ExprKind.Let:
                    r = WhnfCore(Inst.Instantiate(e.LetBody, e.LetValue), cheapRec, cheapProj);
                    break;
                default:
                    throw lean_internal_panic_unreachable();
            }

            if (!cheapRec && !cheapProj)
                m_st.WhnfCore.TryAdd(e, r);
            return r;
        }
        finally { KernelLimits.LeaveRecDepth(); }
    }

    public Expr WhnfCoreCheap(Expr e) => WhnfCore(e, true, true);

    ConstantInfo IsDelta(Expr e)
    {
        Expr f = Expr.GetAppFn(e);
        if (f.IsConst)
        {
            ConstantInfo info = Env.Find(f.ConstName);
            if (!info.IsNull && info.HasValue() && KList.Length(f.ConstLevels) == info.NumLParams)
                return info;
        }
        return default;
    }

    Expr UnfoldDefinitionCore(Expr e)
    {
        if (e.IsConst)
        {
            ConstantInfo d = IsDelta(e);
            if (!d.IsNull)
            {
                Obj us = e.ConstLevels;
                int len = KList.Length(us);
                if (m_diag != null) m_diag.RecordUnfold(d.Name);
                if (len > 0)
                {
                    if (m_st.Unfold.TryGetValue(e, out var cached)) return cached;
                    Expr result = Inst.InstantiateValueLParams(d, us);
                    m_st.Unfold.TryAdd(e, result);
                    return result;
                }
                return Inst.InstantiateValueLParams(d, us);
            }
        }
        return Expr.None;
    }

    /// <summary>Unfold the head of `e` if it is a constant with a value.</summary>
    public Expr UnfoldDefinition(Expr e)
    {
        if (e.IsApp)
        {
            Expr f0 = Expr.GetAppFn(e);
            Expr f = UnfoldDefinitionCore(f0);
            if (f.IsSome)
            {
                var args = new List<Expr>();
                Expr.GetAppRevArgs(e, args);
                return Expr.MkRevApp(f, args);
            }
            return Expr.None;
        }
        return UnfoldDefinitionCore(e);
    }

    static bool IsNatLitExt(Expr e) => e == KConsts.NatZero || e.IsNatLit;

    static Obj GetNatVal(Expr e)
    {
        if (e == KConsts.NatZero) return lean_box(0);
        return e.LitNat;
    }

    Expr ReduceBinNatOp(Func<BigInteger, BigInteger, BigInteger> f, Expr e, bool checkSize = false)
    {
        Expr arg1 = Whnf(e.AppFn.AppArg);
        if (!IsNatLitExt(arg1)) return Expr.None;
        Expr arg2 = Whnf(e.AppArg);
        if (!IsNatLitExt(arg2)) return Expr.None;
        Obj v1 = GetNatVal(arg1);
        Obj v2 = GetNatVal(arg2);
        Obj r = Nat.OfBig(f(Nat.ToBig(v1), Nat.ToBig(v2)));
        if (checkSize) CheckNatSize(Env, Nat.SizeInBytes(r));
        return Expr.MkLit(Expr.MkNatLiteral(r));
    }

    Expr ReducePow(Expr e)
    {
        Expr arg1 = Whnf(e.AppFn.AppArg);
        if (!IsNatLitExt(arg1)) return Expr.None;
        Expr arg2 = Whnf(e.AppArg);
        if (!IsNatLitExt(arg2)) return Expr.None;
        Obj nbase = GetNatVal(arg1);
        Obj nexp = GetNatVal(arg2);
        ulong k = GetCountArg(Env, nexp, "Nat.pow");
        BigInteger b = Nat.ToBig(nbase);
        if (b > 1 && k != 0 && Nat.SizeInBytes(nbase) > CurrentNatMaxSize / k)
            throw new KernelException(m_st.EnvObj, "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size; increase the LEAN_NAT_MAX_SIZE environment variable to allow it");
        BigInteger r;
        if (k == 0) r = BigInteger.One;
        else if (b.IsZero) r = BigInteger.Zero;
        else if (b.IsOne) r = BigInteger.One;
        else if (k > int.MaxValue)
            throw new KernelException(m_st.EnvObj, "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size; increase the LEAN_NAT_MAX_SIZE environment variable to allow it");
        else r = BigInteger.Pow(b, (int)k);
        return Expr.MkLit(Expr.MkNatLiteral(Nat.OfBig(r)));
    }

    Expr ReduceShiftLeft(Expr e)
    {
        Expr arg1 = Whnf(e.AppFn.AppArg);
        if (!IsNatLitExt(arg1)) return Expr.None;
        Expr arg2 = Whnf(e.AppArg);
        if (!IsNatLitExt(arg2)) return Expr.None;
        Obj v = GetNatVal(arg1);
        Obj shift = GetNatVal(arg2);
        if (!Nat.IsZero(v))
        {
            ulong k = GetCountArg(Env, shift, "Nat.shiftLeft");
            CheckNatSize(Env, Nat.SizeInBytes(v) + k / 8 + 1);
            if (k > int.MaxValue) CheckNatSize(Env, ulong.MaxValue);
            return Expr.MkLit(Expr.MkNatLiteral(Nat.OfBig(Nat.ToBig(v) << (int)k)));
        }
        return Expr.MkLit(Expr.MkNatLiteral(lean_box(0)));
    }

    Expr ReduceBinNatPred(Func<BigInteger, BigInteger, bool> f, Expr e)
    {
        Expr arg1 = Whnf(e.AppFn.AppArg);
        if (!IsNatLitExt(arg1)) return Expr.None;
        Expr arg2 = Whnf(e.AppArg);
        if (!IsNatLitExt(arg2)) return Expr.None;
        Obj v1 = GetNatVal(arg1);
        Obj v2 = GetNatVal(arg2);
        return f(Nat.ToBig(v1), Nat.ToBig(v2)) ? KConsts.BoolTrueExpr : KConsts.BoolFalseExpr;
    }

    static BigInteger NatSub(BigInteger a, BigInteger b) => a >= b ? a - b : BigInteger.Zero;
    static BigInteger NatDiv(BigInteger a, BigInteger b) => b.IsZero ? BigInteger.Zero : BigInteger.Divide(a, b);
    static BigInteger NatMod(BigInteger a, BigInteger b) => b.IsZero ? a : BigInteger.Remainder(a, b);
    static BigInteger NatShiftRight(BigInteger a, BigInteger b) => b > int.MaxValue ? BigInteger.Zero : a >> (int)b;

    Expr ReduceNat(Expr e)
    {
        uint nargs = Expr.GetAppNumArgs(e);
        if (nargs == 1)
        {
            Expr f = e.AppFn;
            if (f == KConsts.NatSucc)
            {
                Expr arg = Whnf(e.AppArg);
                if (!IsNatLitExt(arg)) return Expr.None;
                Obj v = Nat.Add(GetNatVal(arg), 1);
                CheckNatSize(Env, Nat.SizeInBytes(v));
                return Expr.MkLit(Expr.MkNatLiteral(v));
            }
        }
        else if (nargs == 2)
        {
            Expr f = e.AppFn.AppFn;
            if (!f.IsConst) return Expr.None;
            if (f == KConsts.NatAdd) return ReduceBinNatOp((a, b) => a + b, e, true);
            if (f == KConsts.NatSub) return ReduceBinNatOp(NatSub, e, true);
            if (f == KConsts.NatMul) return ReduceBinNatOp((a, b) => a * b, e, true);
            if (f == KConsts.NatPow) return ReducePow(e);
            if (f == KConsts.NatGcd) return ReduceBinNatOp(BigInteger.GreatestCommonDivisor, e);
            if (f == KConsts.NatMod) return ReduceBinNatOp(NatMod, e);
            if (f == KConsts.NatDiv) return ReduceBinNatOp(NatDiv, e);
            if (f == KConsts.NatBeq) return ReduceBinNatPred((a, b) => a == b, e);
            if (f == KConsts.NatBle) return ReduceBinNatPred((a, b) => a <= b, e);
            if (f == KConsts.NatLand) return ReduceBinNatOp((a, b) => a & b, e);
            if (f == KConsts.NatLor) return ReduceBinNatOp((a, b) => a | b, e);
            if (f == KConsts.NatXor) return ReduceBinNatOp((a, b) => a ^ b, e);
            if (f == KConsts.NatShiftLeft) return ReduceShiftLeft(e);
            if (f == KConsts.NatShiftRight) return ReduceBinNatOp(NatShiftRight, e);
        }
        return Expr.None;
    }

    /// <summary>Put `e` in weak head normal form.</summary>
    public Expr Whnf(Expr e)
    {
        switch (e.Kind)
        {
            case ExprKind.BVar: case ExprKind.Sort: case ExprKind.MVar: case ExprKind.Pi:
            case ExprKind.Lit:
                return e;
            case ExprKind.MData:
                return Whnf(e.MDataExpr);
            case ExprKind.FVar:
                if (IsLetFVar(e)) break;
                return e;
        }

        if (m_st.Whnf.TryGetValue(e, out var cached)) return cached;

        Expr t = e;
        while (true)
        {
            Expr t1 = WhnfCore(t);
            Expr v = ReduceNat(t1);
            if (v.IsSome)
            {
                m_st.Whnf.TryAdd(e, v);
                return v;
            }
            Expr nextT = UnfoldDefinition(t1);
            if (nextT.IsSome)
            {
                t = nextT;
            }
            else
            {
                m_st.Whnf.TryAdd(e, t1);
                return t1;
            }
        }
    }

    // ---------------------------------------------------------------------------------------
    // Definitional equality

    bool IsDefEqBinding(Expr t, Expr s)
    {
        Obj saved = SaveLCtx();
        try
        {
            ExprKind k = t.Kind;
            var subst = new List<Expr>();
            do
            {
                Expr varSType = Expr.None;
                if (t.BindingDomain != s.BindingDomain)
                {
                    varSType = Inst.InstantiateRev(s.BindingDomain, subst.Count, subst);
                    Expr varTType = Inst.InstantiateRev(t.BindingDomain, subst.Count, subst);
                    if (!IsDefEq(varTType, varSType)) return false;
                }
                if (t.BindingBody.HasLooseBVars || s.BindingBody.HasLooseBVars)
                {
                    if (varSType.IsNull)
                        varSType = Inst.InstantiateRev(s.BindingDomain, subst.Count, subst);
                    subst.Add(MkLocalDecl(s.BindingName, varSType, s.BindingInfo));
                }
                else
                {
                    subst.Add(KConsts.DontCare);
                }
                t = t.BindingBody;
                s = s.BindingBody;
            } while (t.Kind == k && s.Kind == k);
            return IsDefEq(Inst.InstantiateRev(t, subst.Count, subst), Inst.InstantiateRev(s, subst.Count, subst));
        }
        finally { RestoreLCtx(saved); }
    }

    bool IsDefEq(Level l1, Level l2) => Level.IsEquivalent(l1, l2);

    bool IsDefEqLevels(Obj ls1, Obj ls2)
    {
        while (true)
        {
            if (KList.IsNil(ls1) && KList.IsNil(ls2)) return true;
            if (KList.IsNil(ls1) || KList.IsNil(ls2)) return false;
            if (!IsDefEq(new Level(KList.Head(ls1)), new Level(KList.Head(ls2)))) return false;
            ls1 = KList.Tail(ls1);
            ls2 = KList.Tail(ls2);
        }
    }

    static LBool ToLBool(bool b) => b ? LBool.True : LBool.False;

    LBool QuickIsDefEq(Expr t, Expr s)
    {
        if (t == s || SucceededBefore(t, s)) return LBool.True;
        if (t.Kind == s.Kind)
        {
            switch (t.Kind)
            {
                case ExprKind.Lambda: case ExprKind.Pi:
                    return ToLBool(IsDefEqBinding(t, s));
                case ExprKind.Sort:
                    return ToLBool(IsDefEq(t.SortLevel, s.SortLevel));
                case ExprKind.MData:
                    return ToLBool(IsDefEq(t.MDataExpr, s.MDataExpr));
                case ExprKind.MVar:
                    throw lean_internal_panic_unreachable();
                case ExprKind.Lit:
                    return ToLBool(LiteralEq(t.LitValue, s.LitValue));
            }
        }
        return LBool.Undef;
    }

    static bool LiteralEq(Obj a, Obj b)
    {
        uint ka = lean_obj_tag(a), kb = lean_obj_tag(b);
        if (ka != kb) return false;
        if (ka == 1) return Name.StringEq(lean_ctor_get(a, 0), lean_ctor_get(b, 0));
        return Nat.Eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0));
    }

    bool IsDefEqArgs(Expr t, Expr s)
    {
        while (t.IsApp && s.IsApp)
        {
            if (!IsDefEq(t.AppArg, s.AppArg)) return false;
            t = t.AppFn;
            s = s.AppFn;
        }
        return !t.IsApp && !s.IsApp;
    }

    bool TryEtaExpansionCore(Expr t, Expr s)
    {
        if (t.IsLambda && !s.IsLambda)
        {
            Expr sType = Whnf(InferType(s));
            if (!sType.IsPi) return false;
            Expr newS = Expr.MkLambda(sType.BindingName, sType.BindingDomain, Expr.MkApp(s, Expr.MkBVar(0)), sType.BindingInfo);
            return IsDefEq(t, newS);
        }
        return false;
    }

    bool TryEtaExpansion(Expr t, Expr s) => TryEtaExpansionCore(t, s) || TryEtaExpansionCore(s, t);

    bool TryEtaStructCore(Expr t, Expr s)
    {
        Expr f = Expr.GetAppFn(s);
        if (!f.IsConst) return false;
        ConstantInfo fInfo = Env.Get(f.ConstName);
        if (!fInfo.IsConstructor) return false;
        ConstructorVal fVal = fInfo.ToConstructorVal();
        if (Expr.GetAppNumArgs(s) != fVal.NParams + fVal.NFields) return false;
        if (!Inductive.IsNonRecStructure(Env, fVal.Induct)) return false;
        if (!IsDefEq(InferType(t), InferType(s))) return false;
        var sArgs = new List<Expr>();
        Expr.GetAppArgs(s, sArgs);
        for (int i = (int)fVal.NParams; i < sArgs.Count; i++)
        {
            Expr proj = Expr.MkProj(fVal.Induct, (ulong)(i - (int)fVal.NParams), t);
            if (!IsDefEq(proj, sArgs[i])) return false;
        }
        return true;
    }

    bool TryEtaStruct(Expr t, Expr s) => TryEtaStructCore(t, s) || TryEtaStructCore(s, t);

    bool IsDefEqApp(Expr t, Expr s)
    {
        if (t.IsApp && s.IsApp)
        {
            var tArgs = new List<Expr>();
            var sArgs = new List<Expr>();
            Expr tFn = Expr.GetAppArgs(t, tArgs);
            Expr sFn = Expr.GetAppArgs(s, sArgs);
            if (IsDefEq(tFn, sFn) && tArgs.Count == sArgs.Count)
            {
                int i = 0;
                for (; i < tArgs.Count; i++)
                    if (!IsDefEq(tArgs[i], sArgs[i])) break;
                if (i == tArgs.Count) return true;
            }
        }
        return false;
    }

    LBool IsDefEqProofIrrel(Expr t, Expr s)
    {
        Expr tType = InferType(t);
        if (!IsProp(tType)) return LBool.Undef;
        Expr sType = InferType(s);
        return ToLBool(IsDefEq(tType, sType));
    }

    bool FailedBefore(Expr t, Expr s)
    {
        uint ht = t.Hash, hs = s.Hash;
        if (ht < hs) return m_st.Failure.Contains((t, s));
        if (ht > hs) return m_st.Failure.Contains((s, t));
        return m_st.Failure.Contains((t, s)) || m_st.Failure.Contains((s, t));
    }

    void CacheFailure(Expr t, Expr s)
    {
        if (t.Hash <= s.Hash) m_st.Failure.Add((t, s));
        else m_st.Failure.Add((s, t));
    }

    bool SucceededBefore(Expr t, Expr s)
    {
        uint ht = t.Hash, hs = s.Hash;
        if (ht < hs) return m_st.Success.Contains((t, s));
        if (ht > hs) return m_st.Success.Contains((s, t));
        return m_st.Success.Contains((t, s)) || m_st.Success.Contains((s, t));
    }

    void CacheSuccess(Expr t, Expr s)
    {
        if (t.Hash <= s.Hash) m_st.Success.Add((t, s));
        else m_st.Success.Add((s, t));
    }

    Expr TryUnfoldProjApp(Expr e)
    {
        Expr f = Expr.GetAppFn(e);
        if (f.IsProj)
        {
            Expr eNew = WhnfCore(e);
            return eNew != e ? eNew : Expr.None;
        }
        return Expr.None;
    }

    ReductionStatus LazyDeltaReductionStep(ref Expr tn, ref Expr sn)
    {
        ConstantInfo dt = IsDelta(tn);
        ConstantInfo ds = IsDelta(sn);
        if (dt.IsNull && ds.IsNull)
        {
            return ReductionStatus.DefUnknown;
        }
        else if (!dt.IsNull && ds.IsNull)
        {
            Expr snNew = TryUnfoldProjApp(sn);
            if (snNew.IsSome) sn = snNew;
            else tn = WhnfCore(UnfoldDefinition(tn), false, true);
        }
        else if (dt.IsNull && !ds.IsNull)
        {
            Expr tnNew = TryUnfoldProjApp(tn);
            if (tnNew.IsSome) tn = tnNew;
            else sn = WhnfCore(UnfoldDefinition(sn), false, true);
        }
        else
        {
            int c = ReducibilityHints.Compare(dt.Hints, ds.Hints);
            if (c < 0)
            {
                tn = WhnfCore(UnfoldDefinition(tn), false, true);
            }
            else if (c > 0)
            {
                sn = WhnfCore(UnfoldDefinition(sn), false, true);
            }
            else
            {
                if (tn.IsApp && sn.IsApp && ReferenceEquals(dt.Raw, ds.Raw) && ReducibilityHints.IsRegular(dt.Hints))
                {
                    if (!FailedBefore(tn, sn))
                    {
                        if (IsDefEqLevels(Expr.GetAppFn(tn).ConstLevels, Expr.GetAppFn(sn).ConstLevels) && IsDefEqArgs(tn, sn))
                            return ReductionStatus.DefEqual;
                        CacheFailure(tn, sn);
                    }
                }
                tn = WhnfCore(UnfoldDefinition(tn), false, true);
                sn = WhnfCore(UnfoldDefinition(sn), false, true);
            }
        }
        switch (QuickIsDefEq(tn, sn))
        {
            case LBool.True: return ReductionStatus.DefEqual;
            case LBool.False: return ReductionStatus.DefDiff;
            default: return ReductionStatus.Continue;
        }
    }

    static bool IsNatZero(Expr t) => t == KConsts.NatZero || (t.IsNatLit && Nat.IsZero(t.LitNat));

    static Expr IsNatSucc(Expr t)
    {
        if (t.IsNatLit)
        {
            Obj val = t.LitNat;
            if (!Nat.IsZero(val))
                return Expr.MkLit(Expr.MkNatLiteral(Nat.Sub(val, 1)));
        }
        if (Expr.GetAppFn(t) == KConsts.NatSucc && Expr.GetAppNumArgs(t) == 1)
            return t.AppArg;
        return Expr.None;
    }

    LBool IsDefEqOffset(Expr t, Expr s)
    {
        if (IsNatZero(t) && IsNatZero(s)) return LBool.True;
        Expr predT = IsNatSucc(t);
        Expr predS = IsNatSucc(s);
        if (predT.IsSome && predS.IsSome)
            return ToLBool(IsDefEqCore(predT, predS));
        return LBool.Undef;
    }

    LBool LazyDeltaReduction(ref Expr tn, ref Expr sn)
    {
        while (true)
        {
            LBool r = IsDefEqOffset(tn, sn);
            if (r != LBool.Undef) return r;

            if ((!tn.HasFVar && !sn.HasFVar) || m_eagerReduce)
            {
                Expr tv = ReduceNat(tn);
                if (tv.IsSome) return ToLBool(IsDefEqCore(tv, sn));
                Expr sv = ReduceNat(sn);
                if (sv.IsSome) return ToLBool(IsDefEqCore(tn, sv));
            }

            switch (LazyDeltaReductionStep(ref tn, ref sn))
            {
                case ReductionStatus.Continue: break;
                case ReductionStatus.DefUnknown: return LBool.Undef;
                case ReductionStatus.DefEqual: return LBool.True;
                case ReductionStatus.DefDiff: return LBool.False;
            }
        }
    }

    bool LazyDeltaProjReduction(ref Expr tn, ref Expr sn, Name sname, Obj idx)
    {
        while (true)
        {
            switch (LazyDeltaReductionStep(ref tn, ref sn))
            {
                case ReductionStatus.Continue: break;
                case ReductionStatus.DefEqual: return true;
                case ReductionStatus.DefUnknown:
                case ReductionStatus.DefDiff:
                    if (ToProjIdx(idx, out uint i))
                    {
                        Expr t = ReduceProjCore(tn, sname, i);
                        if (t.IsSome)
                        {
                            Expr s = ReduceProjCore(sn, sname, i);
                            if (s.IsSome) return IsDefEqCore(t, s);
                        }
                    }
                    return IsDefEqCore(tn, sn);
            }
        }
    }

    LBool TryStringLitExpansionCore(Expr t, Expr s)
    {
        if (t.IsStringLit && s.IsApp && s.AppFn == KConsts.StringMk)
            return ToLBool(IsDefEqCore(Whnf(Inductive.StringLitToConstructor(t)), s));
        return LBool.Undef;
    }

    LBool TryStringLitExpansion(Expr t, Expr s)
    {
        LBool r = TryStringLitExpansionCore(t, s);
        if (r != LBool.Undef) return r;
        return TryStringLitExpansionCore(s, t);
    }

    bool IsDefEqUnitLike(Expr t, Expr s)
    {
        Expr tType = Whnf(InferType(t));
        Expr I = Expr.GetAppFn(tType);
        if (!I.IsConst || !Inductive.IsNonRecStructure(Env, I.ConstName)) return false;
        Name ctorName = new Name(KList.Head(Env.Get(I.ConstName).ToInductiveVal().Cnstrs));
        ConstructorVal ctorVal = Env.Get(ctorName).ToConstructorVal();
        if (ctorVal.NFields != 0) return false;
        return IsDefEqCore(tType, InferType(s));
    }

    bool IsDefEqCore(Expr t, Expr s)
    {
        KernelLimits.EnterRecDepth();
        try
        {
            KernelLimits.CheckSystem("is_definitionally_equal", true);
            LBool r = QuickIsDefEq(t, s);
            if (r != LBool.Undef) return r == LBool.True;

            if ((!t.HasFVar || m_eagerReduce) && s.IsConstOf(KConsts.BoolTrue))
            {
                if (Whnf(t).IsConstOf(KConsts.BoolTrue)) return true;
            }

            Expr tn = WhnfCore(t, false, true);
            Expr sn = WhnfCore(s, false, true);

            if (!Expr.IsEqp(tn, t) || !Expr.IsEqp(sn, s))
            {
                r = QuickIsDefEq(tn, sn);
                if (r != LBool.Undef) return r == LBool.True;
            }

            r = IsDefEqProofIrrel(tn, sn);
            if (r != LBool.Undef) return r == LBool.True;

            r = LazyDeltaReduction(ref tn, ref sn);
            if (r != LBool.Undef) return r == LBool.True;

            if (tn.IsConst && sn.IsConst && tn.ConstName == sn.ConstName && IsDefEqLevels(tn.ConstLevels, sn.ConstLevels))
                return true;

            if (tn.IsFVar && sn.IsFVar && tn.FVarName == sn.FVarName)
                return true;

            if (tn.IsProj && sn.IsProj && tn.ProjSName == sn.ProjSName && Nat.Eq(tn.ProjIdx, sn.ProjIdx))
            {
                Expr tc = tn.ProjExpr;
                Expr sc = sn.ProjExpr;
                if (LazyDeltaProjReduction(ref tc, ref sc, tn.ProjSName, tn.ProjIdx))
                    return true;
            }

            Expr tnn = WhnfCore(tn);
            Expr snn = WhnfCore(sn);
            if (!Expr.IsEqp(tnn, tn) || !Expr.IsEqp(snn, sn))
                return IsDefEqCore(tnn, snn);

            if (IsDefEqApp(tn, sn)) return true;
            if (TryEtaExpansion(tn, sn)) return true;
            if (TryEtaStruct(tn, sn)) return true;
            r = TryStringLitExpansion(tn, sn);
            if (r != LBool.Undef) return r == LBool.True;
            if (IsDefEqUnitLike(tn, sn)) return true;
            return false;
        }
        finally { KernelLimits.LeaveRecDepth(); }
    }

    /// <summary>Return true iff `t` is definitionally equal to `s`.</summary>
    public bool IsDefEq(Expr t, Expr s)
    {
        bool r = IsDefEqCore(t, s);
        if (r) CacheSuccess(t, s);
        return r;
    }

    static ulong ReadNatSizeEnv(string var, ulong defaultValue)
    {
        string s = System.Environment.GetEnvironmentVariable(var);
        if (s == null) return defaultValue;
        if (ulong.TryParse(s, System.Globalization.NumberStyles.None, System.Globalization.CultureInfo.InvariantCulture, out ulong v)) return v;
        return defaultValue;
    }
}
