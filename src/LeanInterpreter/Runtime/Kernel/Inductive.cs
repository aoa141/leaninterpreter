// Port of kernel/inductive.{h,cpp}: inductive datatypes (declaration, nested inductive
// elimination, recursor generation) and iota reduction.

using System.Text;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

internal static class Inductive
{
    public static Name MkRecName(Name I) => I + KConsts.RecName;

    public static bool IsNonRecStructure(Environment env, Name declName)
    {
        ConstantInfo I = env.Get(declName);
        if (!I.IsInductive) return false;
        InductiveVal v = I.ToInductiveVal();
        return v.NCnstrs == 1 && v.NIndices == 0 && !v.IsRec;
    }

    public static bool IsConstructor(Environment env, Name n)
    {
        ConstantInfo info = env.Find(n);
        return !info.IsNull && info.IsConstructor;
    }

    public static Name? IsConstructorApp(Environment env, Expr e)
    {
        Expr fn = Expr.GetAppFn(e);
        if (fn.IsConst && IsConstructor(env, fn.ConstName)) return fn.ConstName;
        return null;
    }

    static Obj GetAllInductiveNames(List<Obj> indTypes)
    {
        var all = new List<Obj>();
        foreach (var t in indTypes) all.Add(InductiveType.GetName(t).Raw);
        return KList.OfBorrowed(all);
    }

    static Obj GetAllInductiveNames(Declaration d) => GetAllInductiveNames(KList.ToList(d.IndTypes));

    static Name? GetFirstCnstr(Environment env, Name dName)
    {
        ConstantInfo info = env.Get(dName);
        if (!info.IsInductive) return null;
        Obj cnstrs = info.ToInductiveVal().Cnstrs;
        if (KList.IsNil(cnstrs)) return null;
        return new Name(KList.Head(cnstrs));
    }

    public static Expr MkNullaryCnstr(Environment env, Expr type, uint numParams)
    {
        var args = new List<Expr>();
        Expr d = Expr.GetAppArgs(type, args);
        if (!d.IsConst) return Expr.None;
        Name? cnstrName = GetFirstCnstr(env, d.ConstName);
        if (!cnstrName.HasValue) return Expr.None;
        if (args.Count > numParams) args.RemoveRange((int)numParams, args.Count - (int)numParams);
        return Expr.MkApp(Expr.MkConst(cnstrName.Value, d.ConstLevels), args);
    }

    public static Expr ExpandEtaStruct(Environment env, Expr eType, Expr e)
    {
        var args = new List<Expr>();
        Expr I = Expr.GetAppArgs(eType, args);
        if (!I.IsConst) return e;
        Name? ctorName = GetFirstCnstr(env, I.ConstName);
        if (!ctorName.HasValue) return e;
        ConstructorVal ctorVal = env.Get(ctorName.Value).ToConstructorVal();
        int np = (int)ctorVal.NParams;
        if (args.Count > np) args.RemoveRange(np, args.Count - np);
        Expr result = Expr.MkApp(Expr.MkConst(ctorName.Value, I.ConstLevels), args);
        for (uint i = 0; i < ctorVal.NFields; i++)
            result = Expr.MkApp(result, Expr.MkProj(I.ConstName, i, e));
        return result;
    }

    public static RecursorRule? GetRecRuleFor(RecursorVal recVal, Expr major)
    {
        Expr fn = Expr.GetAppFn(major);
        if (!fn.IsConst) return null;
        foreach (var r in KList.Iter(recVal.Rules))
        {
            var rule = new RecursorRule(r);
            if (rule.Cnstr == fn.ConstName) return rule;
        }
        return null;
    }

    /// <summary>`to_cnstr_when_K`.</summary>
    static Expr ToCnstrWhenK(Environment env, RecursorVal rval, Expr e, Func<Expr, Expr> whnf, Func<Expr, Expr> inferType, Func<Expr, Expr, bool> isDefEq)
    {
        Expr appType = whnf(inferType(e));
        Expr appTypeI = Expr.GetAppFn(appType);
        if (!appTypeI.IsConst || appTypeI.ConstName != rval.GetMajorInduct()) return e;
        if (appType.HasExprMVar)
        {
            var appTypeArgs = new List<Expr>();
            Expr.GetAppArgs(appType, appTypeArgs);
            for (int i = (int)rval.NParams; i < appTypeArgs.Count; i++)
                if (appTypeArgs[i].HasExprMVar) return e;
        }
        Expr newCnstrApp = MkNullaryCnstr(env, appType, rval.NParams);
        if (newCnstrApp.IsNull) return e;
        Expr newType = inferType(newCnstrApp);
        if (!isDefEq(appType, newType)) return e;
        return newCnstrApp;
    }

    /// <summary>`to_cnstr_when_structure`.</summary>
    static Expr ToCnstrWhenStructure(Environment env, Name inductName, Expr e, Func<Expr, Expr> whnf, Func<Expr, Expr> inferType, Func<Expr, bool> isProp)
    {
        if (!IsNonRecStructure(env, inductName) || IsConstructorApp(env, e).HasValue) return e;
        Expr eType = whnf(inferType(e));
        if (!Expr.GetAppFn(eType).IsConstOf(inductName)) return e;
        if (isProp(eType)) return e;
        return ExpandEtaStruct(env, eType, e);
    }

    /// <summary>`inductive_reduce_rec`: iota reduction.</summary>
    public static Expr InductiveReduceRec(Environment env, Expr e, Func<Expr, Expr> whnf, Func<Expr, Expr> inferType,
                                          Func<Expr, Expr, bool> isDefEq, Func<Expr, bool> isProp)
    {
        Expr recFn = Expr.GetAppFn(e);
        if (!recFn.IsConst) return Expr.None;
        ConstantInfo recInfo = env.Find(recFn.ConstName);
        if (recInfo.IsNull || !recInfo.IsRecursor) return Expr.None;
        var recArgs = new List<Expr>();
        Expr.GetAppArgs(e, recArgs);
        RecursorVal recVal = recInfo.ToRecursorVal();
        uint majorIdx = recVal.MajorIdx;
        if (majorIdx >= recArgs.Count) return Expr.None;
        Expr major = recArgs[(int)majorIdx];
        if (recVal.IsK)
            major = ToCnstrWhenK(env, recVal, major, whnf, inferType, isDefEq);
        major = whnf(major);
        if (major.IsNatLit)
            major = NatLitToConstructor(major);
        else if (major.IsStringLit)
            major = whnf(StringLitToConstructor(major));
        else
            major = ToCnstrWhenStructure(env, recVal.GetMajorInduct(), major, whnf, inferType, isProp);
        RecursorRule? rule = GetRecRuleFor(recVal, major);
        if (!rule.HasValue) return Expr.None;
        var majorArgs = new List<Expr>();
        Expr.GetAppArgs(major, majorArgs);
        if (rule.Value.NFields > majorArgs.Count) return Expr.None;
        if (KList.Length(recFn.ConstLevels) != KList.Length(recInfo.LParams)) return Expr.None;
        Expr rhs = Inst.InstantiateLParams(rule.Value.Rhs, recInfo.LParams, recFn.ConstLevels);
        rhs = Expr.MkApp(rhs, (int)(recVal.NParams + recVal.NMotives + recVal.NMinors), recArgs, 0);
        int nparams = majorArgs.Count - (int)rule.Value.NFields;
        rhs = Expr.MkApp(rhs, (int)rule.Value.NFields, majorArgs, nparams);
        if (recArgs.Count > majorIdx + 1)
        {
            int nextra = recArgs.Count - (int)majorIdx - 1;
            rhs = Expr.MkApp(rhs, nextra, recArgs, (int)majorIdx + 1);
        }
        return rhs;
    }

    public static Expr NatLitToConstructor(Expr e)
    {
        Obj v = e.LitNat;
        if (Nat.IsZero(v)) return KConsts.NatZero;
        return Expr.MkApp(KConsts.NatSucc, Expr.MkLit(Expr.MkNatLiteral(Nat.Sub(v, 1))));
    }

    public static Expr StringLitToConstructor(Expr e)
    {
        var bytes = lean_string_span(e.LitString);
        var cs = new List<uint>();
        int pos = 0;
        while (pos < bytes.Length)
        {
            System.Buffers.OperationStatus st = Rune.DecodeFromUtf8(bytes.Slice(pos), out Rune rune, out int consumed);
            if (consumed <= 0) consumed = 1;
            cs.Add((uint)rune.Value);
            pos += consumed;
        }
        Expr r = KConsts.ListNilChar;
        int i = cs.Count;
        while (i > 0)
        {
            i--;
            r = Expr.MkApp(Expr.MkApp(KConsts.ListConsChar, Expr.MkApp(KConsts.CharOfNat, Expr.MkLit(Expr.MkNatLiteral(lean_box(cs[i]))))), r);
        }
        return Expr.MkApp(KConsts.StringMk, r);
    }

    /// <summary>Check that every occurrence of a datatype being declared is applied to the parameters.</summary>
    static void CheckUniformIndOccs(Environment env, Declaration d)
    {
        if (!lean_is_scalar(d.IndNParams))
            throw new KernelException(env.Raw, "invalid inductive datatype, number of parameters is too big");
        uint nparams = (uint)lean_unbox(d.IndNParams);
        Obj lvls = Level.LParamsToLevels(d.IndLParams);
        var indNames = new List<Name>();
        foreach (var t in KList.Iter(d.IndTypes)) indNames.Add(InductiveType.GetName(t));
        foreach (var t in KList.Iter(d.IndTypes))
        {
            foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(t)))
            {
                ForEachFn.ForEachOffset(InductiveType.CnstrType(cnstr), (x, offset) =>
                {
                    var args = new List<Expr>();
                    Expr fn = Expr.GetAppArgs(x, args);
                    if (!fn.IsConst || !indNames.Contains(fn.ConstName)) return true;
                    if (args.Count > nparams) return true;
                    bool ok = args.Count == nparams && offset >= nparams && Level.ListEq(fn.ConstLevels, lvls);
                    for (uint i = 0; ok && i < nparams; i++)
                        ok = args[(int)i].IsBVarIdx(offset - 1 - i);
                    if (!ok)
                        throw new KernelException(env.Raw, "invalid occurrence of datatype '" + fn.ConstName + "' being declared: it must be applied to the parameters and universe levels of the mutual declaration");
                    return false;
                });
            }
        }
    }

    /// <summary>Auxiliary class for adding a mutual inductive datatype declaration.</summary>
    sealed class AddInductiveFn
    {
        /// <summary>Owned environment.</summary>
        Obj m_env;
        readonly NameGenerator m_ngen;
        readonly Diagnostics m_diag;
        readonly LocalCtx m_lctx = new LocalCtx();
        readonly Obj m_lparams;
        readonly uint m_nparams;
        readonly bool m_isUnsafe;
        readonly List<Obj> m_indTypes;
        readonly List<uint> m_nindices = new();
        Level m_resultLevel;
        Obj m_levels;
        bool m_isNotZero;
        readonly List<Expr> m_params = new();
        readonly List<Expr> m_indCnsts = new();
        Level m_elimLevel;
        bool m_KTarget;
        readonly uint m_nnested;

        sealed class RecInfo
        {
            public Expr C;
            public readonly List<Expr> Minors = new();
            public readonly List<Expr> Indices = new();
            public Expr Major;
        }

        readonly List<RecInfo> m_recInfos = new();

        public AddInductiveFn(Environment env, Diagnostics diag, Declaration decl, uint nnested)
        {
            m_env = RC.Own(env.Raw);
            m_ngen = new NameGenerator(KConsts.IndFresh);
            m_diag = diag;
            m_lparams = decl.IndLParams;
            m_isUnsafe = decl.IndIsUnsafe;
            m_nnested = nnested;
            if (!lean_is_scalar(decl.IndNParams))
                throw new KernelException(env.Raw, "invalid inductive datatype, number of parameters is too big");
            m_nparams = (uint)lean_unbox(decl.IndNParams);
            m_indTypes = KList.ToList(decl.IndTypes);
        }

        Environment Env => new Environment(m_env);

        TypeChecker Tc() => new TypeChecker(Env, m_lctx.Raw, m_diag, m_isUnsafe ? DefinitionSafety.Unsafe : DefinitionSafety.Safe);

        Expr GetParamType(int i) => m_lctx.GetLocalDecl(m_params[i]).Type;

        Expr MkLocalDecl(Name n, Expr t, BinderInfo bi = BinderInfo.Default) =>
            m_lctx.MkLocalDecl(m_ngen, n, Expr.ConsumeTypeAnnotations(t), bi);

        Expr MkLocalDeclFor(Expr t) =>
            m_lctx.MkLocalDecl(m_ngen, t.BindingName, Expr.ConsumeTypeAnnotations(t.BindingDomain), t.BindingInfo);

        Expr Whnf(Expr t) { using var tc = Tc(); return tc.Whnf(t); }
        Expr InferType(Expr t) { using var tc = Tc(); return tc.Infer(t); }
        bool IsDefEq(Expr t1, Expr t2) { using var tc = Tc(); return tc.IsDefEq(t1, t2); }
        Expr TcCheck(Expr t, Obj lps) { using var tc = Tc(); return tc.Check(t, lps); }
        Expr TcEnsureSort(Expr t) { using var tc = Tc(); return tc.EnsureSort(t); }
        Expr TcEnsureType(Expr t) { using var tc = Tc(); return tc.EnsureType(t); }

        Expr MkPi(List<Expr> fvars, Expr e) => m_lctx.MkPi(fvars, e);
        Expr MkPi(Expr fvar, Expr e) => m_lctx.MkPi(fvar, e);
        Expr MkLambda(List<Expr> fvars, Expr e) => m_lctx.MkLambda(fvars, e);

        void CheckInductiveTypes()
        {
            m_levels = Level.LParamsToLevels(m_lparams);
            bool first = true;
            foreach (var indType in m_indTypes)
            {
                Expr type = InductiveType.GetType(indType);
                Env.CheckName(InductiveType.GetName(indType));
                Env.CheckName(MkRecName(InductiveType.GetName(indType)));
                EnvOps.CheckNoMetavarNoFVar(Env, InductiveType.GetName(indType), type);
                TcCheck(type, m_lparams);
                m_nindices.Add(0);
                uint i = 0;
                type = Whnf(type);
                while (type.IsPi)
                {
                    if (i < m_nparams)
                    {
                        if (first)
                        {
                            Expr param = MkLocalDeclFor(type);
                            m_params.Add(param);
                            type = Inst.Instantiate(type.BindingBody, param);
                        }
                        else
                        {
                            if (!IsDefEq(type.BindingDomain, GetParamType((int)i)))
                                throw new KernelException(m_env, "parameters of all inductive datatypes must match");
                            type = Inst.Instantiate(type.BindingBody, m_params[(int)i]);
                        }
                        i++;
                    }
                    else
                    {
                        Expr local = MkLocalDeclFor(type);
                        type = Inst.Instantiate(type.BindingBody, local);
                        m_nindices[m_nindices.Count - 1]++;
                    }
                    type = Whnf(type);
                }
                if (i != m_nparams)
                    throw new KernelException(m_env, "number of parameters mismatch in inductive datatype declaration");

                type = TcEnsureSort(type);

                if (first)
                {
                    m_resultLevel = type.SortLevel;
                    m_isNotZero = Level.IsNotZero(m_resultLevel);
                }
                else if (!Level.IsEquivalent(type.SortLevel, m_resultLevel))
                {
                    throw new KernelException(m_env, "mutually inductive types must live in the same universe");
                }

                m_indCnsts.Add(Expr.MkConst(InductiveType.GetName(indType), m_levels));
                first = false;
            }
        }

        bool IsIndConstName(Name n)
        {
            foreach (var I in m_indCnsts)
                if (I.ConstName == n) return true;
            return false;
        }

        bool IsRec()
        {
            foreach (var indType in m_indTypes)
            {
                foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(indType)))
                {
                    Expr t = InductiveType.CnstrType(cnstr);
                    while (t.IsPi)
                    {
                        if (ForEachFn.Find(t.BindingDomain, (e, _) => e.IsConst && IsIndConstName(e.ConstName)).IsSome)
                            return true;
                        t = t.BindingBody;
                    }
                }
            }
            return false;
        }

        bool IsReflexive()
        {
            foreach (var indType in m_indTypes)
            {
                foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(indType)))
                {
                    Expr t = InductiveType.CnstrType(cnstr);
                    while (t.IsPi)
                    {
                        Expr argType = t.BindingDomain;
                        if (argType.IsPi && HasIndOcc(argType)) return true;
                        Expr local = MkLocalDeclFor(t);
                        t = Inst.Instantiate(t.BindingBody, local);
                    }
                }
            }
            return false;
        }

        Obj GetAllInductiveNames() => Inductive.GetAllInductiveNames(m_indTypes);

        void DeclareInductiveTypes()
        {
            bool rec = IsRec();
            bool reflexive = IsReflexive();
            Obj all = GetAllInductiveNames();
            for (int idx = 0; idx < m_indTypes.Count; idx++)
            {
                Obj indType = m_indTypes[idx];
                Name n = InductiveType.GetName(indType);
                var cnstrNames = new List<Obj>();
                foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(indType)))
                    cnstrNames.Add(InductiveType.CnstrName(cnstr).Raw);
                Env.CheckName(n);
                var iv = InductiveVal.Mk(n, m_lparams, InductiveType.GetType(indType), m_nparams, m_nindices[idx],
                    all, KList.OfBorrowed(cnstrNames), m_nnested, rec, m_isUnsafe, reflexive);
                m_env = EnvOps.AddCore(m_env, ConstantInfo.Of(ConstantInfoKind.Inductive, iv.Raw));
            }
        }

        bool IsValidIndApp(Expr t, int i)
        {
            var args = new List<Expr>();
            Expr I = Expr.GetAppArgs(t, args);
            if (I != m_indCnsts[i] || args.Count != m_nparams + m_nindices[i]) return false;
            for (int k = 0; k < m_nparams; k++)
                if (m_params[k] != args[k]) return false;
            for (int k = (int)m_nparams; k < args.Count; k++)
                if (HasIndOcc(args[k])) return false;
            return true;
        }

        int? IsValidIndApp(Expr t)
        {
            for (int i = 0; i < m_indTypes.Count; i++)
                if (IsValidIndApp(t, i)) return i;
            return null;
        }

        bool IsIndOcc(Expr e) => e.IsConst && IsIndConstName(e.ConstName);

        bool HasIndOcc(Expr t) => ForEachFn.Find(t, (e, _) => IsIndOcc(e)).IsSome;

        int? IsRecArgument(Expr t)
        {
            t = Whnf(t);
            while (t.IsPi)
            {
                Expr local = MkLocalDeclFor(t);
                t = Whnf(Inst.Instantiate(t.BindingBody, local));
            }
            return IsValidIndApp(t);
        }

        void CheckPositivity(Expr t, Name cnstrName, int argIdx)
        {
            t = Whnf(t);
            if (!HasIndOcc(t))
            {
                // nonrecursive argument
            }
            else if (t.IsPi)
            {
                if (HasIndOcc(t.BindingDomain))
                    throw new KernelException(m_env, "arg #" + (argIdx + 1) + " of '" + cnstrName + "' has a non positive occurrence of the datatypes being declared");
                Expr local = MkLocalDeclFor(t);
                CheckPositivity(Inst.Instantiate(t.BindingBody, local), cnstrName, argIdx);
            }
            else if (IsValidIndApp(t).HasValue)
            {
                // recursive argument
            }
            else
            {
                throw new KernelException(m_env, "arg #" + (argIdx + 1) + " of '" + cnstrName + "' contains a non valid occurrence of the datatypes being declared");
            }
        }

        void CheckConstructors()
        {
            for (int idx = 0; idx < m_indTypes.Count; idx++)
            {
                Obj indType = m_indTypes[idx];
                var foundCnstrs = new HashSet<Name>();
                foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(indType)))
                {
                    Name n = InductiveType.CnstrName(cnstr);
                    if (foundCnstrs.Contains(n))
                        throw new KernelException(m_env, "duplicate constructor name '" + n + "'");
                    foundCnstrs.Add(n);
                    Expr t = InductiveType.CnstrType(cnstr);
                    Env.CheckName(n);
                    EnvOps.CheckNoMetavarNoFVar(Env, n, t);
                    TcCheck(t, m_lparams);
                    uint i = 0;
                    while (t.IsPi)
                    {
                        if (i < m_nparams)
                        {
                            if (!IsDefEq(t.BindingDomain, GetParamType((int)i)))
                                throw new KernelException(m_env, "arg #" + (i + 1) + " of '" + n + "' does not match inductive datatypes parameters'");
                            t = Inst.Instantiate(t.BindingBody, m_params[(int)i]);
                        }
                        else
                        {
                            Expr s = TcEnsureType(t.BindingDomain);
                            if (!(Level.IsGeq(m_resultLevel, s.SortLevel) || Level.NormalizesToZero(m_resultLevel)))
                                throw new KernelException(m_env, "universe level of type_of(arg #" + (i + 1) + ") of '" + n + "' is too big for the corresponding inductive datatype");
                            if (!m_isUnsafe)
                                CheckPositivity(t.BindingDomain, n, (int)i);
                            Expr local = MkLocalDeclFor(t);
                            t = Inst.Instantiate(t.BindingBody, local);
                        }
                        i++;
                    }
                    if (!IsValidIndApp(t, idx))
                        throw new KernelException(m_env, "invalid return type for '" + n + "'");
                }
            }
        }

        void DeclareConstructors()
        {
            for (int idx = 0; idx < m_indTypes.Count; idx++)
            {
                Obj indType = m_indTypes[idx];
                uint cidx = 0;
                foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(indType)))
                {
                    Name n = InductiveType.CnstrName(cnstr);
                    Expr t = InductiveType.CnstrType(cnstr);
                    uint arity = 0;
                    Expr it = t;
                    while (it.IsPi) { it = it.BindingBody; arity++; }
                    uint nfields = arity - m_nparams;
                    Env.CheckName(n);
                    var cv = ConstructorVal.Mk(n, m_lparams, t, InductiveType.GetName(indType), cidx, m_nparams, nfields, m_isUnsafe);
                    m_env = EnvOps.AddCore(m_env, ConstantInfo.Of(ConstantInfoKind.Constructor, cv.Raw));
                    cidx++;
                }
            }
        }

        bool ElimOnlyAtUniverseZero()
        {
            if (m_isNotZero) return false;
            if (m_indTypes.Count > 1) return true;
            int numIntros = KList.Length(InductiveType.GetCnstrs(m_indTypes[0]));
            if (numIntros > 1) return true;
            if (numIntros == 0) return false;
            Obj cnstr = KList.Head(InductiveType.GetCnstrs(m_indTypes[0]));
            Expr type = InductiveType.CnstrType(cnstr);
            uint i = 0;
            var toCheck = new List<Expr>();
            while (type.IsPi)
            {
                Expr fvar = MkLocalDeclFor(type);
                if (i >= m_nparams)
                {
                    Expr s = TcEnsureType(type.BindingDomain);
                    if (!Level.NormalizesToZero(s.SortLevel))
                        toCheck.Add(fvar);
                }
                type = Inst.Instantiate(type.BindingBody, fvar);
                i++;
            }
            var resultArgs = new List<Expr>();
            Expr.GetAppArgs(type, resultArgs);
            foreach (var arg in toCheck)
            {
                bool found = false;
                foreach (var r in resultArgs) if (r == arg) { found = true; break; }
                if (!found) return true;
            }
            return false;
        }

        void InitElimLevel()
        {
            if (ElimOnlyAtUniverseZero())
            {
                m_elimLevel = Level.Zero;
            }
            else
            {
                Name u = Name.Str("u");
                uint i = 1;
                while (Level.NameListContains(m_lparams, u))
                {
                    u = Name.Str("u").AppendAfter(i);
                    i++;
                }
                m_elimLevel = Level.MkParam(u);
            }
        }

        void InitKTarget()
        {
            m_KTarget = m_indTypes.Count == 1 && Level.NormalizesToZero(m_resultLevel) && KList.Length(InductiveType.GetCnstrs(m_indTypes[0])) == 1;
            if (!m_KTarget) return;
            Expr it = InductiveType.CnstrType(KList.Head(InductiveType.GetCnstrs(m_indTypes[0])));
            uint i = 0;
            while (it.IsPi)
            {
                if (i < m_nparams) it = it.BindingBody;
                else { m_KTarget = false; break; }
                i++;
            }
        }

        int GetIIndices(Expr t, List<Expr> indices)
        {
            int? r = IsValidIndApp(t);
            var allArgs = new List<Expr>();
            Expr.GetAppArgs(t, allArgs);
            for (int i = (int)m_nparams; i < allArgs.Count; i++) indices.Add(allArgs[i]);
            return r.Value;
        }

        void MkRecInfos()
        {
            int dIdx = 0;
            foreach (var indType in m_indTypes)
            {
                var info = new RecInfo();
                Expr t = InductiveType.GetType(indType);
                uint i = 0;
                t = Whnf(t);
                while (t.IsPi)
                {
                    if (i < m_nparams)
                    {
                        t = Inst.Instantiate(t.BindingBody, m_params[(int)i]);
                    }
                    else
                    {
                        Expr idx = MkLocalDeclFor(t);
                        info.Indices.Add(idx);
                        t = Inst.Instantiate(t.BindingBody, idx);
                    }
                    i++;
                    t = Whnf(t);
                }
                info.Major = MkLocalDecl(KConsts.TName, Expr.MkApp(Expr.MkApp(m_indCnsts[dIdx], m_params), info.Indices));
                Expr CTy = Expr.MkSort(m_elimLevel);
                CTy = MkPi(info.Major, CTy);
                CTy = MkPi(info.Indices, CTy);
                Name CName = KConsts.MotiveName;
                if (m_indTypes.Count > 1)
                    CName = CName.AppendAfter((uint)(dIdx + 1));
                info.C = MkLocalDecl(CName, CTy);
                m_recInfos.Add(info);
                dIdx++;
            }
            dIdx = 0;
            foreach (var indType in m_indTypes)
            {
                Name indTypeName = InductiveType.GetName(indType);
                foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(indType)))
                {
                    var b_u = new List<Expr>();
                    var u = new List<Expr>();
                    var v = new List<Expr>();
                    Name cnstrName = InductiveType.CnstrName(cnstr);
                    Expr t = InductiveType.CnstrType(cnstr);
                    uint i = 0;
                    while (t.IsPi)
                    {
                        if (i < m_nparams)
                        {
                            t = Inst.Instantiate(t.BindingBody, m_params[(int)i]);
                        }
                        else
                        {
                            Expr l = MkLocalDeclFor(t);
                            b_u.Add(l);
                            if (IsRecArgument(t.BindingDomain).HasValue) u.Add(l);
                            t = Inst.Instantiate(t.BindingBody, l);
                        }
                        i++;
                    }
                    var itIndices = new List<Expr>();
                    int itIdx = GetIIndices(t, itIndices);
                    Expr CApp = Expr.MkApp(m_recInfos[itIdx].C, itIndices);
                    Expr introApp = Expr.MkApp(Expr.MkApp(Expr.MkConst(cnstrName, m_levels), m_params), b_u);
                    CApp = Expr.MkApp(CApp, introApp);
                    for (int k = 0; k < u.Count; k++)
                    {
                        Expr u_i = u[k];
                        Expr u_i_ty = Whnf(InferType(u_i));
                        var xs = new List<Expr>();
                        while (u_i_ty.IsPi)
                        {
                            Expr x = MkLocalDeclFor(u_i_ty);
                            xs.Add(x);
                            u_i_ty = Whnf(Inst.Instantiate(u_i_ty.BindingBody, x));
                        }
                        var itIndices2 = new List<Expr>();
                        int itIdx2 = GetIIndices(u_i_ty, itIndices2);
                        Expr CApp2 = Expr.MkApp(m_recInfos[itIdx2].C, itIndices2);
                        Expr uApp = Expr.MkApp(u_i, xs);
                        CApp2 = Expr.MkApp(CApp2, uApp);
                        Expr v_i_ty = MkPi(xs, CApp2);
                        LocalDecl u_i_decl = m_lctx.GetLocalDecl(u_i.FVarName);
                        Expr v_i = MkLocalDecl(u_i_decl.UserName.AppendAfter("_ih"), v_i_ty, BinderInfo.Default);
                        v.Add(v_i);
                    }
                    Expr minorTy = MkPi(b_u, MkPi(v, CApp));
                    Name minorName = cnstrName.ReplacePrefix(indTypeName, Name.Anonymous);
                    Expr minor = MkLocalDecl(minorName, minorTy);
                    m_recInfos[dIdx].Minors.Add(minor);
                }
                dIdx++;
            }
        }

        Obj GetRecLevels()
        {
            if (m_elimLevel.IsParam) return KList.Cons(RC.Own(m_elimLevel.Raw), RC.Own(m_levels));
            return m_levels;
        }

        Obj GetRecLParams()
        {
            if (m_elimLevel.IsParam) return KList.Cons(RC.Own(m_elimLevel.Id.Raw), RC.Own(m_lparams));
            return m_lparams;
        }

        void CollectCs(List<Expr> Cs)
        {
            for (int i = 0; i < m_indTypes.Count; i++) Cs.Add(m_recInfos[i].C);
        }

        void CollectMinorPremises(List<Expr> ms)
        {
            for (int i = 0; i < m_indTypes.Count; i++) ms.AddRange(m_recInfos[i].Minors);
        }

        Obj MkRecRules(int dIdx, List<Expr> Cs, List<Expr> minors, ref int minorIdx)
        {
            Obj d = m_indTypes[dIdx];
            Obj lvls = GetRecLevels();
            var rules = new List<Obj>();
            foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(d)))
            {
                var b_u = new List<Expr>();
                var u = new List<Expr>();
                Expr t = InductiveType.CnstrType(cnstr);
                uint i = 0;
                while (t.IsPi)
                {
                    if (i < m_nparams)
                    {
                        t = Inst.Instantiate(t.BindingBody, m_params[(int)i]);
                    }
                    else
                    {
                        Expr l = MkLocalDeclFor(t);
                        b_u.Add(l);
                        if (IsRecArgument(t.BindingDomain).HasValue) u.Add(l);
                        t = Inst.Instantiate(t.BindingBody, l);
                    }
                    i++;
                }
                var v = new List<Expr>();
                for (int k = 0; k < u.Count; k++)
                {
                    Expr u_i = u[k];
                    Expr u_i_ty = Whnf(InferType(u_i));
                    var xs = new List<Expr>();
                    while (u_i_ty.IsPi)
                    {
                        Expr x = MkLocalDeclFor(u_i_ty);
                        xs.Add(x);
                        u_i_ty = Whnf(Inst.Instantiate(u_i_ty.BindingBody, x));
                    }
                    var itIndices = new List<Expr>();
                    int itIdx = GetIIndices(u_i_ty, itIndices);
                    Name recName = MkRecName(InductiveType.GetName(m_indTypes[itIdx]));
                    Expr recApp = Expr.MkConst(recName, lvls);
                    recApp = Expr.MkApp(Expr.MkApp(Expr.MkApp(Expr.MkApp(Expr.MkApp(recApp, m_params), Cs), minors), itIndices), Expr.MkApp(u_i, xs));
                    v.Add(MkLambda(xs, recApp));
                }
                Expr eApp = Expr.MkApp(Expr.MkApp(minors[minorIdx], b_u), v);
                Expr compRhs = MkLambda(m_params, MkLambda(Cs, MkLambda(minors, MkLambda(b_u, eApp))));
                rules.Add(RecursorRule.Mk(InductiveType.CnstrName(cnstr), (uint)b_u.Count, compRhs).Raw);
                minorIdx++;
            }
            return KList.OfBorrowed(rules);
        }

        void DeclareRecursors()
        {
            var Cs = new List<Expr>(); CollectCs(Cs);
            var minors = new List<Expr>(); CollectMinorPremises(minors);
            uint nminors = (uint)minors.Count;
            uint nmotives = (uint)Cs.Count;
            Obj all = GetAllInductiveNames();
            int minorIdx = 0;
            for (int dIdx = 0; dIdx < m_indTypes.Count; dIdx++)
            {
                RecInfo info = m_recInfos[dIdx];
                Expr CApp = Expr.MkApp(Expr.MkApp(info.C, info.Indices), info.Major);
                Expr recTy = MkPi(info.Major, CApp);
                recTy = MkPi(info.Indices, recTy);
                recTy = MkPi(minors, recTy);
                recTy = MkPi(Cs, recTy);
                recTy = MkPi(m_params, recTy);
                recTy = Expr.InferImplicit(recTy, true);
                Obj rules = MkRecRules(dIdx, Cs, minors, ref minorIdx);
                Name recName = MkRecName(InductiveType.GetName(m_indTypes[dIdx]));
                Obj recLParams = GetRecLParams();
                Env.CheckName(recName);
                var rv = RecursorVal.Mk(recName, recLParams, recTy, all, m_nparams, m_nindices[dIdx], nmotives, nminors, rules, m_KTarget, m_isUnsafe);
                m_env = EnvOps.AddCore(m_env, ConstantInfo.Of(ConstantInfoKind.Recursor, rv.Raw));
            }
        }

        void CheckRecursors()
        {
            var Cs = new List<Expr>(); CollectCs(Cs);
            var minors = new List<Expr>(); CollectMinorPremises(minors);
            for (int dIdx = 0; dIdx < m_indTypes.Count; dIdx++)
            {
                Name recName = MkRecName(InductiveType.GetName(m_indTypes[dIdx]));
                ConstantInfo recCi = Env.Get(recName);
                TcCheck(recCi.Type, GetRecLParams());
                Expr recPre = Expr.MkApp(Expr.MkApp(Expr.MkApp(Expr.MkConst(recName, GetRecLevels()), m_params), Cs), minors);
                foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(m_indTypes[dIdx])))
                {
                    var b_u = new List<Expr>();
                    Expr t = InductiveType.CnstrType(cnstr);
                    uint i = 0;
                    while (t.IsPi)
                    {
                        if (i < m_nparams)
                        {
                            t = Inst.Instantiate(t.BindingBody, m_params[(int)i]);
                        }
                        else
                        {
                            Expr l = MkLocalDeclFor(t);
                            b_u.Add(l);
                            t = Inst.Instantiate(t.BindingBody, l);
                        }
                        i++;
                    }
                    var itIndices = new List<Expr>();
                    GetIIndices(t, itIndices);
                    Expr introApp = Expr.MkApp(Expr.MkApp(Expr.MkConst(InductiveType.CnstrName(cnstr), m_levels), m_params), b_u);
                    Expr lhs = Expr.MkApp(Expr.MkApp(recPre, itIndices), introApp);
                    using var tcheck = Tc();
                    Expr expected = tcheck.Infer(lhs);
                    Expr reduct = tcheck.Whnf(lhs);
                    Expr actual = tcheck.Infer(reduct);
                    if (!tcheck.IsDefEq(actual, expected))
                        throw new KernelException(m_env, "generated recursor computation rule for '" + InductiveType.CnstrName(cnstr) + "' is not type-preserving");
                }
            }
        }

        /// <summary>Run the procedure; returns the owned new environment.</summary>
        public Obj Run()
        {
            Env.CheckDuplicatedUnivParams(m_lparams);
            CheckInductiveTypes();
            DeclareInductiveTypes();
            CheckConstructors();
            DeclareConstructors();
            InitElimLevel();
            InitKTarget();
            MkRecInfos();
            DeclareRecursors();
            CheckRecursors();
            Obj r = m_env;
            m_env = null;
            return r;
        }
    }

    /// <summary>Result produced by `ElimNestedInductiveFn`.</summary>
    sealed class ElimNestedInductiveResult
    {
        public readonly NameGenerator NGen;
        public readonly List<Expr> Params;
        public readonly LocalCtx ParamsLCtx;
        /// <summary>Mapping from auxiliary type to nested inductive type (ordered by name, as `name_map`).</summary>
        public readonly SortedDictionary<Name, Expr> Aux2Nested = new(Comparer<Name>.Create(Name.Cmp));
        public readonly Declaration AuxDecl;

        public ElimNestedInductiveResult(NameGenerator ngen, List<Expr> prms, LocalCtx paramsLCtx, List<(Expr, Name)> nestedAux, Declaration d)
        {
            NGen = ngen.Clone();
            Params = new List<Expr>(prms);
            ParamsLCtx = paramsLCtx.Copy();
            AuxDecl = d;
            foreach (var p in nestedAux) Aux2Nested[p.Item2] = p.Item1;
        }

        (Expr, Name)? GetNestedIfAuxConstructor(Environment auxEnv, Name c)
        {
            ConstantInfo info = auxEnv.Find(c);
            if (info.IsNull || !info.IsConstructor) return null;
            Name auxIName = info.ToConstructorVal().Induct;
            if (!Aux2Nested.TryGetValue(auxIName, out Expr nested)) return null;
            return (nested, auxIName);
        }

        public Name RestoreConstructorName(Environment auxEnv, Name cnstrName)
        {
            var p = GetNestedIfAuxConstructor(auxEnv, cnstrName);
            if (!p.HasValue)
                throw new KernelException(auxEnv.Raw, "failed to restore nested inductive types, '" + cnstrName + "' is not a constructor of an auxiliary type");
            Expr I = Expr.GetAppFn(p.Value.Item1);
            if (!I.IsConst)
                throw new KernelException(auxEnv.Raw, "failed to restore nested inductive types, nested occurrence is not an inductive type application");
            return cnstrName.ReplacePrefix(p.Value.Item2, I.ConstName);
        }

        public Expr RestoreNested(Expr e, Environment auxEnv, Dictionary<Name, Name> auxRecNameMap = null)
        {
            auxRecNameMap ??= new Dictionary<Name, Name>();
            var lctx = new LocalCtx();
            var As = new List<Expr>();
            bool pi = e.IsPi;
            for (int i = 0; i < Params.Count; i++)
            {
                if (!e.IsPi && !e.IsLambda)
                    throw new KernelException(auxEnv.Raw, "failed to restore nested inductive types, fewer binders than parameters");
                As.Add(lctx.MkLocalDecl(NGen, e.BindingName, e.BindingDomain, e.BindingInfo));
                e = Inst.Instantiate(e.BindingBody, As[As.Count - 1]);
            }
            e = ReplaceFn.Replace(e, (t, _) =>
            {
                if (t.IsConst && auxRecNameMap.TryGetValue(t.ConstName, out Name recName))
                    return Expr.MkConst(recName, t.ConstLevels);
                Expr fn = Expr.GetAppFn(t);
                if (fn.IsConst)
                {
                    if (Aux2Nested.TryGetValue(fn.ConstName, out Expr nested0))
                    {
                        var args = new List<Expr>();
                        Expr.GetAppArgs(t, args);
                        if (args.Count < Params.Count)
                            throw new KernelException(auxEnv.Raw, "failed to restore nested inductive types, auxiliary type is not applied to all parameters");
                        Expr newT = Inst.InstantiateRev(Inst.Abstract(nested0, Params.Count, Params), As.Count, As);
                        return Expr.MkApp(newT, args.Count - Params.Count, args, Params.Count);
                    }
                    var r = GetNestedIfAuxConstructor(auxEnv, fn.ConstName);
                    if (r.HasValue)
                    {
                        Expr nested = r.Value.Item1;
                        Name auxIName = r.Value.Item2;
                        var args = new List<Expr>();
                        Expr.GetAppArgs(t, args);
                        if (args.Count < Params.Count)
                            throw new KernelException(auxEnv.Raw, "failed to restore nested inductive types, auxiliary constructor is not applied to all parameters");
                        Expr newNested = Inst.InstantiateRev(Inst.Abstract(nested, Params.Count, Params), As.Count, As);
                        var IArgs = new List<Expr>();
                        Expr I = Expr.GetAppArgs(newNested, IArgs);
                        if (!I.IsConst)
                            throw new KernelException(auxEnv.Raw, "failed to restore nested inductive types, nested occurrence is not an inductive type application");
                        Name newFnName = fn.ConstName.ReplacePrefix(auxIName, I.ConstName);
                        Expr newFn = Expr.MkConst(newFnName, I.ConstLevels);
                        return Expr.MkApp(Expr.MkApp(newFn, IArgs), args.Count - Params.Count, args, Params.Count);
                    }
                }
                return Expr.None;
            });
            return pi ? lctx.MkPi(As, e) : lctx.MkLambda(As, e);
        }
    }

    /// <summary>Eliminate nested inductive datatypes by creating an auxiliary mutual declaration.</summary>
    sealed class ElimNestedInductiveFn
    {
        readonly Environment m_env;
        readonly Declaration m_d;
        readonly NameGenerator m_ngen;
        readonly LocalCtx m_paramsLCtx = new LocalCtx();
        readonly List<Expr> m_params = new();
        readonly List<(Expr, Name)> m_nestedAux = new();
        readonly Obj m_lvls;
        readonly List<Obj> m_newTypes = new();
        uint m_nextIdx = 1;

        public ElimNestedInductiveFn(Environment env, Declaration d)
        {
            m_env = env;
            m_d = d;
            m_ngen = new NameGenerator(KConsts.NestedFresh);
            m_lvls = Level.LParamsToLevels(d.IndLParams);
        }

        Name MkUniqueName(Name n)
        {
            while (true)
            {
                Name r = n.AppendAfter(m_nextIdx);
                m_nextIdx++;
                if (m_env.Find(r).IsNull) return r;
            }
        }

        void ThrowIllFormed() => throw new KernelException(m_env.Raw, "invalid nested inductive datatype, ill-formed declaration");

        Expr ReplaceParams(Expr e, List<Expr> As) => Inst.InstantiateRev(Inst.Abstract(e, As.Count, As), m_params.Count, m_params);

        InductiveVal? IsNestedInductiveApp(Expr e)
        {
            if (!e.IsApp) return null;
            Expr fn = Expr.GetAppFn(e);
            if (!fn.IsConst) return null;
            ConstantInfo info = m_env.Find(fn.ConstName);
            if (info.IsNull || !info.IsInductive) return null;
            var args = new List<Expr>();
            Expr.GetAppArgs(e, args);
            uint nparams = info.ToInductiveVal().NParams;
            if (nparams > args.Count) return null;
            bool isNested = false;
            bool looseBVars = false;
            for (int i = 0; i < nparams; i++)
            {
                if (args[i].HasLooseBVars) looseBVars = true;
                if (ForEachFn.Find(args[i], (t, _) =>
                    {
                        if (t.IsConst)
                            foreach (var indType in m_newTypes)
                                if (t.ConstName == InductiveType.GetName(indType)) return true;
                        return false;
                    }).IsSome)
                    isNested = true;
            }
            if (!isNested) return null;
            if (looseBVars)
                throw new KernelException(m_env.Raw, "invalid nested inductive datatype '" + fn.ConstName + "', nested inductive datatypes parameters cannot contain local variables.");
            return info.ToInductiveVal();
        }

        Expr InstantiatePiParams(Expr e, uint nparams, List<Expr> prms)
        {
            for (uint i = 0; i < nparams; i++)
            {
                if (!e.IsPi) ThrowIllFormed();
                e = e.BindingBody;
            }
            return Inst.InstantiateRev(e, (int)nparams, prms);
        }

        Expr ReplaceIfNested(LocalCtx lctx, List<Expr> As, Expr e)
        {
            InductiveVal? IVal = IsNestedInductiveApp(e);
            if (!IVal.HasValue) return Expr.None;
            var args = new List<Expr>();
            Expr fn = Expr.GetAppArgs(e, args);
            Name IName = fn.ConstName;
            Obj ILvls = fn.ConstLevels;
            uint INParams = IVal.Value.NParams;
            Expr IAs = Expr.MkApp(fn, (int)INParams, args, 0);
            Name? auxIName = null;
            Expr Iparams = ReplaceParams(IAs, As);
            foreach (var p in m_nestedAux)
            {
                if (p.Item1 == Iparams) { auxIName = p.Item2; break; }
            }
            if (auxIName.HasValue)
            {
                Expr auxI = Expr.MkConst(auxIName.Value, m_lvls);
                auxI = Expr.MkApp(auxI, As);
                return Expr.MkApp(auxI, args.Count - (int)INParams, args, (int)INParams);
            }
            Expr result = Expr.None;
            foreach (var JNameObj in KList.Iter(IVal.Value.All))
            {
                Name JName = new Name(JNameObj);
                ConstantInfo JInfo = m_env.Get(JName);
                Expr J = Expr.MkConst(JName, ILvls);
                Expr JAs = Expr.MkApp(J, (int)INParams, args, 0);
                Name auxJName = MkUniqueName(KConsts.Nested + JName);
                Expr auxJType = Inst.InstantiateLParams(JInfo.Type, JInfo.LParams, ILvls);
                auxJType = InstantiatePiParams(auxJType, INParams, args);
                auxJType = lctx.MkPi(As, auxJType);
                m_nestedAux.Add((ReplaceParams(JAs, As), auxJName));
                if (JName == IName)
                {
                    Expr auxI = Expr.MkConst(auxJName, m_lvls);
                    auxI = Expr.MkApp(auxI, As);
                    result = Expr.MkApp(auxI, args.Count - (int)INParams, args, (int)INParams);
                }
                var auxJConstructors = new List<Obj>();
                foreach (var JCnstrNameObj in KList.Iter(JInfo.ToInductiveVal().Cnstrs))
                {
                    Name JCnstrName = new Name(JCnstrNameObj);
                    ConstantInfo JCnstrInfo = m_env.Get(JCnstrName);
                    Name auxJCnstrName = JCnstrName.ReplacePrefix(JName, auxJName);
                    Expr auxJCnstrType = Inst.InstantiateLParams(JCnstrInfo.Type, JCnstrInfo.LParams, ILvls);
                    auxJCnstrType = InstantiatePiParams(auxJCnstrType, INParams, args);
                    auxJCnstrType = lctx.MkPi(As, auxJCnstrType);
                    auxJConstructors.Add(InductiveType.MkCnstr(auxJCnstrName, auxJCnstrType));
                }
                m_newTypes.Add(InductiveType.Mk(auxJName, auxJType, KList.OfOwned(auxJConstructors)));
            }
            return result;
        }

        Expr ReplaceAllNested(LocalCtx lctx, List<Expr> As, Expr e) =>
            ReplaceFn.Replace(e, (x, _) => ReplaceIfNested(lctx, As, x));

        Expr GetParams(Expr type, uint nparams, LocalCtx lctx, List<Expr> prms)
        {
            for (uint i = 0; i < nparams; i++)
            {
                if (!type.IsPi)
                    throw new KernelException(m_env.Raw, "invalid inductive datatype declaration, incorrect number of parameters");
                prms.Add(lctx.MkLocalDecl(m_ngen, type.BindingName, type.BindingDomain, type.BindingInfo));
                type = Inst.Instantiate(type.BindingBody, prms[prms.Count - 1]);
            }
            return type;
        }

        public ElimNestedInductiveResult Run()
        {
            if (!lean_is_scalar(m_d.IndNParams)) ThrowIllFormed();
            uint dNParams = (uint)lean_unbox(m_d.IndNParams);
            m_newTypes.AddRange(KList.ToList(m_d.IndTypes));
            if (m_newTypes.Count == 0)
                throw new KernelException(m_env.Raw, "invalid empty (mutual) inductive datatype declaration, it must contain at least one inductive type.");
            GetParams(InductiveType.GetType(m_newTypes[0]), dNParams, m_paramsLCtx, m_params);
            int qhead = 0;
            while (qhead < m_newTypes.Count)
            {
                Obj indType = m_newTypes[qhead];
                var newCnstrs = new List<Obj>();
                foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(indType)))
                {
                    Expr cnstrType = InductiveType.CnstrType(cnstr);
                    var lctx = new LocalCtx();
                    var As = new List<Expr>();
                    cnstrType = GetParams(cnstrType, dNParams, lctx, As);
                    Expr newCnstrType = ReplaceAllNested(lctx, As, cnstrType);
                    newCnstrType = lctx.MkPi(As, newCnstrType);
                    newCnstrs.Add(InductiveType.MkCnstr(InductiveType.CnstrName(cnstr), newCnstrType));
                }
                m_newTypes[qhead] = InductiveType.Mk(InductiveType.GetName(indType), InductiveType.GetType(indType), KList.OfOwned(newCnstrs));
                qhead++;
            }
            Declaration auxDecl = Declaration.MkInductiveDecl(m_d.IndLParams, m_d.IndNParams, KList.OfBorrowed(m_newTypes), m_d.IndIsUnsafe);
            return new ElimNestedInductiveResult(m_ngen, m_params, m_paramsLCtx, m_nestedAux, auxDecl);
        }
    }

    static (Obj, Dictionary<Name, Name>) MkAuxRecNameMap(Environment auxEnv, Declaration d)
    {
        int ntypes = KList.Length(d.IndTypes);
        Obj mainType = KList.Head(d.IndTypes);
        Name mainName = InductiveType.GetName(mainType);
        ConstantInfo mainInfo = auxEnv.Get(mainName);
        Obj allNames = mainInfo.ToInductiveVal().All;
        var oldRecNames = new List<Obj>();
        var recMap = new Dictionary<Name, Name>();
        int i = 0;
        uint nextIdx = 1;
        foreach (var indNameObj in KList.Iter(allNames))
        {
            if (i >= ntypes)
            {
                Name oldRecName = MkRecName(new Name(indNameObj));
                oldRecNames.Add(oldRecName.Raw);
                Name newRecName = MkRecName(mainName).AppendAfter(nextIdx);
                nextIdx++;
                recMap[oldRecName] = newRecName;
            }
            i++;
        }
        return (KList.OfBorrowed(oldRecNames), recMap);
    }

    static void CheckNoNestedAux(Environment env, Name n, Expr e)
    {
        if (ForEachFn.Find(e, (x, _) =>
                (x.IsConst && Name.IsPrefixOf(KConsts.Nested, x.ConstName)) ||
                (x.IsProj && Name.IsPrefixOf(KConsts.Nested, x.ProjSName))).IsSome)
        {
            throw new KernelException(env.Raw, "invalid declaration '" + n + "', it uses the reserved prefix '" + KConsts.Nested + "'");
        }
    }

    /// <summary>`environment::add_inductive` (owned result; `env` is borrowed).</summary>
    public static Obj AddInductive(Environment env, Declaration d)
    {
        foreach (var indType in KList.Iter(d.IndTypes))
        {
            EnvOps.CheckNoMetavarNoFVar(env, InductiveType.GetName(indType), InductiveType.GetType(indType));
            CheckNoNestedAux(env, InductiveType.GetName(indType), InductiveType.GetType(indType));
            foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(indType)))
            {
                EnvOps.CheckNoMetavarNoFVar(env, InductiveType.CnstrName(cnstr), InductiveType.CnstrType(cnstr));
                CheckNoNestedAux(env, InductiveType.CnstrName(cnstr), InductiveType.CnstrType(cnstr));
            }
        }
        CheckUniformIndOccs(env, d);
        ElimNestedInductiveResult res = new ElimNestedInductiveFn(env, d).Run();
        uint nnested = (uint)res.Aux2Nested.Count;
        var diag = new ScopedDiagnostics(env, true);
        Obj auxEnvObj = new AddInductiveFn(env, diag.Get(), res.AuxDecl, nnested).Run();
        if (nnested == 0)
            return diag.Update(auxEnvObj);

        var auxEnv = new Environment(auxEnvObj);
        Obj allIndNames = GetAllInductiveNames(d);
        var (auxRecNames, auxRecNameMap) = MkAuxRecNameMap(auxEnv, d);
        Obj newEnv = RC.Own(env.Raw);
        var newRecNames = new List<Name>();
        void ProcessRec(Name recName)
        {
            Name newRecName = recName;
            if (auxRecNameMap.TryGetValue(recName, out Name nn)) newRecName = nn;
            ConstantInfo recInfo = auxEnv.Get(recName);
            Expr newRecType = res.RestoreNested(recInfo.Type, auxEnv, auxRecNameMap);
            RecursorVal recVal = recInfo.ToRecursorVal();
            var newRules = new List<Obj>();
            foreach (var ruleObj in KList.Iter(recVal.Rules))
            {
                var rule = new RecursorRule(ruleObj);
                Expr newRhs = res.RestoreNested(rule.Rhs, auxEnv, auxRecNameMap);
                Name cnstrName = rule.Cnstr;
                Name newCnstrName = cnstrName;
                if (newRecName != recName)
                    newCnstrName = res.RestoreConstructorName(auxEnv, cnstrName);
                newRules.Add(RecursorRule.Mk(newCnstrName, rule.NFields, newRhs).Raw);
            }
            new Environment(newEnv).CheckName(newRecName);
            var rv = RecursorVal.Mk(newRecName, recInfo.LParams, newRecType, allIndNames, recVal.NParams, recVal.NIndices,
                recVal.NMotives, recVal.NMinors, KList.OfOwned(newRules), recVal.IsK, recVal.IsUnsafe);
            newEnv = EnvOps.AddCore(newEnv, ConstantInfo.Of(ConstantInfoKind.Recursor, rv.Raw));
            newRecNames.Add(newRecName);
        }
        foreach (var indType in KList.Iter(d.IndTypes))
        {
            ConstantInfo indInfo = auxEnv.Get(InductiveType.GetName(indType));
            InductiveVal indVal = indInfo.ToInductiveVal();
            new Environment(newEnv).CheckName(indInfo.Name);
            var iv = InductiveVal.Mk(indInfo.Name, indInfo.LParams, indInfo.Type, indVal.NParams, indVal.NIndices,
                allIndNames, indVal.Cnstrs, indVal.NNested, indVal.IsRec, indVal.IsUnsafe, indVal.IsReflexive);
            newEnv = EnvOps.AddCore(newEnv, ConstantInfo.Of(ConstantInfoKind.Inductive, iv.Raw));
            foreach (var cnstrNameObj in KList.Iter(indVal.Cnstrs))
            {
                ConstantInfo cnstrInfo = auxEnv.Get(new Name(cnstrNameObj));
                ConstructorVal cnstrVal = cnstrInfo.ToConstructorVal();
                Expr newType = res.RestoreNested(cnstrInfo.Type, auxEnv);
                new Environment(newEnv).CheckName(cnstrInfo.Name);
                var cv = ConstructorVal.Mk(cnstrInfo.Name, cnstrInfo.LParams, newType, cnstrVal.Induct, cnstrVal.CIdx,
                    cnstrVal.NParams, cnstrVal.NFields, cnstrVal.IsUnsafe);
                newEnv = EnvOps.AddCore(newEnv, ConstantInfo.Of(ConstantInfoKind.Constructor, cv.Raw));
            }
            ProcessRec(MkRecName(InductiveType.GetName(indType)));
        }
        foreach (var auxRec in KList.Iter(auxRecNames))
            ProcessRec(new Name(auxRec));

        DefinitionSafety ds = d.IndIsUnsafe ? DefinitionSafety.Unsafe : DefinitionSafety.Safe;
        {
            using var tc = new TypeChecker(new Environment(newEnv), res.ParamsLCtx.Raw, diag.Get(), ds);
            foreach (var kv in res.Aux2Nested)
                tc.Check(kv.Value, d.IndLParams);
        }
        {
            var ne = new Environment(newEnv);
            using var tc = new TypeChecker(ne, diag.Get(), ds);
            foreach (var indType in KList.Iter(d.IndTypes))
                foreach (var cnstr in KList.Iter(InductiveType.GetCnstrs(indType)))
                    tc.Check(ne.Get(InductiveType.CnstrName(cnstr)).Type, d.IndLParams);
            foreach (var recName in newRecNames)
            {
                ConstantInfo recInfo = ne.Get(recName);
                tc.Check(recInfo.Type, recInfo.LParams);
                foreach (var ruleObj in KList.Iter(recInfo.ToRecursorVal().Rules))
                    tc.Check(new RecursorRule(ruleObj).Rhs, recInfo.LParams);
            }
        }
        return diag.Update(newEnv);
    }
}
