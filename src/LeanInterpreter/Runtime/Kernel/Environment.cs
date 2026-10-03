// Port of kernel/environment.{h,cpp} and kernel/local_ctx.{h,cpp}.

using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

/// <summary>Borrowed view of a `Lean.Kernel.Environment`.</summary>
public readonly struct Environment
{
    public readonly Obj Raw;
    public Environment(Obj raw) { Raw = raw; }

    /// <summary>Return the constant with name `n`, or a null `ConstantInfo`.</summary>
    public ConstantInfo Find(Name n)
    {
        // The `Option` result is intentionally never released: it keeps the constant alive
        // (and its reference count positive) while we use it.
        Obj o = KX.EnvironmentFind(RC.Own(Raw), RC.Own(n.Raw));
        if (lean_is_scalar(o)) return default;
        return new ConstantInfo(lean_ctor_get(o, 0));
    }

    public ConstantInfo Get(Name n)
    {
        var r = Find(n);
        if (r.IsNull) throw new UnknownConstantException(Raw, n);
        return r;
    }

    public bool IsQuotInitialized => KX.EnvironmentQuotInit(RC.Own(Raw)) != 0;

    /// <summary>`get_diag` (owned result).</summary>
    public Obj GetDiag() => KX.KernelGetDiag(RC.Own(Raw));

    public void CheckName(Name n)
    {
        if (!Find(n).IsNull) throw new AlreadyDeclaredException(Raw, n);
    }

    public void CheckDuplicatedUnivParams(Obj ls)
    {
        while (!KList.IsNil(ls))
        {
            Name p = new Name(KList.Head(ls));
            ls = KList.Tail(ls);
            if (Level.NameListContains(ls, p))
                throw new KernelException(Raw, "failed to add declaration to environment, duplicate universe level parameter: '" + p + "'");
        }
    }
}

/// <summary>Wrapper for `Kernel.Diagnostics` (the object is threaded linearly).</summary>
internal sealed class Diagnostics
{
    /// <summary>Owned `Kernel.Diagnostics` object.</summary>
    public Obj Obj;
    public Diagnostics(Obj owned) { Obj = owned; }

    public void RecordUnfold(Name declName)
    {
        Obj = KX.KernelRecordUnfold(Obj, RC.Own(declName.Raw));
    }
}

/// <summary>`scoped_diagnostics`: collect diagnostics only if they are enabled in the environment.</summary>
internal sealed class ScopedDiagnostics
{
    readonly Diagnostics m_diag;

    public ScopedDiagnostics(Environment env, bool collect)
    {
        if (collect)
        {
            Obj d = env.GetDiag();
            if (KX.KernelDiagIsEnabled(RC.Own(d)) != 0)
                m_diag = new Diagnostics(d);
        }
    }

    public Diagnostics Get() => m_diag;

    /// <summary>`update(env)`: takes an owned environment and returns an owned environment.</summary>
    public Obj Update(Obj envOwned)
    {
        if (m_diag != null) return KX.KernelSetDiag(envOwned, RC.Own(m_diag.Obj));
        return envOwned;
    }
}

/// <summary>View of a `Lean.LocalDecl`.</summary>
/// <remarks>
/// cdecl (index fvarId userName type) (bi kind : UInt8) | ldecl (index fvarId userName type value) (nondep kind : UInt8)
/// </remarks>
public readonly struct LocalDecl
{
    public readonly Obj Raw;
    public LocalDecl(Obj raw) { Raw = raw; }
    public bool IsNull => Raw == null;
    public uint Idx => (uint)lean_unbox(lean_ctor_get(Raw, 0));
    public Name Name => new Name(lean_ctor_get(Raw, 1));
    public Name UserName => new Name(lean_ctor_get(Raw, 2));
    public Expr Type => new Expr(lean_ctor_get(Raw, 3));
    public Expr Value => Raw.m_tag == 0 ? Expr.None : new Expr(lean_ctor_get(Raw, 4));
    /// <summary>`lean_local_decl_binder_info`.</summary>
    public BinderInfo Info => Raw.m_tag == 0 ? (BinderInfo)lean_ctor_get_uint8_s(Raw, 0) : BinderInfo.Default;
    public Expr MkRef() => Expr.MkFVar(Name);
}

/// <summary>
/// `local_ctx`: a mutable holder for an owned `Lean.LocalContext` object. As in C++, adding a
/// declaration moves the object into the Lean function (updating it destructively when unshared).
/// </summary>
internal sealed class LocalCtx
{
    /// <summary>Owned `LocalContext` object.</summary>
    public Obj Raw;

    public LocalCtx() { Raw = KX.MkEmptyLocalCtx(lean_box(0)); }
    /// <summary>Takes ownership of `owned`.</summary>
    public LocalCtx(Obj owned) { Raw = owned; }

    /// <summary>Copy (`local_ctx(local_ctx const &)`).</summary>
    public LocalCtx Copy() => new LocalCtx(RC.Own(Raw));

    /// <summary>Low level `mk_local_decl` for let-declarations.</summary>
    public void MkLocalDeclCore(Name n, Name un, Expr type, Expr value)
    {
        Raw = KX.LocalCtxMkLetDecl(Raw, RC.Own(n.Raw), RC.Own(un.Raw), RC.Own(type.Raw), RC.Own(value.Raw), 0);
    }

    /// <summary>Low level `mk_local_decl`.</summary>
    public void MkLocalDeclCore(Name n, Name un, Expr type, BinderInfo bi)
    {
        Raw = KX.LocalCtxMkLocalDecl(Raw, RC.Own(n.Raw), RC.Own(un.Raw), RC.Own(type.Raw), (byte)bi);
    }

    public Expr MkLocalDecl(NameGenerator g, Name un, Expr type, BinderInfo bi = BinderInfo.Default)
    {
        Name n = g.Next();
        MkLocalDeclCore(n, un, type, bi);
        return Expr.MkFVar(n);
    }

    public Expr MkLocalDecl(NameGenerator g, Name un, Expr type, Expr value)
    {
        Name n = g.Next();
        MkLocalDeclCore(n, un, type, value);
        return Expr.MkFVar(n);
    }

    public LocalDecl FindLocalDecl(Name n)
    {
        // The `Option` result is never released (it keeps the declaration alive).
        Obj o = KX.LocalCtxFind(RC.Own(Raw), RC.Own(n.Raw));
        if (lean_is_scalar(o)) return default;
        return new LocalDecl(lean_ctor_get(o, 0));
    }

    public LocalDecl FindLocalDecl(Expr e) => FindLocalDecl(e.FVarName);

    public LocalDecl GetLocalDecl(Name n)
    {
        var r = FindLocalDecl(n);
        if (r.IsNull) throw new KernelError("unknown free variable: " + n);
        return r;
    }

    public LocalDecl GetLocalDecl(Expr e) => GetLocalDecl(e.FVarName);

    public Expr GetType(Expr e) => GetLocalDecl(e).Type;

    Expr MkBinding(bool isLambda, int num, IReadOnlyList<Expr> fvars, Expr b, bool removeDeadLet)
    {
        Expr r = Inst.Abstract(b, num, fvars);
        int i = num;
        while (i > 0)
        {
            --i;
            LocalDecl decl = GetLocalDecl(fvars[i].FVarName);
            Expr optVal = decl.Value;
            if (optVal.IsSome)
            {
                if (!removeDeadLet || Expr.HasLooseBVar(r, 0))
                {
                    Expr type = Inst.Abstract(decl.Type, i, fvars);
                    Expr value = Inst.Abstract(optVal, i, fvars);
                    r = Expr.MkLet(decl.UserName, type, value, r);
                }
                else
                {
                    r = Expr.LowerLooseBVars(r, 1, 1);
                }
            }
            else if (isLambda)
            {
                Expr type = Inst.Abstract(decl.Type, i, fvars);
                r = Expr.MkLambda(decl.UserName, type, r, decl.Info);
            }
            else
            {
                Expr type = Inst.Abstract(decl.Type, i, fvars);
                r = Expr.MkPi(decl.UserName, type, r, decl.Info);
            }
        }
        return r;
    }

    public Expr MkLambda(IReadOnlyList<Expr> fvars, Expr e, bool removeDeadLet = false) => MkBinding(true, fvars.Count, fvars, e, removeDeadLet);
    public Expr MkPi(IReadOnlyList<Expr> fvars, Expr e, bool removeDeadLet = false) => MkBinding(false, fvars.Count, fvars, e, removeDeadLet);
    public Expr MkLambda(Expr fvar, Expr e) => MkBinding(true, 1, new[] { fvar }, e, false);
    public Expr MkPi(Expr fvar, Expr e) => MkBinding(false, 1, new[] { fvar }, e, false);
}

/// <summary>Adding declarations to the environment (`environment::add*`).</summary>
internal static class EnvOps
{
    static void CheckNoMetavar(Environment env, Name n, Expr e)
    {
        if (e.HasMVar) throw new DeclarationHasMetavarsException(env.Raw, n, e);
    }

    static void CheckNoFVar(Environment env, Name n, Expr e)
    {
        if (e.HasFVar) throw new DeclarationHasFreeVarsException(env.Raw, n, e);
    }

    public static void CheckNoMetavarNoFVar(Environment env, Name n, Expr e)
    {
        CheckNoMetavar(env, n, e);
        CheckNoFVar(env, n, e);
    }

    /// <summary>`environment::add(constant_info)` (owned result).</summary>
    public static Obj Add(Environment env, ConstantInfo info) => KX.EnvironmentAdd(RC.Own(env.Raw), RC.Own(info.Raw));

    /// <summary>`environment::add_core`: moves `envOwned`, returns the owned result.</summary>
    public static Obj AddCore(Obj envOwned, ConstantInfo info) => KX.EnvironmentAdd(envOwned, RC.Own(info.Raw));

    static void CheckConstantVal(Environment env, ConstantVal v, TypeChecker checker)
    {
        env.CheckName(v.Name);
        env.CheckDuplicatedUnivParams(v.LParams);
        CheckNoMetavarNoFVar(env, v.Name, v.Type);
        Expr sort = checker.Check(v.Type, v.LParams);
        checker.EnsureSort(sort, v.Type);
    }

    static void CheckConstantVal(Environment env, ConstantVal v, Diagnostics diag, bool safeOnly)
    {
        using var checker = new TypeChecker(env, diag, safeOnly ? DefinitionSafety.Safe : DefinitionSafety.Unsafe);
        CheckConstantVal(env, v, checker);
    }

    static Obj AddAxiom(Environment env, Declaration d, bool check)
    {
        var diag = new ScopedDiagnostics(env, check);
        var v = d.ToConstantVal();
        if (check) CheckConstantVal(env, v, diag.Get(), !d.IsUnsafe);
        return diag.Update(Add(env, new ConstantInfo(d.Raw)));
    }

    static Obj AddDefinition(Environment env, Declaration d, bool check)
    {
        var diag = new ScopedDiagnostics(env, check);
        DefinitionVal v = d.ToDefinitionVal();
        if (v.IsUnsafe)
        {
            if (check)
            {
                using var checker = new TypeChecker(env, diag.Get(), DefinitionSafety.Unsafe);
                CheckConstantVal(env, v.CVal, checker);
            }
            Obj newEnvObj = Add(env, new ConstantInfo(d.Raw));
            if (check)
            {
                var newEnv = new Environment(newEnvObj);
                using var checker = new TypeChecker(newEnv, diag.Get(), DefinitionSafety.Unsafe);
                CheckNoMetavarNoFVar(newEnv, v.Name, v.Value);
                Expr valType = checker.Check(v.Value, v.LParams);
                if (!checker.IsDefEq(valType, v.Type))
                    throw new DefinitionTypeMismatchException(newEnv.Raw, d.Raw, valType);
            }
            return diag.Update(newEnvObj);
        }
        else
        {
            if (check)
            {
                using var checker = new TypeChecker(env, diag.Get());
                CheckConstantVal(env, v.CVal, checker);
                CheckNoMetavarNoFVar(env, v.Name, v.Value);
                Expr valType = checker.Check(v.Value, v.LParams);
                if (!checker.IsDefEq(valType, v.Type))
                    throw new DefinitionTypeMismatchException(env.Raw, d.Raw, valType);
            }
            return diag.Update(Add(env, new ConstantInfo(d.Raw)));
        }
    }

    static Obj AddTheorem(Environment env, Declaration d, bool check)
    {
        var diag = new ScopedDiagnostics(env, check);
        ConstantVal cv = d.ToConstantVal();
        if (check)
        {
            using var checker = new TypeChecker(env, diag.Get());
            var share = new ShareCommon();
            Expr val = new Expr(share.Share(d.Value.Raw));
            Expr type = new Expr(share.Share(cv.Type.Raw));
            CheckConstantVal(env, cv, checker);
            if (!checker.IsProp(type))
                throw new TheoremTypeIsNotPropException(env.Raw, cv.Name, type);
            CheckNoMetavarNoFVar(env, cv.Name, val);
            Expr valType = checker.Check(val, cv.LParams);
            if (!checker.IsDefEq(valType, type))
                throw new DefinitionTypeMismatchException(env.Raw, d.Raw, valType);
        }
        return diag.Update(Add(env, new ConstantInfo(d.Raw)));
    }

    static Obj AddOpaque(Environment env, Declaration d, bool check)
    {
        var diag = new ScopedDiagnostics(env, check);
        ConstantVal cv = d.ToConstantVal();
        if (check)
        {
            using var checker = new TypeChecker(env, diag.Get());
            CheckConstantVal(env, cv, checker);
            CheckNoMetavarNoFVar(env, cv.Name, d.Value);
            Expr valType = checker.Check(d.Value, cv.LParams);
            if (!checker.IsDefEq(valType, cv.Type))
                throw new DefinitionTypeMismatchException(env.Raw, d.Raw, valType);
        }
        return diag.Update(Add(env, new ConstantInfo(d.Raw)));
    }

    static Obj AddMutual(Environment env, Declaration d, bool check)
    {
        var diag = new ScopedDiagnostics(env, check);
        Obj vs = d.DefinitionVals;
        if (KList.IsNil(vs))
            throw new KernelException(env.Raw, "invalid empty mutual definition");
        var vals = new List<DefinitionVal>();
        foreach (var o in KList.Iter(vs)) vals.Add(new DefinitionVal(o));
        DefinitionSafety safety = vals[0].Safety;
        if (safety == DefinitionSafety.Safe)
            throw new KernelException(env.Raw, "invalid mutual definition, declaration is not tagged as unsafe/partial");
        Obj lparams = vals[0].LParams;
        if (check)
        {
            using var checker = new TypeChecker(env, diag.Get(), safety);
            var found = new HashSet<Name>();
            foreach (var v in vals)
            {
                if (v.Safety != safety)
                    throw new KernelException(env.Raw, "invalid mutual definition, declarations must have the same safety annotation");
                if (!NameListEq(v.LParams, lparams))
                    throw new KernelException(env.Raw, "invalid mutual definition, declarations must have the same universe level parameters");
                if (found.Contains(v.Name))
                    throw new KernelException(env.Raw, "invalid mutual definition, duplicate declaration name '" + v.Name + "'");
                found.Add(v.Name);
                CheckConstantVal(env, v.CVal, checker);
            }
        }
        Obj newEnvObj = RC.Own(env.Raw);
        foreach (var v in vals)
            newEnvObj = AddCore(newEnvObj, ConstantInfo.Of(ConstantInfoKind.Definition, v.Raw));
        if (check)
        {
            var newEnv = new Environment(newEnvObj);
            using var checker = new TypeChecker(newEnv, diag.Get(), safety);
            foreach (var v in vals)
            {
                CheckNoMetavarNoFVar(newEnv, v.Name, v.Value);
                Expr valType = checker.Check(v.Value, v.LParams);
                if (!checker.IsDefEq(valType, v.Type))
                    throw new DefinitionTypeMismatchException(newEnv.Raw, d.Raw, valType);
            }
        }
        return diag.Update(newEnvObj);
    }

    /// <summary>Equality of lists of names (`names != names`).</summary>
    public static bool NameListEq(Obj l1, Obj l2)
    {
        while (!lean_is_scalar(l1) && !lean_is_scalar(l2))
        {
            if (ReferenceEquals(l1, l2)) return true;
            if (!Name.Eq(lean_ctor_get(l1, 0), lean_ctor_get(l2, 0))) return false;
            l1 = lean_ctor_get(l1, 1);
            l2 = lean_ctor_get(l2, 1);
        }
        return lean_is_scalar(l1) && lean_is_scalar(l2);
    }

    /// <summary>`environment::add(declaration, check)` (owned result; `env` is borrowed).</summary>
    public static Obj AddDecl(Environment env, Declaration d, bool check = true)
    {
        switch (d.Kind)
        {
            case DeclarationKind.Axiom: return AddAxiom(env, d, check);
            case DeclarationKind.Definition: return AddDefinition(env, d, check);
            case DeclarationKind.Theorem: return AddTheorem(env, d, check);
            case DeclarationKind.Opaque: return AddOpaque(env, d, check);
            case DeclarationKind.MutualDefinition: return AddMutual(env, d, check);
            case DeclarationKind.Quot: return Quot.AddQuot(env);
            case DeclarationKind.Inductive: return Inductive.AddInductive(env, d);
        }
        throw lean_internal_panic_unreachable();
    }
}
