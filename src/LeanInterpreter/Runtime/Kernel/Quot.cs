// Port of kernel/quot.{h,cpp}: quotient types.

using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

internal static class Quot
{
    public static bool IsDecl(Name n) => n == KConsts.Quot || n == KConsts.QuotLift || n == KConsts.QuotInd || n == KConsts.QuotMk;
    public static bool IsRec(Name n) => n == KConsts.QuotLift || n == KConsts.QuotInd;

    /// <summary>Try to reduce a `Quot.lift` or `Quot.ind` application.</summary>
    public static Expr QuotReduceRec(Expr e, Func<Expr, Expr> whnf)
    {
        Expr fn = Expr.GetAppFn(e);
        if (!fn.IsConst) return Expr.None;
        int mkPos, argPos;
        if (fn.ConstName == KConsts.QuotLift) { mkPos = 5; argPos = 3; }
        else if (fn.ConstName == KConsts.QuotInd) { mkPos = 4; argPos = 3; }
        else return Expr.None;
        var args = new List<Expr>();
        Expr.GetAppArgs(e, args);
        if (args.Count <= mkPos) return Expr.None;

        Expr mk = whnf(args[mkPos]);
        Expr mkFn = Expr.GetAppFn(mk);
        if (!mkFn.IsConst || mkFn.ConstName != KConsts.QuotMk || Expr.GetAppNumArgs(mk) != 3) return Expr.None;

        Expr f = args[argPos];
        Expr r = Expr.MkApp(f, mk.AppArg);
        int elimArity = mkPos + 1;
        if (args.Count > elimArity)
            r = Expr.MkApp(r, args.Count - elimArity, args, elimArity);
        return r;
    }

    static void CheckEqType(Environment env)
    {
        ConstantInfo eqInfo = env.Get(KConsts.Eq);
        if (!eqInfo.IsInductive) throw new KernelError("failed to initialize quot module, environment does not have 'Eq' type");
        InductiveVal eqVal = eqInfo.ToInductiveVal();
        if (KList.Length(eqInfo.LParams) != 1)
            throw new KernelError("failed to initialize quot module, unexpected number of universe params at 'Eq' type");
        if (KList.Length(eqVal.Cnstrs) != 1)
            throw new KernelError("failed to initialize quot module, unexpected number of constructors for 'Eq' type");
        var lctx = new LocalCtx();
        var g = new NameGenerator();
        {
            Level u = Level.MkParam(new Name(KList.Head(eqInfo.LParams)));
            Expr alpha = lctx.MkLocalDecl(g, Name.Str("α"), Expr.MkSort(u), BinderInfo.Implicit);
            Expr expectedEqType = lctx.MkPi(alpha, Expr.MkArrow(alpha, Expr.MkArrow(alpha, Expr.MkProp())));
            if (expectedEqType != eqInfo.Type)
                throw new KernelError("failed to initialize quot module, 'Eq' has an expected type");
        }
        {
            ConstantInfo eqReflInfo = env.Get(new Name(KList.Head(eqVal.Cnstrs)));
            Level u = Level.MkParam(new Name(KList.Head(eqReflInfo.LParams)));
            Expr alpha = lctx.MkLocalDecl(g, Name.Str("α"), Expr.MkSort(u), BinderInfo.Implicit);
            Expr a = lctx.MkLocalDecl(g, Name.Str("a"), alpha);
            Expr expectedEqReflType = lctx.MkPi(new[] { alpha, a }, Expr.MkApp(Expr.MkConst(KConsts.Eq, u), alpha, a, a));
            if (eqReflInfo.Type != expectedEqReflType)
                throw new KernelError("failed to initialize quot module, unexpected type for 'Eq' type constructor");
        }
    }

    static Obj Names(params Name[] ns) => KList.OfBorrowed(ns);

    /// <summary>`environment::add_quot` (owned result; `env` is borrowed).</summary>
    public static Obj AddQuot(Environment env)
    {
        if (env.IsQuotInitialized) return RC.Own(env.Raw);
        CheckEqType(env);
        env.CheckName(KConsts.Quot);
        env.CheckName(KConsts.QuotMk);
        env.CheckName(KConsts.QuotLift);
        env.CheckName(KConsts.QuotInd);
        Obj newEnv = RC.Own(env.Raw);
        Name uName = Name.Str("u");
        var lctx = new LocalCtx();
        var g = new NameGenerator();
        Level u = Level.MkParam(uName);
        Expr sortU = Expr.MkSort(u);
        Expr alpha = lctx.MkLocalDecl(g, Name.Str("α"), sortU, BinderInfo.Implicit);
        Expr r = lctx.MkLocalDecl(g, Name.Str("r"), Expr.MkArrow(alpha, Expr.MkArrow(alpha, Expr.MkProp())));
        // constant {u} quot {α : Sort u} (r : α → α → Prop) : Sort u
        newEnv = EnvOps.AddCore(newEnv, ConstantInfo.Of(ConstantInfoKind.Quot,
            QuotVal.Mk(KConsts.Quot, Names(uName), lctx.MkPi(new[] { alpha, r }, sortU), QuotKind.Type)));
        Expr quotR = Expr.MkApp(Expr.MkConst(KConsts.Quot, u), alpha, r);
        Expr a = lctx.MkLocalDecl(g, Name.Str("a"), alpha);
        // constant {u} quot.mk {α : Sort u} (r : α → α → Prop) (a : α) : @quot.{u} α r
        newEnv = EnvOps.AddCore(newEnv, ConstantInfo.Of(ConstantInfoKind.Quot,
            QuotVal.Mk(KConsts.QuotMk, Names(uName), lctx.MkPi(new[] { alpha, r, a }, quotR), QuotKind.Mk)));
        // make r implicit
        lctx = new LocalCtx();
        alpha = lctx.MkLocalDecl(g, Name.Str("α"), sortU, BinderInfo.Implicit);
        r = lctx.MkLocalDecl(g, Name.Str("r"), Expr.MkArrow(alpha, Expr.MkArrow(alpha, Expr.MkProp())), BinderInfo.Implicit);
        quotR = Expr.MkApp(Expr.MkConst(KConsts.Quot, u), alpha, r);
        a = lctx.MkLocalDecl(g, Name.Str("a"), alpha);
        Name vName = Name.Str("v");
        Level v = Level.MkParam(vName);
        Expr sortV = Expr.MkSort(v);
        Expr beta = lctx.MkLocalDecl(g, Name.Str("β"), sortV, BinderInfo.Implicit);
        Expr f = lctx.MkLocalDecl(g, Name.Str("f"), Expr.MkArrow(alpha, beta));
        Expr b = lctx.MkLocalDecl(g, Name.Str("b"), alpha);
        Expr rab = Expr.MkApp(r, a, b);
        // f a = f b
        Expr faEqFb = Expr.MkApp(Expr.MkConst(KConsts.Eq, v), beta, Expr.MkApp(f, a), Expr.MkApp(f, b));
        // (∀ a b : α, r a b → f a = f b)
        Expr sanity = lctx.MkPi(new[] { a, b }, Expr.MkArrow(rab, faEqFb));
        // constant {u v} quot.lift {α : Sort u} {r : α → α → Prop} {β : Sort v} (f : α → β)
        //   : (∀ a b : α, r a b → f a = f b) → @quot.{u} α r → β
        newEnv = EnvOps.AddCore(newEnv, ConstantInfo.Of(ConstantInfoKind.Quot,
            QuotVal.Mk(KConsts.QuotLift, Names(uName, vName),
                lctx.MkPi(new[] { alpha, r, beta, f }, Expr.MkArrow(sanity, Expr.MkArrow(quotR, beta))), QuotKind.Lift)));
        // {β : @quot.{u} α r → Prop}
        beta = lctx.MkLocalDecl(g, Name.Str("β"), Expr.MkArrow(quotR, Expr.MkProp()), BinderInfo.Implicit);
        Expr quotMkA = Expr.MkApp(Expr.MkConst(KConsts.QuotMk, u), alpha, r, a);
        Expr allQuot = lctx.MkPi(a, Expr.MkApp(beta, quotMkA));
        Expr q = lctx.MkLocalDecl(g, Name.Str("q"), quotR);
        Expr betaQ = Expr.MkApp(beta, q);
        // constant {u} quot.ind {α : Sort u} {r : α → α → Prop} {β : @quot.{u} α r → Prop}
        //   : (∀ a : α, β (@quot.mk.{u} α r a)) → ∀ q : @quot.{u} α r, β q
        newEnv = EnvOps.AddCore(newEnv, ConstantInfo.Of(ConstantInfoKind.Quot,
            QuotVal.Mk(KConsts.QuotInd, Names(uName),
                lctx.MkPi(new[] { alpha, r, beta }, Expr.MkPi(Name.Str("mk"), allQuot, lctx.MkPi(q, betaQ))), QuotKind.Ind)));
        newEnv = KX.EnvironmentMarkQuotInit(newEnv);
        return newEnv;
    }
}
