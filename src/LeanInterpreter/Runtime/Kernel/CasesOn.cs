// Port of library/constructions/cases_on.cpp (`mk_cases_on`).

using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

internal static class CasesOn
{
    /// <summary>Given `C := As -> Type`, return `As -> unit`.</summary>
    static Expr MkPiUnit(Expr C, Expr unit)
    {
        if (C.IsPi) return Expr.MkPi(C.BindingName, C.BindingDomain, MkPiUnit(C.BindingBody, unit));
        return unit;
    }

    /// <summary>Given `C := As -> Type`, return `fun (xs : As), unit`.</summary>
    static Expr MkFunUnit(Expr C, Expr unit)
    {
        if (C.IsPi) return Expr.MkLambda(C.BindingName, C.BindingDomain, MkFunUnit(C.BindingBody, unit));
        return unit;
    }

    static bool IsTypeFormerArg(List<Name> CIds, Expr arg)
    {
        Expr fn = Expr.GetAppFn(arg);
        return fn.IsFVar && CIds.Contains(fn.FVarName);
    }

    public static Declaration MkCasesOn(Environment env, Name n)
    {
        ConstantInfo indInfo = env.Get(n);
        if (!indInfo.IsInductive)
            throw new KernelError("error in 'casesOn' generation, '" + n + "' is not an inductive datatype");
        Name casesOnName = Name.Mk(n, "casesOn");
        var lctx = new LocalCtx();
        InductiveVal indVal = indInfo.ToInductiveVal();
        var ngen = new NameGenerator(KConsts.ConstructionsFresh);
        Name recName = Inductive.MkRecName(n);
        ConstantInfo recInfo = env.Get(recName);
        RecursorVal recVal = recInfo.ToRecursorVal();
        int numIndices = (int)recVal.NIndices;
        int numMinors = (int)recVal.NMinors;
        int numMotives = (int)recVal.NMotives;
        int numParams = (int)recVal.NParams;
        var indNames = new List<Name>();
        foreach (var o in KList.Iter(recVal.All)) indNames.Add(new Name(o));
        var recFVars = new List<Expr>();
        Expr recType = recInfo.Type;
        while (recType.IsPi)
        {
            Expr local = lctx.MkLocalDecl(ngen, recType.BindingName, recType.BindingDomain, recType.BindingInfo);
            recType = Inst.Instantiate(recType.BindingBody, local);
            recFVars.Add(local);
        }

        Obj lvls = Level.LParamsToLevels(recInfo.LParams);
        bool elimToProp = recInfo.NumLParams == indInfo.NumLParams;
        Level elimLvl = elimToProp ? Level.Zero : new Level(KList.Head(lvls));
        Expr unit = Expr.MkConst(KConsts.PUnit, elimLvl);
        Expr star = Expr.MkConst(KConsts.PUnitUnit, elimLvl);

        var casesOnParams = new List<Expr>();
        Expr recCnst = Expr.MkConst(recName, lvls);
        var recArgs = new List<Expr>();

        for (int k = 0; k < numParams; k++)
        {
            casesOnParams.Add(recFVars[k]);
            recArgs.Add(recFVars[k]);
        }

        var CIds = new List<Name>();
        int i = numParams;
        Name CMainId = Name.Anonymous;
        for (int j = 0; j < numMotives; j++)
        {
            CIds.Add(recFVars[i].FVarName);
            if (j < indNames.Count && indNames[j] == n)
            {
                casesOnParams.Add(recFVars[i]);
                recArgs.Add(recFVars[i]);
                CMainId = recFVars[i].FVarName;
            }
            else
            {
                recArgs.Add(MkFunUnit(lctx.GetType(recFVars[i]), unit));
            }
            i++;
        }

        for (int k = 0; k < numIndices + 1; k++)
            casesOnParams.Add(recFVars[numParams + numMotives + numMinors + k]);

        void ProcessMinor(Expr minor, bool isMain)
        {
            var minorNonRecParams = new List<Expr>();
            var minorParams = new List<Expr>();
            LocalDecl minorDecl = lctx.GetLocalDecl(minor);
            Expr minorType = minorDecl.Type;
            while (minorType.IsPi)
            {
                Expr currType = minorType.BindingDomain;
                Expr local = lctx.MkLocalDecl(ngen, minorType.BindingName, currType, minorType.BindingInfo);
                Expr it = currType;
                while (it.IsPi) it = it.BindingBody;
                if (IsTypeFormerArg(CIds, it))
                {
                    if (Expr.GetAppFn(it).FVarName == CMainId)
                    {
                        minorParams.Add(local);
                    }
                    else
                    {
                        Expr newLocal = lctx.MkLocalDecl(ngen, minorType.BindingName, MkPiUnit(currType, unit), minorType.BindingInfo);
                        minorParams.Add(newLocal);
                    }
                }
                else
                {
                    minorParams.Add(local);
                    if (isMain) minorNonRecParams.Add(local);
                }
                minorType = Inst.Instantiate(minorType.BindingBody, local);
            }
            if (isMain)
            {
                Expr newC = lctx.MkLocalDecl(ngen, minorDecl.UserName, lctx.MkPi(minorNonRecParams, minorType), minorDecl.Info);
                casesOnParams.Add(newC);
                Expr newCApp = Expr.MkApp(newC, minorNonRecParams);
                Expr recArg = lctx.MkLambda(minorParams, newCApp);
                recArgs.Add(recArg);
            }
            else
            {
                recArgs.Add(lctx.MkLambda(minorParams, star));
            }
        }

        int minorIdx = 0;
        foreach (var JName in indNames)
        {
            ConstantInfo JInfo = env.Get(JName);
            InductiveVal JVal = JInfo.ToInductiveVal();
            int numCnstrs = KList.Length(JVal.Cnstrs);
            for (int k = 0; k < numCnstrs; k++)
            {
                Expr minor = recFVars[numParams + numMotives + minorIdx];
                ProcessMinor(minor, JName == n);
                minorIdx++;
            }
        }
        for (; minorIdx < numMinors; minorIdx++)
        {
            Expr minor = recFVars[numParams + numMotives + minorIdx];
            ProcessMinor(minor, false);
        }

        for (int k = 0; k < numIndices + 1; k++)
            recArgs.Add(recFVars[numParams + numMotives + numMinors + k]);

        Expr casesOnType = lctx.MkPi(casesOnParams, recType);
        Expr casesOnValue = lctx.MkLambda(casesOnParams, Expr.MkApp(recCnst, recArgs));
        return Declaration.MkDefinitionInferringUnsafe(env, casesOnName, recInfo.LParams, casesOnType, casesOnValue,
            ReducibilityHints.MkAbbreviation());
    }
}
