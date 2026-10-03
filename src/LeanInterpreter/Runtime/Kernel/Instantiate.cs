// Port of kernel/instantiate.cpp and kernel/abstract.cpp.

using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

internal static class Inst
{
    /// <summary>`map_reuse` on a list of levels (`f` is applied from the last element to the first).</summary>
    public static Obj MapReuseLevels(Obj l, Func<Level, Level> f)
    {
        if (lean_is_scalar(l)) return l;
        var cells = new List<Obj>();
        for (Obj it = l; !lean_is_scalar(it); it = lean_ctor_get(it, 1)) cells.Add(it);
        int i = cells.Count;
        while (i > 0)
        {
            --i;
            Obj curr = cells[i];
            Level h = new Level(lean_ctor_get(curr, 0));
            Level newH = f(h);
            if (!ReferenceEquals(newH.Raw, h.Raw))
            {
                Obj r = KList.Cons(RC.Own(newH.Raw), RC.Own(lean_ctor_get(curr, 1)));
                while (i > 0)
                {
                    --i;
                    Level hh = new Level(lean_ctor_get(cells[i], 0));
                    r = KList.Cons(RC.Own(f(hh).Raw), r);
                }
                return r;
            }
        }
        return l;
    }

    // ---------------------------------------------------------------------------------------
    // instantiate

    /// <summary>Replace loose bound variables `s .. s+n-1` in `a` with `subst[0] .. subst[n-1]` (with offset `soff`).</summary>
    public static Expr Instantiate(Expr a, uint s, uint n, IReadOnlyList<Expr> subst, int soff = 0)
    {
        if (s >= a.LooseBVarRange || n == 0) return a;
        return ReplaceFn.Replace(a, (m, offset) =>
        {
            uint s1 = s + offset;
            if (s1 < s) return m;
            if (s1 >= m.LooseBVarRange) return m;
            if (m.IsBVar)
            {
                Obj vidx = m.BVarIdx;
                if (Nat.Ge(vidx, s1))
                {
                    uint h = s1 + n;
                    if (h < s1 || (lean_is_scalar(vidx) && lean_unbox(vidx) < h))
                        return Expr.LiftLooseBVars(subst[soff + (int)(lean_unbox(vidx) - s1)], offset);
                    return Expr.MkBVar(Nat.Sub(vidx, n));
                }
            }
            return Expr.None;
        });
    }

    public static Expr Instantiate(Expr e, uint n, IReadOnlyList<Expr> s, int soff = 0) => Instantiate(e, 0, n, s, soff);
    public static Expr Instantiate(Expr e, IReadOnlyList<Expr> s) => Instantiate(e, 0, (uint)s.Count, s, 0);
    public static Expr Instantiate(Expr e, uint i, Expr s) => Instantiate(e, i, 1, new[] { s }, 0);
    public static Expr Instantiate(Expr e, Expr s) => Instantiate(e, 0, 1, new[] { s }, 0);

    /// <summary>`lean_expr_instantiate_core`: `subst` are `n` borrowed Lean objects starting at `off`.</summary>
    public static Expr InstantiateCore(Expr a, ulong n, Obj[] subst, ulong off)
    {
        return ReplaceFn.Replace(a, (m, offset) =>
        {
            if (offset >= m.LooseBVarRange) return m;
            if (m.IsBVar)
            {
                Obj vidx = m.BVarIdx;
                if (Nat.Ge(vidx, offset))
                {
                    ulong h = offset + n;
                    if (h < offset || (lean_is_scalar(vidx) && lean_unbox(vidx) < h))
                    {
                        Obj v = subst[off + (lean_unbox(vidx) - offset)];
                        return Expr.LiftLooseBVars(new Expr(v), offset);
                    }
                    return Expr.MkBVar(Nat.Sub(vidx, n));
                }
            }
            return Expr.None;
        });
    }

    /// <summary>`lean_expr_instantiate_rev_core`.</summary>
    public static Expr InstantiateRevCore(Expr a, ulong n, Obj[] subst, ulong off)
    {
        return ReplaceFn.Replace(a, (m, offset) =>
        {
            if (offset >= m.LooseBVarRange) return m;
            if (m.IsBVar)
            {
                Obj vidx = m.BVarIdx;
                if (Nat.Ge(vidx, offset))
                {
                    ulong h = offset + n;
                    if (h < offset || (lean_is_scalar(vidx) && lean_unbox(vidx) < h))
                    {
                        Obj v = subst[off + (n - (lean_unbox(vidx) - offset) - 1)];
                        return Expr.LiftLooseBVars(new Expr(v), offset);
                    }
                    return Expr.MkBVar(Nat.Sub(vidx, n));
                }
            }
            return Expr.None;
        });
    }

    /// <summary>Replace loose bound variables `0 .. n-1` with `subst[n-1] .. subst[0]`.</summary>
    public static Expr InstantiateRev(Expr a, int n, IReadOnlyList<Expr> subst, int soff = 0)
    {
        if (!a.HasLooseBVars) return a;
        return ReplaceFn.Replace(a, (m, offset) =>
        {
            if (offset >= m.LooseBVarRange) return m;
            if (m.IsBVar)
            {
                Obj vidx = m.BVarIdx;
                if (Nat.Ge(vidx, offset))
                {
                    ulong h = (ulong)offset + (ulong)n;
                    if (h < offset || (lean_is_scalar(vidx) && lean_unbox(vidx) < h))
                        return Expr.LiftLooseBVars(subst[soff + (int)((ulong)n - (lean_unbox(vidx) - offset) - 1)], offset);
                    return Expr.MkBVar(Nat.Sub(vidx, (ulong)n));
                }
            }
            return Expr.None;
        });
    }

    public static Expr InstantiateRev(Expr a, IReadOnlyList<Expr> subst) => InstantiateRev(a, subst.Count, subst, 0);

    // ---------------------------------------------------------------------------------------
    // beta reduction

    static Expr ApplyBetaRec(Expr e, uint i, uint numRevArgs, IReadOnlyList<Expr> revArgs, bool preserveData, bool zeta)
    {
        while (true)
        {
            if (e.IsLambda)
            {
                if (i + 1 < numRevArgs) { e = e.BindingBody; i++; continue; }
                return Instantiate(e.BindingBody, numRevArgs, revArgs);
            }
            else if (e.IsLet)
            {
                if (zeta && i < numRevArgs) { e = Instantiate(e.LetBody, e.LetValue); continue; }
                uint n = numRevArgs - i;
                return Expr.MkRevApp(Instantiate(e, i, revArgs, (int)n), (int)n, revArgs);
            }
            else if (e.IsMData)
            {
                if (preserveData)
                {
                    uint n = numRevArgs - i;
                    return Expr.MkRevApp(Instantiate(e, i, revArgs, (int)n), (int)n, revArgs);
                }
                e = e.MDataExpr;
                continue;
            }
            else
            {
                uint n = numRevArgs - i;
                return Expr.MkRevApp(Instantiate(e, i, revArgs, (int)n), (int)n, revArgs);
            }
        }
    }

    public static Expr ApplyBeta(Expr f, uint numRevArgs, IReadOnlyList<Expr> revArgs, bool preserveData = true, bool zeta = false)
    {
        if (numRevArgs == 0) return f;
        return ApplyBetaRec(f, 0, numRevArgs, revArgs, preserveData, zeta);
    }

    public static Expr CheapBetaReduce(Expr e)
    {
        if (!e.IsApp) return e;
        Expr fn = Expr.GetAppFn(e);
        if (!fn.IsLambda) return e;
        var args = new List<Expr>();
        Expr.GetAppArgs(e, args);
        int i = 0;
        while (fn.IsLambda && i < args.Count) { i++; fn = fn.BindingBody; }
        if (!fn.HasLooseBVars)
            return Expr.MkApp(fn, args.Count - i, args, i);
        if (fn.IsBVar)
            return Expr.MkApp(args[i - (int)lean_unbox(fn.BVarIdx) - 1], args.Count - i, args, i);
        return e;
    }

    // ---------------------------------------------------------------------------------------
    // universe level parameters

    public static Expr InstantiateLParams(Expr e, Obj lps, Obj ls)
    {
        if (!e.HasUnivParam) return e;
        return ReplaceFn.Replace(e, x =>
        {
            if (!x.HasUnivParam) return x;
            if (x.IsConst)
                return Expr.UpdateConst(x, MapReuseLevels(x.ConstLevels, l => Level.Instantiate(l, lps, ls)));
            if (x.IsSort)
                return Expr.UpdateSort(x, Level.Instantiate(x.SortLevel, lps, ls));
            return Expr.None;
        });
    }

    public static Expr InstantiateTypeLParams(ConstantInfo info, Obj ls)
    {
        if (info.NumLParams != KList.Length(ls))
            throw lean_internal_panic("#universes mismatch at instantiateTypeLevelParams");
        if (KList.IsNil(ls) || !info.Type.HasUnivParam) return info.Type;
        return InstantiateLParams(info.Type, info.LParams, ls);
    }

    public static Expr InstantiateValueLParams(ConstantInfo info, Obj ls)
    {
        if (info.NumLParams != KList.Length(ls))
            throw lean_internal_panic("#universes mismatch at instantiateValueLevelParams");
        if (!info.HasValue())
            throw lean_internal_panic("definition/theorem expected at instantiateValueLevelParams");
        Expr v = info.GetValue();
        if (KList.IsNil(ls) || !v.HasUnivParam) return v;
        return InstantiateLParams(v, info.LParams, ls);
    }

    // ---------------------------------------------------------------------------------------
    // abstract

    /// <summary>Replace the free variables `s[0] .. s[n-1]` in `e` with `#(n-1) .. #0`.</summary>
    public static Expr Abstract(Expr e, int n, IReadOnlyList<Expr> subst, int soff = 0)
    {
        if (!e.HasFVar) return e;
        return ReplaceFn.Replace(e, (m, offset) =>
        {
            if (!m.HasFVar) return m;
            if (m.IsFVar)
            {
                int i = n;
                while (i > 0)
                {
                    --i;
                    if (subst[soff + i].FVarName == m.FVarName)
                        return Expr.MkBVar((ulong)offset + (ulong)n - (ulong)i - 1);
                }
                return Expr.None;
            }
            return Expr.None;
        });
    }

    public static Expr Abstract(Expr e, IReadOnlyList<Expr> subst) => Abstract(e, subst.Count, subst, 0);
    public static Expr Abstract(Expr e, Expr s) => Abstract(e, 1, new[] { s }, 0);

    /// <summary>`lean_expr_abstract_core`: `subst` is a Lean array of free/meta variables.</summary>
    public static Expr AbstractCore(Expr e, ulong n, Obj subst)
    {
        if (!e.HasFVar && !e.HasMVar) return e;
        return ReplaceFn.Replace(e, (m, offset) =>
        {
            if (!m.HasFVar && !m.HasMVar) return m;
            bool fv = m.IsFVar;
            bool mv = m.IsMVar;
            if (fv || mv)
            {
                ulong i = n;
                while (i > 0)
                {
                    --i;
                    Obj v = lean_array_get_core(subst, i);
                    if (fv && v.m_tag == (byte)ExprKind.FVar && Name.Eq(lean_ctor_get(v, 0), m.FVarName.Raw))
                        return Expr.MkBVar((ulong)offset + n - i - 1);
                    if (mv && v.m_tag == (byte)ExprKind.MVar && Name.Eq(lean_ctor_get(v, 0), m.MVarName.Raw))
                        return Expr.MkBVar((ulong)offset + n - i - 1);
                }
                return Expr.None;
            }
            return Expr.None;
        });
    }
}
