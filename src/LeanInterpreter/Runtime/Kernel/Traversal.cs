// Port of kernel/replace_fn.cpp, kernel/for_each_fn.cpp, kernel/find_fn.h and
// kernel/expr_eq_fn.cpp.

using System.Runtime.CompilerServices;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

/// <summary>`replace(e, f)`: `f(e, offset)` returns a non-null expression to replace `e`, or `Expr.None` to visit the children.</summary>
internal sealed class ReplaceFn
{
    readonly Dictionary<ObjOffset, Expr> m_cache = new();
    readonly Func<Expr, uint, Expr> m_f;
    readonly bool m_useCache;

    ReplaceFn(Func<Expr, uint, Expr> f, bool useCache) { m_f = f; m_useCache = useCache; }

    public static Expr Replace(Expr e, Func<Expr, uint, Expr> f, bool useCache = true) => new ReplaceFn(f, useCache).Apply(e, 0);

    public static Expr Replace(Expr e, Func<Expr, Expr> f, bool useCache = true) => new ReplaceFn((x, _) => f(x), useCache).Apply(e, 0);

    Expr SaveResult(Expr e, uint offset, Expr r, bool shared)
    {
        if (shared) m_cache[new ObjOffset(e.Raw, offset)] = r;
        return r;
    }

    Expr Apply(Expr e, uint offset)
    {
        bool shared = false;
        if (m_useCache && !RC.IsLikelyUnshared(e.Raw))
        {
            if (m_cache.TryGetValue(new ObjOffset(e.Raw, offset), out var c)) return c;
            shared = true;
        }
        Expr r = m_f(e, offset);
        if (r.IsSome) return SaveResult(e, offset, r, shared);
        KernelLimits.CheckStack("replace");
        switch (e.Kind)
        {
            case ExprKind.Const: case ExprKind.Sort: case ExprKind.BVar:
            case ExprKind.Lit: case ExprKind.MVar: case ExprKind.FVar:
                return SaveResult(e, offset, e, shared);
            case ExprKind.MData:
            {
                Expr newE = Apply(e.MDataExpr, offset);
                return SaveResult(e, offset, Expr.UpdateMData(e, newE), shared);
            }
            case ExprKind.Proj:
            {
                Expr newE = Apply(e.ProjExpr, offset);
                return SaveResult(e, offset, Expr.UpdateProj(e, newE), shared);
            }
            case ExprKind.App:
            {
                Expr newF = Apply(e.AppFn, offset);
                Expr newA = Apply(e.AppArg, offset);
                return SaveResult(e, offset, Expr.UpdateApp(e, newF, newA), shared);
            }
            case ExprKind.Pi: case ExprKind.Lambda:
            {
                Expr newD = Apply(e.BindingDomain, offset);
                Expr newB = Apply(e.BindingBody, offset + 1);
                return SaveResult(e, offset, Expr.UpdateBinding(e, newD, newB), shared);
            }
            case ExprKind.Let:
            {
                Expr newT = Apply(e.LetType, offset);
                Expr newV = Apply(e.LetValue, offset);
                Expr newB = Apply(e.LetBody, offset + 1);
                return SaveResult(e, offset, Expr.UpdateLet(e, newT, newV, newB), shared);
            }
        }
        throw lean_internal_panic_unreachable();
    }
}

/// <summary>`replace_fn` used by `lean_replace_expr`: the replacement function is a Lean closure `Expr → Option Expr`.</summary>
internal sealed class ReplaceClosureFn
{
    readonly Dictionary<Obj, Expr> m_cache = new(ReferenceEqualityComparer.Instance);
    readonly Obj m_f;

    public ReplaceClosureFn(Obj f) { m_f = f; }

    Expr SaveResult(Expr e, Expr r, bool shared)
    {
        if (shared) m_cache[e.Raw] = r;
        return r;
    }

    public Expr Apply(Expr e)
    {
        bool shared = false;
        if (RC.IsShared(e.Raw))
        {
            if (m_cache.TryGetValue(e.Raw, out var c)) return c;
            shared = true;
        }
        lean_inc(e.Raw);
        lean_inc_ref(m_f);
        Obj r = lean_apply_1(m_f, e.Raw);
        if (!lean_is_scalar(r))
        {
            // keep the `some` cell (and hence its content) alive: we never `dec` it
            Expr eNew = new Expr(lean_ctor_get(r, 0));
            return SaveResult(e, eNew, shared);
        }
        KernelLimits.CheckStack("replace");
        switch (e.Kind)
        {
            case ExprKind.Const: case ExprKind.Sort: case ExprKind.BVar:
            case ExprKind.Lit: case ExprKind.MVar: case ExprKind.FVar:
                return SaveResult(e, e, shared);
            case ExprKind.MData:
            {
                Expr newE = Apply(e.MDataExpr);
                return SaveResult(e, Expr.UpdateMData(e, newE), shared);
            }
            case ExprKind.Proj:
            {
                Expr newE = Apply(e.ProjExpr);
                return SaveResult(e, Expr.UpdateProj(e, newE), shared);
            }
            case ExprKind.App:
            {
                Expr newF = Apply(e.AppFn);
                Expr newA = Apply(e.AppArg);
                return SaveResult(e, Expr.UpdateApp(e, newF, newA), shared);
            }
            case ExprKind.Pi: case ExprKind.Lambda:
            {
                Expr newD = Apply(e.BindingDomain);
                Expr newB = Apply(e.BindingBody);
                return SaveResult(e, Expr.UpdateBinding(e, newD, newB), shared);
            }
            case ExprKind.Let:
            {
                Expr newT = Apply(e.LetType);
                Expr newV = Apply(e.LetValue);
                Expr newB = Apply(e.LetBody);
                return SaveResult(e, Expr.UpdateLet(e, newT, newV, newB), shared);
            }
        }
        throw lean_internal_panic_unreachable();
    }
}

/// <summary>Expression visitors (`for_each_fn`, `for_each_offset_fn`).</summary>
internal static class ForEachFn
{
    /// <summary>`for_each_fn&lt;partial_apps&gt;`.</summary>
    sealed class Visitor
    {
        readonly HashSet<Obj> m_cache = new(ReferenceEqualityComparer.Instance);
        readonly Func<Expr, bool> m_f;
        readonly bool m_partialApps;

        public Visitor(Func<Expr, bool> f, bool partialApps) { m_f = f; m_partialApps = partialApps; }

        bool Visited(Expr e)
        {
            if (RC.IsLikelyUnshared(e.Raw)) return false;
            return !m_cache.Add(e.Raw);
        }

        void ApplyFn(Expr e)
        {
            if (e.IsApp) { ApplyFn(e.AppFn); Apply(e.AppArg); }
            else Apply(e);
        }

        public void Apply(Expr e)
        {
            switch (e.Kind)
            {
                case ExprKind.Const: case ExprKind.BVar: case ExprKind.Sort:
                    m_f(e);
                    return;
            }
            if (Visited(e)) return;
            if (!m_f(e)) return;
            KernelLimits.CheckStack("for_each");
            switch (e.Kind)
            {
                case ExprKind.Lit: case ExprKind.MVar: case ExprKind.FVar:
                    return;
                case ExprKind.MData:
                    Apply(e.MDataExpr);
                    return;
                case ExprKind.Proj:
                    Apply(e.ProjExpr);
                    return;
                case ExprKind.App:
                    if (m_partialApps) Apply(e.AppFn);
                    else ApplyFn(e.AppFn);
                    Apply(e.AppArg);
                    return;
                case ExprKind.Lambda: case ExprKind.Pi:
                    Apply(e.BindingDomain);
                    Apply(e.BindingBody);
                    return;
                case ExprKind.Let:
                    Apply(e.LetType);
                    Apply(e.LetValue);
                    Apply(e.LetBody);
                    return;
            }
        }
    }

    sealed class OffsetVisitor
    {
        readonly HashSet<ObjOffset> m_cache = new();
        readonly Func<Expr, uint, bool> m_f;

        public OffsetVisitor(Func<Expr, uint, bool> f) { m_f = f; }

        bool Visited(Expr e, uint offset)
        {
            if (RC.IsLikelyUnshared(e.Raw)) return false;
            return !m_cache.Add(new ObjOffset(e.Raw, offset));
        }

        public void Apply(Expr e, uint offset)
        {
            switch (e.Kind)
            {
                case ExprKind.Const: case ExprKind.BVar: case ExprKind.Sort:
                    m_f(e, offset);
                    return;
            }
            if (Visited(e, offset)) return;
            if (!m_f(e, offset)) return;
            KernelLimits.CheckStack("for_each");
            switch (e.Kind)
            {
                case ExprKind.Lit: case ExprKind.MVar: case ExprKind.FVar:
                    return;
                case ExprKind.MData:
                    Apply(e.MDataExpr, offset);
                    return;
                case ExprKind.Proj:
                    Apply(e.ProjExpr, offset);
                    return;
                case ExprKind.App:
                    Apply(e.AppFn, offset);
                    Apply(e.AppArg, offset);
                    return;
                case ExprKind.Lambda: case ExprKind.Pi:
                    Apply(e.BindingDomain, offset);
                    Apply(e.BindingBody, offset + 1);
                    return;
                case ExprKind.Let:
                    Apply(e.LetType, offset);
                    Apply(e.LetValue, offset);
                    Apply(e.LetBody, offset + 1);
                    return;
            }
        }
    }

    /// <summary>`for_each(e, f)` (visits partial applications).</summary>
    public static void ForEach(Expr e, Func<Expr, bool> f) => new Visitor(f, true).Apply(e);

    /// <summary>`for_each_fn&lt;false&gt;` (does not visit partial applications).</summary>
    public static void ForEachNoPartialApps(Expr e, Func<Expr, bool> f) => new Visitor(f, false).Apply(e);

    /// <summary>`for_each(e, f)` where `f` takes the binder offset.</summary>
    public static void ForEachOffset(Expr e, Func<Expr, uint, bool> f) => new OffsetVisitor(f).Apply(e, 0);

    /// <summary>`find(e, p)`: return a subexpression satisfying `p`, or `Expr.None`.</summary>
    public static Expr Find(Expr e, Func<Expr, uint, bool> p)
    {
        Expr result = Expr.None;
        ForEachOffset(e, (x, offset) =>
        {
            if (result.IsSome) return false;
            if (p(x, offset)) { result = x; return false; }
            return true;
        });
        return result;
    }
}

/// <summary>Port of `expr_eq_fn&lt;CompareBinderInfo&gt;`.</summary>
internal sealed class ExprEqFn
{
    readonly bool m_compareBinderInfo;
    HashSet<ObjPair> m_cache;
    ulong m_counter;

    ExprEqFn(bool compareBinderInfo) { m_compareBinderInfo = compareBinderInfo; }

    bool CheckCache(Expr a, Expr b)
    {
        if (!RC.IsShared(a.Raw) || !RC.IsShared(b.Raw)) return false;
        m_cache ??= new HashSet<ObjPair>();
        return !m_cache.Add(new ObjPair(a.Raw, b.Raw));
    }

    static bool LiteralEq(Obj a, Obj b)
    {
        uint ka = lean_obj_tag(a), kb = lean_obj_tag(b);
        if (ka != kb) return false;
        if (ka == 1) return Name.StringEq(lean_ctor_get(a, 0), lean_ctor_get(b, 0));
        return Nat.Eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0));
    }

    /// <summary>`kvmap` equality (`list_ref&lt;pair_ref&lt;name, data_value&gt;&gt;::operator==`).</summary>
    public static bool KVMapEq(Obj l1, Obj l2)
    {
        while (!lean_is_scalar(l1) && !lean_is_scalar(l2))
        {
            if (ReferenceEquals(l1, l2)) return true;
            Obj p1 = lean_ctor_get(l1, 0), p2 = lean_ctor_get(l2, 0);
            if (!ReferenceEquals(p1, p2))
            {
                if (!Name.Eq(lean_ctor_get(p1, 0), lean_ctor_get(p2, 0))) return false;
                Obj v1 = lean_ctor_get(p1, 1), v2 = lean_ctor_get(p2, 1);
                if (!ReferenceEquals(v1, v2) && KX.DataValueBeq(RC.Own(v1), RC.Own(v2)) == 0) return false;
            }
            l1 = lean_ctor_get(l1, 1);
            l2 = lean_ctor_get(l2, 1);
        }
        return lean_is_scalar(l1) && lean_is_scalar(l2);
    }

    public static bool LevelsEq(Obj l1, Obj l2)
    {
        while (!lean_is_scalar(l1) && !lean_is_scalar(l2))
        {
            if (!Level.Eq(new Level(lean_ctor_get(l1, 0)), new Level(lean_ctor_get(l2, 0)))) return false;
            l1 = lean_ctor_get(l1, 1);
            l2 = lean_ctor_get(l2, 1);
        }
        return lean_is_scalar(l1) && lean_is_scalar(l2);
    }

    bool Apply(Expr a, Expr b, bool root = false)
    {
        if (Expr.IsEqp(a, b)) return true;
        if (a.Hash != b.Hash) return false;
        if (a.Kind != b.Kind) return false;
        switch (a.Kind)
        {
            case ExprKind.BVar: return Nat.Eq(a.BVarIdx, b.BVarIdx);
            case ExprKind.Lit: return LiteralEq(a.LitValue, b.LitValue);
            case ExprKind.MVar: return a.MVarName == b.MVarName;
            case ExprKind.FVar: return a.FVarName == b.FVarName;
            case ExprKind.Sort: return a.SortLevel == b.SortLevel;
        }
        if (!root && CheckCache(a, b)) return true;
        m_counter++;
        KernelLimits.CheckStack("expr_eq");
        switch (a.Kind)
        {
            case ExprKind.MData:
                return Apply(a.MDataExpr, b.MDataExpr) && KVMapEq(a.MDataData, b.MDataData);
            case ExprKind.Proj:
                return Apply(a.ProjExpr, b.ProjExpr) && a.ProjSName == b.ProjSName && Nat.Eq(a.ProjIdx, b.ProjIdx);
            case ExprKind.Const:
                return a.ConstName == b.ConstName && LevelsEq(a.ConstLevels, b.ConstLevels);
            case ExprKind.App:
            {
                if (!Apply(a.AppArg, b.AppArg)) return false;
                Expr currA = a.AppFn, currB = b.AppFn;
                while (true)
                {
                    if (!currA.IsApp) break;
                    if (!currB.IsApp) return false;
                    if (!Apply(currA.AppArg, currB.AppArg)) return false;
                    currA = currA.AppFn;
                    currB = currB.AppFn;
                }
                return Apply(currA, currB);
            }
            case ExprKind.Lambda: case ExprKind.Pi:
                return Apply(a.BindingDomain, b.BindingDomain) &&
                       Apply(a.BindingBody, b.BindingBody) &&
                       (!m_compareBinderInfo || a.BindingName == b.BindingName) &&
                       (!m_compareBinderInfo || a.BindingInfo == b.BindingInfo);
            case ExprKind.Let:
                return Apply(a.LetType, b.LetType) &&
                       Apply(a.LetValue, b.LetValue) &&
                       Apply(a.LetBody, b.LetBody) &&
                       a.LetNonDep == b.LetNonDep &&
                       (!m_compareBinderInfo || a.LetName == b.LetName);
        }
        throw lean_internal_panic_unreachable();
    }

    bool Run(Expr a, Expr b)
    {
        try { return Apply(a, b, true); }
        finally { if (m_counter > 0) KernelLimits.AddHeartbeats(m_counter); }
    }

    [ThreadStatic] static ExprEqFn t_fn, t_fnStrict;

    static bool RunCached(Expr a, Expr b, bool strict)
    {
        // fast paths identical to the first steps of `Apply`
        if (ReferenceEquals(a.Raw, b.Raw)) return true;
        if (a.Hash != b.Hash) return false;
        if (a.Kind != b.Kind) return false;
        ExprEqFn fn = strict ? t_fnStrict : t_fn;
        if (fn == null) fn = new ExprEqFn(strict);
        else if (strict) t_fnStrict = null; else t_fn = null; // take ownership (re-entrancy safe)
        try
        {
            fn.m_counter = 0;
            return fn.Run(a, b);
        }
        finally
        {
            if (fn.m_cache != null)
            {
                if (fn.m_cache.Count > 4096) fn.m_cache = null; // do not retain large caches
                else fn.m_cache.Clear();
            }
            if (strict) t_fnStrict = fn; else t_fn = fn;
        }
    }

    /// <summary>`is_equal` / `operator==`: structural equality ignoring binder names and binder info.</summary>
    public static bool IsEqual(Expr a, Expr b) => RunCached(a, b, false);

    /// <summary>Structural equality also comparing binder names and binder information.</summary>
    public static bool IsEqualStrict(Expr a, Expr b) => RunCached(a, b, true);
}
