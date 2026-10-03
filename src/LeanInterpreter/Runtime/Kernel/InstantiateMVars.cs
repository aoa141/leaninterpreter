// Port of library/instantiate_mvars.cpp and library/scope_cache.h: `instantiateMVars` with
// linear complexity in the presence of nested delayed-assigned metavariables.
// See the C++ source for the description of the two passes.

using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

/// <summary>Holder of an owned `MetavarContext` object, threaded linearly as in C++.</summary>
internal sealed class MCtx
{
    public Obj Raw;
    public MCtx(Obj owned) { Raw = owned; }

    public void AssignLMVar(Name mid, Level l) => Raw = KX.AssignLMVar(Raw, RC.Own(mid.Raw), RC.Own(l.Raw));
    public void AssignMVar(Name mid, Expr e) => Raw = KX.AssignMVar(Raw, RC.Own(mid.Raw), RC.Own(e.Raw));

    // The `Option` results below are never released; they keep the values alive.
    public Level GetLMVarAssignment(Name mid) => new Level(KList.OptionVal(KX.GetLMVarAssignment(RC.Own(Raw), RC.Own(mid.Raw))));
    public Expr GetMVarAssignment(Name mid) => new Expr(KList.OptionVal(KX.GetMVarAssignment(RC.Own(Raw), RC.Own(mid.Raw))));
    /// <summary>Returns the `DelayedMetavarAssignment` object or null.</summary>
    public Obj GetDelayedMVarAssignment(Name mid) => KList.OptionVal(KX.GetDelayedMVarAssignment(RC.Own(Raw), RC.Own(mid.Raw)));

    public static Obj DelayedAssignmentFVars(Obj d) => KX.DelayedMVarAssignmentFVars(RC.Own(d));
    public static Name DelayedAssignmentMVarIdPending(Obj d) => new Name(KX.DelayedMVarAssignmentMVarIdPending(RC.Own(d)));
}

/// <summary>Level metavariable instantiation (`instantiate_lmvars_all_fn`).</summary>
internal sealed class InstantiateLMVarsAllFn
{
    readonly MCtx m_mctx;
    readonly Dictionary<Obj, Level> m_cache = new(ReferenceEqualityComparer.Instance);

    public InstantiateLMVarsAllFn(MCtx mctx) { m_mctx = mctx; }

    Level Cache(Level l, Level r, bool shared)
    {
        if (shared) m_cache.TryAdd(l.Raw, r);
        return r;
    }

    public Level Visit(Level l)
    {
        if (!l.HasMVar) return l;
        bool shared = false;
        if (RC.IsShared(l.Raw))
        {
            if (m_cache.TryGetValue(l.Raw, out var c)) return c;
            shared = true;
        }
        switch (l.Kind)
        {
            case LevelKind.Succ:
                return Cache(l, Level.UpdateSucc(l, Visit(l.SuccOf)), shared);
            case LevelKind.Max: case LevelKind.IMax:
            {
                Level lhs = Visit(l.Lhs);
                Level rhs = Visit(l.Rhs);
                return Cache(l, Level.UpdateMax(l, lhs, rhs), shared);
            }
            case LevelKind.MVar:
            {
                Level a = m_mctx.GetLMVarAssignment(l.Id);
                if (a.IsNull) return l;
                if (!a.HasMVar) return a;
                Level aNew = Visit(a);
                if (!Level.IsEqp(a, aNew))
                    m_mctx.AssignLMVar(l.Id, aNew);
                return aNew;
            }
        }
        throw lean_internal_panic_unreachable();
    }
}

/// <summary>Pass 1: instantiate updateable direct metavariables with write-back.</summary>
internal sealed class InstantiateDirectFn
{
    readonly MCtx m_mctx;
    readonly InstantiateLMVarsAllFn m_levelFn;
    readonly HashSet<Name> m_alreadyNormalized = new();
    bool m_hasUpdateableDelayed;
    readonly Dictionary<Obj, Expr> m_cache = new(ReferenceEqualityComparer.Instance);

    public InstantiateDirectFn(MCtx mctx)
    {
        m_mctx = mctx;
        m_levelFn = new InstantiateLMVarsAllFn(mctx);
    }

    public bool HasUpdateableDelayed => m_hasUpdateableDelayed;

    Level VisitLevel(Level l) => m_levelFn.Visit(l);
    Obj VisitLevels(Obj ls) => Inst.MapReuseLevels(ls, VisitLevel);

    Expr Cache(Expr e, Expr r, bool shared)
    {
        if (shared) m_cache.TryAdd(e.Raw, r);
        return r;
    }

    Expr GetAssignment(Name mid)
    {
        Expr a = m_mctx.GetMVarAssignment(mid);
        if (a.IsNull) return Expr.None;
        if (!a.HasMVar || m_alreadyNormalized.Contains(mid)) return a;
        m_alreadyNormalized.Add(mid);
        Expr aNew = Visit(a);
        if (!Expr.IsEqp(a, aNew))
            m_mctx.AssignMVar(mid, aNew);
        return aNew;
    }

    Expr VisitNonMVarApp(Expr e)
    {
        Expr newA = Visit(e.AppArg);
        Expr fn = e.AppFn;
        Expr newF = fn.IsApp ? VisitNonMVarApp(fn) : Visit(fn);
        return Expr.UpdateApp(e, newF, newA);
    }

    Expr VisitAppBeta(Expr fNew, Expr e)
    {
        var args = new List<Expr>();
        Expr curr = e;
        while (curr.IsApp)
        {
            args.Add(Visit(curr.AppArg));
            curr = curr.AppFn;
        }
        return Inst.ApplyBeta(fNew, (uint)args.Count, args, false, true);
    }

    Expr VisitApp(Expr e)
    {
        Expr f = Expr.GetAppFn(e);
        if (!f.IsMVar) return VisitNonMVarApp(e);
        Name mid = f.MVarName;
        Expr fNew = GetAssignment(mid);
        if (fNew.IsSome) return VisitAppBeta(fNew, e);
        Obj d = m_mctx.GetDelayedMVarAssignment(mid);
        if (d != null)
        {
            Name midPending = MCtx.DelayedAssignmentMVarIdPending(d);
            if (GetAssignment(midPending).IsSome)
                m_hasUpdateableDelayed = true;
        }
        return VisitNonMVarApp(e);
    }

    Expr VisitMVar(Expr e)
    {
        Name mid = e.MVarName;
        Expr r = GetAssignment(mid);
        if (r.IsSome) return r;
        Obj d = m_mctx.GetDelayedMVarAssignment(mid);
        if (d != null)
        {
            Name midPending = MCtx.DelayedAssignmentMVarIdPending(d);
            if (GetAssignment(midPending).IsSome)
                m_hasUpdateableDelayed = true;
        }
        return e;
    }

    public Expr Visit(Expr e)
    {
        if (!e.HasMVar) return e;
        bool shared = false;
        if (RC.IsShared(e.Raw))
        {
            if (m_cache.TryGetValue(e.Raw, out var c)) return c;
            shared = true;
        }
        KernelLimits.CheckStack("instantiate_mvars");
        switch (e.Kind)
        {
            case ExprKind.Sort:
                return Cache(e, Expr.UpdateSort(e, VisitLevel(e.SortLevel)), shared);
            case ExprKind.Const:
                return Cache(e, Expr.UpdateConst(e, VisitLevels(e.ConstLevels)), shared);
            case ExprKind.MVar:
                return VisitMVar(e);
            case ExprKind.MData:
                return Cache(e, Expr.UpdateMData(e, Visit(e.MDataExpr)), shared);
            case ExprKind.Proj:
                return Cache(e, Expr.UpdateProj(e, Visit(e.ProjExpr)), shared);
            case ExprKind.App:
                return Cache(e, VisitApp(e), shared);
            case ExprKind.Pi: case ExprKind.Lambda:
            {
                Expr d = Visit(e.BindingDomain);
                Expr b = Visit(e.BindingBody);
                return Cache(e, Expr.UpdateBinding(e, d, b), shared);
            }
            case ExprKind.Let:
            {
                Expr t = Visit(e.LetType);
                Expr v = Visit(e.LetValue);
                Expr b = Visit(e.LetBody);
                return Cache(e, Expr.UpdateLet(e, t, v, b), shared);
            }
        }
        throw lean_internal_panic_unreachable();
    }
}

/// <summary>Lifting of fvar-substitution values with pass-lifetime caching and origin tracking (`lift_fn`).</summary>
internal sealed class LiftFn
{
    readonly struct Key : IEquatable<Key>
    {
        public readonly Obj Ptr; public readonly uint Cutoff, Amount;
        public Key(Obj p, uint c, uint a) { Ptr = p; Cutoff = c; Amount = a; }
        public bool Equals(Key o) => ReferenceEquals(Ptr, o.Ptr) && Cutoff == o.Cutoff && Amount == o.Amount;
        public override bool Equals(object obj) => obj is Key k && Equals(k);
        public override int GetHashCode() => HashCode.Combine(System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(Ptr), Cutoff, Amount);
    }

    readonly Dictionary<Key, Expr> m_cache = new();
    readonly Dictionary<Obj, (Expr, uint)> m_origin = new(ReferenceEqualityComparer.Instance);

    Expr Apply(Expr e, uint cutoff, uint amount)
    {
        if (cutoff >= e.LooseBVarRange) return e;
        if (e.IsBVar) return Expr.MkBVar(Nat.Add(e.BVarIdx, amount));

        if (!RC.IsLikelyUnshared(e.Raw))
        {
            if (m_origin.TryGetValue(e.Raw, out var org) && cutoff <= org.Item2)
                return Apply(org.Item1, 0, org.Item2 + amount);
        }

        var k = new Key(e.Raw, cutoff, amount);
        bool cacheIt = cutoff == 0 || !RC.IsLikelyUnshared(e.Raw);
        if (cacheIt && m_cache.TryGetValue(k, out var c)) return c;

        KernelLimits.CheckStack("instantiate_mvars");
        Expr r;
        switch (e.Kind)
        {
            case ExprKind.MData:
                r = Expr.UpdateMData(e, Apply(e.MDataExpr, cutoff, amount));
                break;
            case ExprKind.Proj:
                r = Expr.UpdateProj(e, Apply(e.ProjExpr, cutoff, amount));
                break;
            case ExprKind.App:
            {
                Expr f = Apply(e.AppFn, cutoff, amount);
                Expr a = Apply(e.AppArg, cutoff, amount);
                r = Expr.UpdateApp(e, f, a);
                break;
            }
            case ExprKind.Pi: case ExprKind.Lambda:
            {
                Expr d = Apply(e.BindingDomain, cutoff, amount);
                Expr b = Apply(e.BindingBody, cutoff + 1, amount);
                r = Expr.UpdateBinding(e, d, b);
                break;
            }
            case ExprKind.Let:
            {
                Expr t = Apply(e.LetType, cutoff, amount);
                Expr v = Apply(e.LetValue, cutoff, amount);
                Expr b = Apply(e.LetBody, cutoff + 1, amount);
                r = Expr.UpdateLet(e, t, v, b);
                break;
            }
            default:
                throw lean_internal_panic_unreachable();
        }
        if (cacheIt) m_cache.TryAdd(k, r);
        if (cutoff == 0) m_origin.TryAdd(r.Raw, (e, amount));
        return r;
    }

    public Expr Lift(Expr e, uint amount)
    {
        if (amount == 0) return e;
        return Apply(e, 0, amount);
    }
}

/// <summary>Port of `scope_cache` (library/scope_cache.h).</summary>
internal sealed class ScopeCache<TKey, TValue>
{
    sealed class GenNode
    {
        public uint Gen;
        public GenNode Tail;
    }

    sealed class Entry
    {
        public TValue Result;
        public uint ScopeLevel;
        public GenNode ScopeGens;
        public uint ResultScope;
    }

    readonly Dictionary<TKey, List<Entry>> m_cache;
    GenNode m_scopeGensList;
    uint m_genCounter;
    uint m_scope;

    public ScopeCache(IEqualityComparer<TKey> comparer)
    {
        m_cache = new Dictionary<TKey, List<Entry>>(comparer);
        m_scopeGensList = new GenNode { Gen = 0, Tail = null };
    }

    public uint Scope => m_scope;

    public void Push()
    {
        m_scope++;
        m_genCounter++;
        m_scopeGensList = new GenNode { Gen = m_genCounter, Tail = m_scopeGensList };
    }

    public void Pop()
    {
        m_scope--;
        m_scopeGensList = m_scopeGensList.Tail;
    }

    void Rewind(List<Entry> stack)
    {
        while (stack.Count > 0)
        {
            Entry top = stack[stack.Count - 1];
            if (top.ResultScope > m_scope)
            {
                stack.RemoveAt(stack.Count - 1);
                continue;
            }
            while (top.ScopeLevel > m_scope)
            {
                top.ScopeGens = top.ScopeGens.Tail;
                top.ScopeLevel--;
            }
            GenNode currentNode = m_scopeGensList;
            for (uint i = m_scope; i > top.ScopeLevel; i--)
                currentNode = currentNode.Tail;
            if (top.ScopeGens.Gen == currentNode.Gen) return;
            GenNode entryNode = top.ScopeGens;
            uint level = top.ScopeLevel;
            bool found = false;
            while (level > top.ResultScope)
            {
                entryNode = entryNode.Tail;
                currentNode = currentNode.Tail;
                level--;
                if (entryNode.Gen == currentNode.Gen)
                {
                    top.ScopeLevel = level;
                    top.ScopeGens = entryNode;
                    found = true;
                    break;
                }
            }
            if (found) return;
            stack.RemoveAt(stack.Count - 1);
        }
    }

    public bool Lookup(TKey key, ref uint resultScope, out TValue value)
    {
        value = default;
        if (!m_cache.TryGetValue(key, out var stack)) return false;
        Rewind(stack);
        if (stack.Count == 0) return false;
        Entry top = stack[stack.Count - 1];
        if (top.ScopeLevel != m_scope) return false;
        resultScope = Math.Max(resultScope, top.ResultScope);
        value = top.Result;
        return true;
    }

    public TValue Insert(TKey key, TValue result, uint resultScope)
    {
        if (!m_cache.TryGetValue(key, out var stack))
        {
            stack = new List<Entry>();
            m_cache[key] = stack;
        }
        Rewind(stack);
        TValue shared = result;
        if (stack.Count > 0 && stack[stack.Count - 1].ResultScope == resultScope)
            shared = stack[stack.Count - 1].Result;
        while (stack.Count > 0 && stack[stack.Count - 1].ScopeLevel >= resultScope)
            stack.RemoveAt(stack.Count - 1);
        stack.Add(new Entry { Result = shared, ScopeLevel = m_scope, ScopeGens = m_scopeGensList, ResultScope = resultScope });
        return shared;
    }
}

/// <summary>Pass 2: resolve delayed-assigned metavariables with fused fvar substitution.</summary>
internal sealed class InstantiateDelayedFn
{
    struct FVarSubstEntry
    {
        public uint Depth;
        public uint Scope;
        public Expr Value;
    }

    readonly MCtx m_mctx;
    readonly Dictionary<Name, FVarSubstEntry> m_fvarSubst = new();
    uint m_depth;
    readonly ScopeCache<ObjOffset, Expr> m_cache = new(EqualityComparer<ObjOffset>.Default);
    readonly LiftFn m_lift = new();
    uint m_resultScope;
    readonly HashSet<Name> m_alreadyNormalized = new();
    readonly Dictionary<Obj, bool> m_resolvableExprCache = new(ReferenceEqualityComparer.Instance);
    /// <summary>0 = in-progress, 1 = yes, 2 = no.</summary>
    readonly Dictionary<Name, uint> m_resolvablePendingCache = new();

    public InstantiateDelayedFn(MCtx mctx) { m_mctx = mctx; }

    bool IsResolvablePending(Name pending)
    {
        if (m_resolvablePendingCache.TryGetValue(pending, out uint st)) return st == 1;
        m_resolvablePendingCache[pending] = 0;
        Expr r = m_mctx.GetMVarAssignment(pending);
        if (r.IsNull)
        {
            m_resolvablePendingCache[pending] = 2;
            return false;
        }
        bool ok = IsResolvableExpr(r);
        m_resolvablePendingCache[pending] = ok ? 1u : 2u;
        return ok;
    }

    bool IsResolvableExpr(Expr e)
    {
        if (!e.HasExprMVar) return true;
        if (RC.IsShared(e.Raw) && m_resolvableExprCache.TryGetValue(e.Raw, out bool c)) return c;
        bool r = IsResolvableExprCore(e);
        if (RC.IsShared(e.Raw)) m_resolvableExprCache[e.Raw] = r;
        return r;
    }

    bool IsResolvableExprCore(Expr e)
    {
        KernelLimits.CheckStack("instantiate_mvars");
        switch (e.Kind)
        {
            case ExprKind.MVar:
                return false;
            case ExprKind.App:
            {
                Expr f = Expr.GetAppFn(e);
                if (f.IsMVar)
                {
                    Name mid = f.MVarName;
                    Obj d = m_mctx.GetDelayedMVarAssignment(mid);
                    if (d == null) return false;
                    Obj fvars = MCtx.DelayedAssignmentFVars(d);
                    if (lean_array_size(fvars) > Expr.GetAppNumArgs(e)) return false;
                    Name midPending = MCtx.DelayedAssignmentMVarIdPending(d);
                    if (!IsResolvablePending(midPending)) return false;
                    Expr curr = e;
                    while (curr.IsApp)
                    {
                        if (!IsResolvableExpr(curr.AppArg)) return false;
                        curr = curr.AppFn;
                    }
                    return true;
                }
                return IsResolvableExpr(e.AppFn) && IsResolvableExpr(e.AppArg);
            }
            case ExprKind.Lambda: case ExprKind.Pi:
                return IsResolvableExpr(e.BindingDomain) && IsResolvableExpr(e.BindingBody);
            case ExprKind.Let:
                return IsResolvableExpr(e.LetType) && IsResolvableExpr(e.LetValue) && IsResolvableExpr(e.LetBody);
            case ExprKind.MData:
                return IsResolvableExpr(e.MDataExpr);
            case ExprKind.Proj:
                return IsResolvableExpr(e.ProjExpr);
            default:
                return true;
        }
    }

    bool InOuterMode => m_fvarSubst.Count == 0;

    Expr LookupFVar(Name fid)
    {
        if (!m_fvarSubst.TryGetValue(fid, out var entry)) return Expr.None;
        m_resultScope = Math.Max(m_resultScope, entry.Scope);
        uint d = m_depth - entry.Depth;
        if (d == 0) return entry.Value;
        return m_lift.Lift(entry.Value, d);
    }

    Expr GetAssignment(Name mid)
    {
        Expr a = m_mctx.GetMVarAssignment(mid);
        if (a.IsNull) return Expr.None;
        if (InOuterMode)
        {
            if (m_alreadyNormalized.Contains(mid)) return a;
            m_alreadyNormalized.Add(mid);
            Expr aNew = Visit(a);
            if (!Expr.IsEqp(a, aNew))
                m_mctx.AssignMVar(mid, aNew);
            return aNew;
        }
        return Visit(a);
    }

    Expr VisitDelayed(Obj fvars, Name midPending, Expr e)
    {
        var args = new List<Expr>();
        Expr curr = e;
        while (curr.IsApp)
        {
            args.Add(Visit(curr.AppArg));
            curr = curr.AppFn;
        }

        int fvarCount = (int)lean_array_size(fvars);
        int extraCount = args.Count - fvarCount;

        m_cache.Push();
        var savedEntries = new List<(Name key, bool hadOld, FVarSubstEntry old)>(fvarCount);
        for (int i = 0; i < fvarCount; i++)
        {
            Name fid = new Expr(lean_array_get_core(fvars, (ulong)i)).FVarName;
            if (m_fvarSubst.TryGetValue(fid, out var old)) savedEntries.Add((fid, true, old));
            else savedEntries.Add((fid, false, default));
            m_fvarSubst[fid] = new FVarSubstEntry { Depth = m_depth, Scope = m_cache.Scope, Value = args[args.Count - 1 - i] };
        }

        Expr pendingVal = m_mctx.GetMVarAssignment(midPending);
        Expr valNew = Visit(pendingVal);

        m_cache.Pop();
        m_resultScope = Math.Min(m_resultScope, m_cache.Scope);

        foreach (var se in savedEntries)
        {
            if (!se.hadOld) m_fvarSubst.Remove(se.key);
            else m_fvarSubst[se.key] = se.old;
        }

        return Inst.ApplyBeta(valNew, (uint)extraCount, args, false, true);
    }

    Expr VisitNonMVarApp(Expr e)
    {
        Expr newA = Visit(e.AppArg);
        Expr fn = e.AppFn;
        Expr newF = fn.IsApp ? VisitNonMVarApp(fn) : Visit(fn);
        return Expr.UpdateApp(e, newF, newA);
    }

    Expr VisitApp(Expr e)
    {
        Expr f = Expr.GetAppFn(e);
        if (!f.IsMVar) return VisitNonMVarApp(e);
        Name mid = f.MVarName;
        Obj d = m_mctx.GetDelayedMVarAssignment(mid);
        if (d == null) return VisitNonMVarApp(e);
        Obj fvars = MCtx.DelayedAssignmentFVars(d);
        Name midPending = MCtx.DelayedAssignmentMVarIdPending(d);
        if (lean_array_size(fvars) > Expr.GetAppNumArgs(e)) return VisitNonMVarApp(e);
        if (IsResolvablePending(midPending))
            return VisitDelayed(fvars, midPending, e);
        GetAssignment(midPending);
        return VisitNonMVarApp(e);
    }

    Expr VisitFVar(Expr e)
    {
        Expr r = LookupFVar(e.FVarName);
        if (r.IsSome) return r;
        return e;
    }

    public Expr Visit(Expr e)
    {
        if ((!e.HasFVar || InOuterMode) && !e.HasExprMVar) return e;

        bool shared = false;
        if (RC.IsShared(e.Raw))
        {
            if (m_cache.Lookup(new ObjOffset(e.Raw, m_depth), ref m_resultScope, out var c)) return c;
            shared = true;
        }

        uint savedResultScope = m_resultScope;
        m_resultScope = 0;

        KernelLimits.CheckStack("instantiate_mvars");
        Expr r;
        switch (e.Kind)
        {
            case ExprKind.FVar:
                r = VisitFVar(e);
                goto done;
            case ExprKind.MVar:
                r = e;
                goto done;
            case ExprKind.MData:
                r = Expr.UpdateMData(e, Visit(e.MDataExpr));
                break;
            case ExprKind.Proj:
                r = Expr.UpdateProj(e, Visit(e.ProjExpr));
                break;
            case ExprKind.App:
                r = VisitApp(e);
                break;
            case ExprKind.Pi: case ExprKind.Lambda:
            {
                Expr d = Visit(e.BindingDomain);
                m_depth++;
                Expr b = Visit(e.BindingBody);
                m_depth--;
                r = Expr.UpdateBinding(e, d, b);
                break;
            }
            case ExprKind.Let:
            {
                Expr t = Visit(e.LetType);
                Expr v = Visit(e.LetValue);
                m_depth++;
                Expr b = Visit(e.LetBody);
                m_depth--;
                r = Expr.UpdateLet(e, t, v, b);
                break;
            }
            default:
                throw lean_internal_panic_unreachable();
        }
        if (shared)
            r = m_cache.Insert(new ObjOffset(e.Raw, m_depth), r, m_resultScope);

    done:
        m_resultScope = Math.Max(savedResultScope, m_resultScope);
        return r;
    }
}

internal static class InstantiateMVars
{
    /// <summary>`run_instantiate_all`: `m` and `e` are owned; returns the owned pair `(mctx, e')`.</summary>
    public static Obj RunInstantiateAll(Obj m, Obj e)
    {
        var mctx = new MCtx(m);
        var pass1 = new InstantiateDirectFn(mctx);
        Expr e1 = pass1.Visit(new Expr(e));
        Expr e2;
        if (!pass1.HasUpdateableDelayed)
        {
            e2 = e1;
        }
        else
        {
            var pass2 = new InstantiateDelayedFn(mctx);
            e2 = pass2.Visit(e1);
        }
        Obj er = e2.Raw;
        if (!ReferenceEquals(er, e))
        {
            lean_inc(er);
            lean_dec(e);
        }
        Obj r = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(r, 0, mctx.Raw);
        lean_ctor_set(r, 1, er);
        return r;
    }

    /// <summary>`lean_instantiate_level_mvars`: `m` and `l` are owned.</summary>
    public static Obj RunInstantiateLevel(Obj m, Obj l)
    {
        var mctx = new MCtx(m);
        Level lNew = new InstantiateLMVarsAllFn(mctx).Visit(new Level(l));
        Obj lr = lNew.Raw;
        if (!ReferenceEquals(lr, l))
        {
            lean_inc(lr);
            lean_dec(l);
        }
        Obj r = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(r, 0, mctx.Raw);
        lean_ctor_set(r, 1, lr);
        return r;
    }
}
