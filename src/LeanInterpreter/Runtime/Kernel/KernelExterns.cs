// The kernel externs called by the generated code (docs/externs-kernel.txt), and the port of
// library/expr_lt.cpp.

using LeanInterpreter.Kernel;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel
{
    /// <summary>Port of library/expr_lt.cpp: total order on expressions.</summary>
    internal static class ExprLt
    {
        static bool LiteralLt(Obj a, Obj b)
        {
            uint ka = lean_obj_tag(a), kb = lean_obj_tag(b);
            if (ka != kb) return ka < kb;
            if (ka == 1) return Name.StringLt(lean_ctor_get(a, 0), lean_ctor_get(b, 0));
            return Nat.Lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0));
        }

        static bool DataValueEq(Obj a, Obj b) =>
            ReferenceEquals(a, b) || KX.DataValueBeq(RC.Own(a), RC.Own(b)) != 0;

        /// <summary>`data_value::operator&lt;` (DataValue: ofString | ofBool | ofName | ofNat | ofInt | ofSyntax).</summary>
        static bool DataValueLt(Obj a, Obj b)
        {
            uint ka = lean_obj_tag(a), kb = lean_obj_tag(b);
            if (ka != kb) return ka < kb;
            switch (ka)
            {
                case 0: return Name.StringLt(lean_ctor_get(a, 0), lean_ctor_get(b, 0));
                case 3: return Nat.Lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0));
                case 1: return lean_ctor_get_uint8_s(a, 0) == 0 && lean_ctor_get_uint8_s(b, 0) != 0;
                case 2: return new Name(lean_ctor_get(a, 0)) < new Name(lean_ctor_get(b, 0));
            }
            return false;
        }

        /// <summary>`kvmap` lexicographic order.</summary>
        static bool KVMapLt(Obj l1, Obj l2)
        {
            while (!lean_is_scalar(l1) && !lean_is_scalar(l2))
            {
                if (ReferenceEquals(l1, l2)) return false;
                Obj h1 = lean_ctor_get(l1, 0), h2 = lean_ctor_get(l2, 0);
                if (PairLt(h1, h2)) return true;
                if (PairLt(h2, h1)) return false;
                l1 = lean_ctor_get(l1, 1);
                l2 = lean_ctor_get(l2, 1);
            }
            return lean_is_scalar(l1) && !lean_is_scalar(l2);
        }

        static bool PairLt(Obj a, Obj b)
        {
            Name a1 = new Name(lean_ctor_get(a, 0)), b1 = new Name(lean_ctor_get(b, 0));
            if (a1 != b1) return a1 < b1;
            return DataValueLt(lean_ctor_get(a, 1), lean_ctor_get(b, 1));
        }

        public static bool IsLt(Expr a, Expr b, bool useHash, LocalCtx lctx = null)
        {
            if (Expr.IsEqp(a, b)) return false;
            if (a.Kind != b.Kind) return a.Kind < b.Kind;
            if (useHash)
            {
                if (a.Hash < b.Hash) return true;
                if (a.Hash > b.Hash) return false;
            }
            if (a == b) return false;
            KernelLimits.CheckStack("expr_lt");
            switch (a.Kind)
            {
                case ExprKind.Lit:
                    return LiteralLt(a.LitValue, b.LitValue);
                case ExprKind.BVar:
                    return Nat.Lt(a.BVarIdx, b.BVarIdx);
                case ExprKind.MData:
                    if (a.MDataExpr != b.MDataExpr) return IsLt(a.MDataExpr, b.MDataExpr, useHash, lctx);
                    return KVMapLt(a.MDataData, b.MDataData);
                case ExprKind.Proj:
                    if (a.ProjExpr != b.ProjExpr) return IsLt(a.ProjExpr, b.ProjExpr, useHash, lctx);
                    if (a.ProjSName != b.ProjSName) return a.ProjSName < b.ProjSName;
                    return Nat.Lt(a.ProjIdx, b.ProjIdx);
                case ExprKind.Const:
                    if (a.ConstName != b.ConstName) return a.ConstName < b.ConstName;
                    return Level.IsLt(a.ConstLevels, b.ConstLevels, useHash);
                case ExprKind.App:
                    if (a.AppFn != b.AppFn) return IsLt(a.AppFn, b.AppFn, useHash, lctx);
                    return IsLt(a.AppArg, b.AppArg, useHash, lctx);
                case ExprKind.Lambda: case ExprKind.Pi:
                    if (a.BindingDomain != b.BindingDomain) return IsLt(a.BindingDomain, b.BindingDomain, useHash, lctx);
                    return IsLt(a.BindingBody, b.BindingBody, useHash, lctx);
                case ExprKind.Let:
                    if (a.LetNonDep != b.LetNonDep) return !a.LetNonDep && b.LetNonDep;
                    if (a.LetType != b.LetType) return IsLt(a.LetType, b.LetType, useHash, lctx);
                    if (a.LetValue != b.LetValue) return IsLt(a.LetValue, b.LetValue, useHash, lctx);
                    return IsLt(a.LetBody, b.LetBody, useHash, lctx);
                case ExprKind.Sort:
                    return Level.IsLt(a.SortLevel, b.SortLevel, useHash);
                case ExprKind.FVar:
                    if (lctx != null)
                    {
                        LocalDecl d1 = lctx.FindLocalDecl(a);
                        if (!d1.IsNull)
                        {
                            LocalDecl d2 = lctx.FindLocalDecl(b);
                            if (!d2.IsNull) return d1.Idx < d2.Idx;
                        }
                    }
                    return a.FVarName < b.FVarName;
                case ExprKind.MVar:
                    return a.MVarName < b.MVarName;
            }
            throw lean_internal_panic_unreachable();
        }
    }
}

namespace LeanInterpreter.Runtime
{
    public static unsafe partial class LeanRt
    {
        static Obj KernelOwnedResult(Expr r) { lean_inc(r.Raw); return r.Raw; }

        // ------------------------------------------------------------------------------------
        // Expr / Level data

        public static ulong lean_expr_mk_data(ulong hash, Obj bvarRange, uint approxDepth, byte hasFVar, byte hasExprMVar, byte hasLevelMVar, byte hasLevelParam) =>
            Expr.MkData(hash, bvarRange, approxDepth, hasFVar, hasExprMVar, hasLevelMVar, hasLevelParam);

        public static ulong lean_expr_mk_app_data(ulong fData, ulong aData) => Expr.MkAppData(fData, aData);

        /// <summary>`Expr.data` (borrowed argument).</summary>
        public static ulong lean_expr_data(Obj e) => Expr.DataOf(e);

        public static ulong lean_level_mk_data(ulong h, Obj depth, byte hasMVar, byte hasParam)
        {
            if (!lean_is_scalar(depth)) throw lean_internal_panic("universe level depth is too big");
            ulong d = lean_unbox(depth);
            if (d > 16777215) throw lean_internal_panic("universe level depth is too big");
            uint h1 = (uint)h;
            return ((ulong)h1) + (((ulong)hasMVar) << 32) + (((ulong)hasParam) << 33) + (d << 40);
        }

        public static byte lean_level_eq(Obj l1, Obj l2) => Level.Eq(new Level(l1), new Level(l2)) ? (byte)1 : (byte)0;

        // ------------------------------------------------------------------------------------
        // Equality and order

        public static byte lean_expr_eqv(Obj a, Obj b) => ExprEqFn.IsEqual(new Expr(a), new Expr(b)) ? (byte)1 : (byte)0;

        public static byte lean_expr_equal(Obj a, Obj b) => ExprEqFn.IsEqualStrict(new Expr(a), new Expr(b)) ? (byte)1 : (byte)0;

        public static byte lean_expr_quick_lt(Obj a, Obj b) => ExprLt.IsLt(new Expr(a), new Expr(b), true) ? (byte)1 : (byte)0;

        public static byte lean_expr_lt(Obj a, Obj b) => ExprLt.IsLt(new Expr(a), new Expr(b), false) ? (byte)1 : (byte)0;

        // ------------------------------------------------------------------------------------
        // Loose bound variables

        public static byte lean_expr_has_loose_bvar(Obj e, Obj i)
        {
            if (!lean_is_scalar(i)) return 0;
            return Expr.HasLooseBVar(new Expr(e), (uint)lean_unbox(i)) ? (byte)1 : (byte)0;
        }

        public static Obj lean_expr_lower_loose_bvars(Obj e, Obj s, Obj d)
        {
            if (!lean_is_scalar(s) || !lean_is_scalar(d) || lean_unbox(s) < lean_unbox(d))
            {
                lean_inc(e);
                return e;
            }
            return KernelOwnedResult(Expr.LowerLooseBVars(new Expr(e), (uint)lean_unbox(s), (uint)lean_unbox(d)));
        }

        public static Obj lean_expr_lift_loose_bvars(Obj e, Obj s, Obj d)
        {
            if (!lean_is_scalar(s) || !lean_is_scalar(d))
            {
                lean_inc(e);
                return e;
            }
            return KernelOwnedResult(Expr.LiftLooseBVars(new Expr(e), (uint)lean_unbox(s), (uint)lean_unbox(d)));
        }

        // ------------------------------------------------------------------------------------
        // Instantiate / abstract

        public static Obj lean_expr_instantiate1(Obj a0, Obj e0)
        {
            var a = new Expr(a0);
            if (!a.HasLooseBVars)
            {
                lean_inc(a0);
                return a0;
            }
            return KernelOwnedResult(Inst.Instantiate(a, 0, 1, new[] { new Expr(e0) }));
        }

        static Obj InstantiateCore(Obj a0, ulong n, Obj[] subst, ulong off)
        {
            var a = new Expr(a0);
            if (!a.HasLooseBVars || n == 0)
            {
                lean_inc(a0);
                return a0;
            }
            return KernelOwnedResult(Inst.InstantiateCore(a, n, subst, off));
        }

        public static Obj lean_expr_instantiate(Obj a, Obj subst) =>
            InstantiateCore(a, lean_array_size(subst), lean_array_cptr(subst), 0);

        public static Obj lean_expr_instantiate_range(Obj a, Obj begin, Obj end, Obj subst)
        {
            if (!lean_is_scalar(begin) || !lean_is_scalar(end))
                throw lean_internal_panic("invalid range for Expr.instantiateRange");
            ulong sz = lean_array_size(subst);
            ulong b = lean_unbox(begin);
            ulong e = lean_unbox(end);
            if (b > e || e > sz)
                throw lean_internal_panic("invalid range for Expr.instantiateRange");
            return InstantiateCore(a, e - b, lean_array_cptr(subst), b);
        }

        static Obj InstantiateRevCore(Obj a0, ulong n, Obj[] subst, ulong off)
        {
            var a = new Expr(a0);
            if (!a.HasLooseBVars)
            {
                lean_inc(a0);
                return a0;
            }
            return KernelOwnedResult(Inst.InstantiateRevCore(a, n, subst, off));
        }

        public static Obj lean_expr_instantiate_rev(Obj a, Obj subst) =>
            InstantiateRevCore(a, lean_array_size(subst), lean_array_cptr(subst), 0);

        public static Obj lean_expr_instantiate_rev_range(Obj a, Obj begin, Obj end, Obj subst)
        {
            if (!lean_is_scalar(begin) || !lean_is_scalar(end))
                throw lean_internal_panic("invalid range for Expr.instantiateRevRange");
            ulong sz = lean_array_size(subst);
            ulong b = lean_unbox(begin);
            ulong e = lean_unbox(end);
            if (b > e || e > sz)
                throw lean_internal_panic("invalid range for Expr.instantiateRevRange");
            return InstantiateRevCore(a, e - b, lean_array_cptr(subst), b);
        }

        static Obj AbstractCore(Obj e0, ulong n, Obj subst)
        {
            var e = new Expr(e0);
            if (!e.HasFVar && !e.HasMVar)
            {
                lean_inc(e0);
                return e0;
            }
            return KernelOwnedResult(Inst.AbstractCore(e, n, subst));
        }

        public static Obj lean_expr_abstract_range(Obj e, Obj n, Obj subst)
        {
            if (!lean_is_scalar(n))
                return AbstractCore(e, lean_array_size(subst), subst);
            return AbstractCore(e, Math.Min(lean_unbox(n), lean_array_size(subst)), subst);
        }

        public static Obj lean_expr_abstract(Obj e, Obj subst) => AbstractCore(e, lean_array_size(subst), subst);

        // ------------------------------------------------------------------------------------
        // replace / find

        public static Obj lean_replace_expr(Obj f, Obj e) =>
            KernelOwnedResult(new ReplaceClosureFn(f).Apply(new Expr(e)));

        public static Obj lean_find_expr(Obj p, Obj e0)
        {
            Obj found = null;
            ForEachFn.ForEach(new Expr(e0), e =>
            {
                if (found != null) return false;
                lean_inc(p);
                lean_inc(e.Raw);
                if (lean_unbox(lean_apply_1(p, e.Raw)) != 0)
                {
                    found = e.Raw;
                    return false;
                }
                return true;
            });
            if (found != null)
            {
                lean_inc(found);
                return lean_mk_option_some(found);
            }
            return lean_box(0);
        }

        public static Obj lean_find_ext_expr(Obj p, Obj e0)
        {
            Obj found = null;
            ForEachFn.ForEachNoPartialApps(new Expr(e0), e =>
            {
                if (found != null) return false;
                lean_inc(p);
                lean_inc(e.Raw);
                switch (lean_unbox(lean_apply_1(p, e.Raw)))
                {
                    case 0: found = e.Raw; return false; // found
                    case 1: return true;                  // visit
                    case 2: return false;                 // done
                    default: throw lean_internal_panic_unreachable();
                }
            });
            if (found != null)
            {
                lean_inc(found);
                return lean_mk_option_some(found);
            }
            return lean_box(0);
        }

        // ------------------------------------------------------------------------------------
        // Printing

        public static Obj lean_expr_dbg_to_string(Obj e) => lean_mk_string(ExprPrinter.ToString(new Expr(e)));

        // ------------------------------------------------------------------------------------
        // Metavariable instantiation

        public static Obj lean_instantiate_level_mvars(Obj m, Obj l) => InstantiateMVars.RunInstantiateLevel(m, l);

        public static Obj lean_instantiate_expr_mvars(Obj m, Obj e) => InstantiateMVars.RunInstantiateAll(m, e);

        // ------------------------------------------------------------------------------------
        // Adding declarations

        /// <summary>`addDeclCore (env : Environment) (maxHeartbeats maxRecDepth : USize) (decl : @&amp; Declaration) (cancelTk? : @&amp; Option IO.CancelToken)`.</summary>
        public static Obj lean_add_decl(Obj env, ulong maxHeartbeat, ulong maxRecDepth, Obj decl, Obj optCancelTk)
        {
            using var scope = new KernelLimits.Scope(maxHeartbeat, maxRecDepth, true, lean_is_scalar(optCancelTk) ? null : lean_ctor_get(optCancelTk, 0));
            try
            {
                return KernelExceptions.Catch(() => EnvOps.AddDecl(new Kernel.Environment(env), new Declaration(decl), true));
            }
            finally { lean_dec(env); }
        }

        public static Obj lean_add_decl_without_checking(Obj env, Obj decl)
        {
            try
            {
                return KernelExceptions.Catch(() => EnvOps.AddDecl(new Kernel.Environment(env), new Declaration(decl), false));
            }
            finally { lean_dec(env); }
        }

        /// <summary>`elab_environment::add`: `env` is owned and consumed on success.</summary>
        static Obj ElabEnvAdd(Obj env, Obj decl, bool check, ref bool envConsumed)
        {
            Obj k0 = KX.ElabEnvironmentToKernelEnv(RC.Own(env));
            Obj k1 = EnvOps.AddDecl(new Kernel.Environment(k0), new Declaration(decl), check);
            lean_dec(k0);
            envConsumed = true;
            return KX.ElabEnvironmentUpdateBaseAfterKernelAdd(env, k1, RC.Own(decl));
        }

        public static Obj lean_elab_add_decl(Obj env, ulong maxHeartbeat, ulong maxRecDepth, Obj decl, Obj optCancelTk)
        {
            using var scope = new KernelLimits.Scope(maxHeartbeat, maxRecDepth, true, lean_is_scalar(optCancelTk) ? null : lean_ctor_get(optCancelTk, 0));
            bool consumed = false;
            try
            {
                return KernelExceptions.Catch(() => ElabEnvAdd(env, decl, true, ref consumed));
            }
            finally { if (!consumed) lean_dec(env); }
        }

        public static Obj lean_elab_add_decl_without_checking(Obj env, Obj decl)
        {
            bool consumed = false;
            try
            {
                return KernelExceptions.Catch(() => ElabEnvAdd(env, decl, false, ref consumed));
            }
            finally { if (!consumed) lean_dec(env); }
        }

        // ------------------------------------------------------------------------------------
        // Kernel type checker entry points (all arguments owned)

        public static Obj lean_kernel_is_def_eq(Obj env, Obj lctx, Obj a, Obj b)
        {
            Obj kenv = KX.ElabEnvironmentToKernelEnv(RC.Own(env));
            try
            {
                return KernelExceptions.Catch(() =>
                {
                    using var tc = new TypeChecker(new Kernel.Environment(kenv), lctx);
                    return lean_box(tc.IsDefEq(new Expr(a), new Expr(b)) ? 1UL : 0UL);
                });
            }
            finally
            {
                lean_dec(kenv); lean_dec(env); lean_dec(lctx); lean_dec(a); lean_dec(b);
            }
        }

        public static Obj lean_kernel_whnf(Obj env, Obj lctx, Obj a)
        {
            Obj kenv = KX.ElabEnvironmentToKernelEnv(RC.Own(env));
            try
            {
                return KernelExceptions.Catch(() =>
                {
                    using var tc = new TypeChecker(new Kernel.Environment(kenv), lctx);
                    return KernelOwnedResult(tc.Whnf(new Expr(a)));
                });
            }
            finally
            {
                lean_dec(kenv); lean_dec(env); lean_dec(lctx); lean_dec(a);
            }
        }

        public static Obj lean_kernel_check(Obj env, Obj lctx, Obj a)
        {
            Obj kenv = KX.ElabEnvironmentToKernelEnv(RC.Own(env));
            try
            {
                return KernelExceptions.Catch(() =>
                {
                    using var tc = new TypeChecker(new Kernel.Environment(kenv), lctx);
                    return KernelOwnedResult(tc.Check(new Expr(a)));
                });
            }
            finally
            {
                lean_dec(kenv); lean_dec(env); lean_dec(lctx); lean_dec(a);
            }
        }

        // ------------------------------------------------------------------------------------
        // Constructions

        /// <summary>`mkCasesOnImp (env : Kernel.Environment) (declName : @&amp; Name)`.</summary>
        public static Obj lean_mk_cases_on(Obj env, Obj n)
        {
            try
            {
                return KernelExceptions.Catch(() => CasesOn.MkCasesOn(new Kernel.Environment(env), new Name(n)).Raw);
            }
            finally { lean_dec(env); }
        }
    }
}
