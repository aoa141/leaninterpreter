// Interpretation of code from the environment of a program: declarations of the file being
// elaborated (`#eval`, macros, `initialize`) and of modules imported from outside the library
// (the user's own modules, `lean --run`). Library functions are shared; everything else is
// looked up in the environment (`Lean.IR.findEnvDecl`) and compiled for this session.

using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Interp;

internal sealed unsafe class Session : Scope
{
    public readonly Obj Env;
    public readonly Obj Opts;
    readonly Dictionary<Obj, Fn> m_fns = new(NameComparer.Instance);

    [ThreadStatic] static Session t_current;

    Session(Obj env, Obj opts)
    {
        // Closures created by interpreted code may outlive the call that created them and still
        // need the environment to compile their callees.
        lean_inc(env);
        lean_inc(opts);
        Env = env;
        Opts = opts;
    }

    /// <summary>Runs `f` with the session of the current thread if it is for the same
    /// environment and options, or with a new one (C++ `with_interpreter`).</summary>
    public static T With<T>(Obj env, Obj opts, Func<Session, T> f)
    {
        var cur = t_current;
        if (cur != null && ReferenceEquals(cur.Env, env) && ReferenceEquals(cur.Opts, opts))
            return f(cur);
        var s = new Session(env, opts);
        t_current = s;
        try { return f(s); }
        finally { t_current = cur; }
    }

    public override Fn Resolve(Obj name)
    {
        var lib = Library.Instance;
        if (lib != null && lib.TryResolve(name, out var fn)) return fn;
        lock (m_fns)
        {
            if (m_fns.TryGetValue(name, out fn)) return fn;
        }
        lean_inc(Env); lean_inc(name);
        Obj decl = InterpExports.TakeOption(InterpExports.FindEnvDecl(Env, name));
        if (decl == null) throw new InterpreterException($"(interpreter) unknown declaration '{IrName.ToString(name)}'");
        lock (m_fns)
        {
            if (m_fns.TryGetValue(name, out fn)) return fn;
            lean_inc(name);
            fn = new Fn(name, decl, this);
            m_fns[name] = fn;
            return fn;
        }
    }

    // ------------------------------------------------------------------
    // Constants and initializers

    /// <summary>Values of the `[init]` declarations run by `lean_run_init` (per logical process:
    /// natively every process runs the initializers of the modules it imports itself).</summary>
    static Dictionary<Obj, Obj> InitGlobals
    {
        get
        {
            var p = LeanContext.Proc;
            var d = (Dictionary<Obj, Obj>)p.InterpreterInitGlobals;
            if (d != null) return d;
            Interlocked.CompareExchange(ref p.InterpreterInitGlobals, new Dictionary<Obj, Obj>(NameComparer.Instance), null);
            return (Dictionary<Obj, Obj>)p.InterpreterInitGlobals;
        }
    }

    public static bool HasInitGlobal(Obj decl)
    {
        var d = InitGlobals;
        lock (d) return d.ContainsKey(decl);
    }

    bool TryInitGlobal(Fn g, out Value v)
    {
        var d = InitGlobals;
        Obj o;
        lock (d)
        {
            if (!d.TryGetValue(g.Name, out o)) { v = default; return false; }
        }
        v = Ir.IsScalar(g.RetType) ? Boxing.Unbox(o, g.RetType) : Value.Of(o);
        return true;
    }

    public Value LoadConstant(Fn g)
    {
        if (TryInitGlobal(g, out var v)) return v;
        lean_inc(Env); lean_inc(g.Name);
        Obj reg = InterpExports.GetRegularInitFnNameFor(Env, g.Name);
        bool hasRegularInit = !lean_is_scalar(reg);
        lean_dec(reg);
        if (hasRegularInit)
            // we don't know whether `[init]` declarations can be re-executed, so let's not
            throw new InterpreterException($"cannot evaluate `[init]` declaration '{g.Str}' in the same module");
        if (g.BodyIsUnreachable)
        {
            // A `builtin_initialize x : T ← ...` constant of a module outside the library:
            // natively only usable compiled; here its initializer is run on first use.
            lean_inc(Env); lean_inc(g.Name);
            Obj init = InterpExports.GetInitFnNameFor(Env, g.Name);
            if (!lean_is_scalar(init))
            {
                Obj initDecl = lean_ctor_get(init, 0);
                lean_inc(initDecl);
                lean_dec(init);
                Obj r = RunInit(g.Name, initDecl);
                bool ok = lean_io_result_is_ok(r);
                lean_dec(r);
                if (ok && TryInitGlobal(g, out v)) return v;
                throw new InterpreterException($"(interpreter) failed to run the initializer of '{g.Str}'");
            }
            throw new InterpreterException($"(interpreter) cannot evaluate constant '{g.Str}': its IR body is `unreachable` (missing initializer?)");
        }
        return Constants.Evaluate(g);
    }

    /// <summary>Runs `initDecl` and stores its value as the value of `decl` (borrowed arguments).</summary>
    public Obj RunInit(Obj decl, Obj initDecl)
    {
        try
        {
            Fn init = Resolve(initDecl);
            Obj r = Machine.Current.CallBoxed(init, [lean_box(0)]);
            if (!lean_io_result_is_ok(r)) return r;
            Obj o = lean_io_result_get_value(r);
            lean_inc(o);
            lean_dec_ref(r);
            lean_mark_persistent(o);
            var d = InitGlobals;
            lock (d)
            {
                if (!d.ContainsKey(decl)) lean_inc(decl);
                d[decl] = o;
            }
            return lean_io_result_mk_ok(lean_box(0));
        }
        catch (InterpreterException ex)
        {
            return InterpExports.IoResultMkError(ex.Message);
        }
    }

    /// <summary>Evaluates `fn` with owned boxed arguments, supporting under- and
    /// over-application and nullary constants (C++ `call_boxed`).</summary>
    public Obj CallBoxed(Obj fn, int n, Obj[] args)
    {
        Fn g = Resolve(fn);
        var m = Machine.Current;
        Obj r;
        if (g.Arity == 0)
        {
            Value v = Constants.Load(g);
            r = Ir.IsScalar(g.RetType) ? Boxing.Box(v, g.RetType) : v.O ?? lean_box(0);
            lean_inc(r);
        }
        else if (n == g.Arity)
            return m.CallBoxed(g, args.AsSpan(0, n));
        else
        {
            r = lean_alloc_closure(Stubs.For(g.Arity + 1), (uint)(g.Arity + 1), 1);
            lean_closure_set(r, 0, g.Handle);
        }
        if (n > 0) r = lean_apply_n(r, (uint)n, args);
        return r;
    }

    public uint RunMain(Obj args)
    {
        Obj mainName = IrName.Mk("main");
        Fn main = Resolve(mainName);
        var callArgs = new List<Obj>();
        if (main.Arity == 2)
        {
            // List String -> IO _
            lean_inc(args);
            callArgs.Add(args);
        }
        else if (main.Arity != 1)
            throw new InterpreterException("(interpreter) unexpected signature of 'main'");
        callArgs.Add(lean_box(0));
        Obj w = Machine.Current.CallBoxed(main, callArgs.ToArray());
        if (lean_io_result_is_ok(w))
        {
            uint ret = 0;
            // `IO UInt32` or `IO (P)Unit`
            if (MainReturnsUInt32(mainName))
                ret = (uint)lean_unbox(lean_io_result_get_value(w));
            lean_dec_ref(w);
            return ret;
        }
        InterpExports.IoResultShowError(w);
        lean_dec_ref(w);
        return 1;
    }

    /// <summary>Is the type of `main` `[_ →] IO UInt32`?</summary>
    bool MainReturnsUInt32(Obj mainName)
    {
        lean_inc(Env);
        Obj kenv = InterpExports.ToKernelEnv(Env);
        lean_inc(mainName);
        Obj ci = InterpExports.TakeOption(InterpExports.EnvironmentFind(kenv, mainName));
        if (ci == null) return false;
        // ConstantInfo.<kind>Info val; val.toConstantVal.type
        Obj ty = Ir.F(Ir.F(Ir.F(ci, 0), 0), 2);
        const uint ExprConst = 4, ExprApp = 5, ExprForall = 7;
        if (lean_obj_tag(ty) == ExprForall) ty = Ir.F(ty, 2);
        if (lean_obj_tag(ty) != ExprApp) return false;
        Obj arg = Ir.F(ty, 1);
        return lean_obj_tag(arg) == ExprConst && IrName.IsAtomic(Ir.F(arg, 0), "UInt32");
    }
}
