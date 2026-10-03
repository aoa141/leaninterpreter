// Externs of the IR interpreter (library/ir_interpreter.cpp): `Lean.Environment.evalConstCore`,
// `Lean.runInit`, `Lean.runModInitCore` and `Lean.runMain`.

using LeanInterpreter.Interp;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    /// <summary>`evalConstCore (α) (env : @&amp; Environment) (opts : @&amp; Options) (constName : @&amp; Name) : Except String α`.</summary>
    public static Obj lean_eval_const(Obj env, Obj opts, Obj c)
    {
        try
        {
            lean_inc(env); lean_inc(c);
            Obj declWithSorry = InterpExports.TakeOption(InterpExports.DeclGetSorryDep(env, c));
            if (declWithSorry != null)
            {
                string s = IrName.ToString(declWithSorry);
                lean_dec(declWithSorry);
                throw new InterpreterException($"cannot evaluate code because '{s}' uses 'sorry' and/or contains errors");
            }
            Obj v = Session.With(env, opts, s => s.CallBoxed(c, 0, null));
            var r = lean_alloc_ctor(1, 1, 0);
            lean_ctor_set(r, 0, v);
            return r;
        }
        catch (InterpreterException ex)
        {
            var r = lean_alloc_ctor(0, 1, 0);
            lean_ctor_set(r, 0, lean_mk_string(ex.Message));
            return r;
        }
    }

    /// <summary>`runInit (env : @&amp; Environment) (opts : @&amp; Options) (decl initDecl : @&amp; Name) : IO Unit`.</summary>
    public static Obj lean_run_init(Obj env, Obj opts, Obj decl, Obj initDecl) =>
        Session.With(env, opts, s => s.RunInit(decl, initDecl));

    /// <summary>`runModInitCore (sym : @&amp; String) : IO Bool`: runs the initializer of a compiled
    /// module given the symbol of its initialization function; `false` if there is none. The
    /// modules of the library count as compiled: they were initialized at startup.</summary>
    public static Obj lean_run_mod_init_core(Obj sym)
    {
        bool known = Library.Instance?.IsModuleInitializer(lean_string_to_net(sym)) == true;
        return lean_io_result_mk_ok(lean_box(known ? 1UL : 0UL));
    }

    /// <summary>`runMain (env : @&amp; Environment) (opts : @&amp; Options) (args : @&amp; List String) : BaseIO UInt32`.</summary>
    public static uint lean_eval_main(Obj env, Obj opts, Obj args)
    {
        try
        {
            return Session.With(env, opts, s => s.RunMain(args));
        }
        catch (InterpreterException ex)
        {
            LeanStdStreams.WriteProcessStderr(ex.Message + "\n");
            return 1;
        }
    }

}

/// <summary>Process-level setup of the interpreter (C++ `initialize_ir_interpreter`).</summary>
public static unsafe class LeanInterpreterInit
{
    /// <summary>Registers the `interpreter.prefer_native` option (`register_bool_option`); called
    /// after the library is initialized, like the C++ static initializer.</summary>
    public static void RegisterOptions()
    {
        Obj name = IrName.Mk("interpreter", "prefer_native");
        // DataValue.ofBool (ctor 1 with a `Bool` scalar)
        Obj defValue = lean_alloc_ctor(1, 0, 1);
        lean_ctor_set_uint8_s(defValue, 0, 1);
        // OptionDecl { name, declName := anonymous, defValue, descr, deprecation? := none }
        Obj decl = lean_alloc_ctor(0, 5, 0);
        lean_inc(name);
        lean_ctor_set(decl, 0, name);
        lean_ctor_set(decl, 1, lean_box(0));
        lean_ctor_set(decl, 2, defValue);
        lean_ctor_set(decl, 3, lean_mk_string("(interpreter) whether to use precompiled code where available"));
        lean_ctor_set(decl, 4, lean_box(0));
        var register = (delegate*<Obj, Obj, Obj>)LeanExports.Get("lean_register_option");
        Obj r = register(name, decl);
        if (lean_io_result_is_error(r))
        {
            Obj err = lean_io_result_get_error(r);
            lean_inc(err);
            string msg = InterpExports.TakeString(InterpExports.IoErrorToString(err));
            lean_dec(r);
            throw new InvalidOperationException("LeanInterpreter: " + msg);
        }
        lean_dec(r);
    }
}
