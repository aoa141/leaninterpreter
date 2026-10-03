// `@[extern]` declarations: implemented by the runtime (ExternTable.g.cs), or by a Lean function
// exported under the extern's symbol (`@[extern "lean_whnf"] opaque whnf` in one module,
// `@[export lean_whnf] def whnfImp` in another, linked natively by the C linker).

using LeanInterpreter.Runtime;

namespace LeanInterpreter.Interp;

internal static unsafe partial class ExternTable
{
    static readonly Dictionary<string, nint> s_table = Build();

    static Dictionary<string, nint> Build()
    {
        var t = new Dictionary<string, nint>(StringComparer.Ordinal);
        RegisterGenerated(t);
        t["lean_void_mk"] = (nint)(delegate*<Value[], int, int[], Value>)&lean_void_mk;
        return t;
    }

    static readonly Obj s_box0 = LeanRt.lean_box(0);

    /// <summary>Argument in slot `a` of the frame at `b` (-1: erased, `box(0)`).</summary>
    [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    static Value A(Value[] s, int b, int a) => a < 0 ? new Value { O = s_box0 } : s[b + a];

    // `static inline` functions of lean.h that the generator does not cover

    static Value lean_void_mk(Value[] s, int b, int[] a)
    {
        LeanRt.lean_dec(A(s, b, a[0]).O);
        return Value.Of(s_box0);
    }

    public static bool TryGet(string sym, out nint fn) => s_table.TryGetValue(sym, out fn);
}

internal static class Externs
{
    public static ExternTarget Resolve(Fn g)
    {
        var t = Volatile.Read(ref g.Extern);
        if (t != null) return t;
        string sym = Ir.ExternSymbol(g.Decl, out _) ?? LeanNameMangling.Mangle(g.Name);
        var live = new List<int>();
        for (int i = 0; i < g.Arity; i++)
            if (g.ParamTypes[i] != IrType.Erased && g.ParamTypes[i] != IrType.Void) live.Add(i);
        t = new ExternTarget { Symbol = sym, Live = live.ToArray() };
        if (ExternTable.TryGet(sym, out var fn))
            t.Fn = fn;
        else if (Library.Instance?.ResolveExport(sym) is Fn target && !ReferenceEquals(target, g))
        {
            // C ABI of a Lean function: its non-`void` parameters
            var map = new int[target.Arity];
            int k = 0;
            for (int j = 0; j < target.Arity; j++)
                map[j] = target.ParamTypes[j] == IrType.Void || k >= live.Count ? -1 : live[k++];
            t.Forward = target;
            t.ForwardMap = map;
        }
        Interlocked.CompareExchange(ref g.Extern, t, null);
        return g.Extern;
    }

    public static Exception Missing(Fn g, string sym) =>
        new InterpreterException($"(interpreter) no implementation of the external declaration '{g.Str}' (symbol '{sym}') is available in LeanInterpreter");
}

/// <summary>Entry points of the `@[export]` functions (see ExportStubs.g.cs).</summary>
internal static unsafe partial class ExportStubs
{
    static readonly Obj s_box0 = LeanRt.lean_box(0);

    static Value Invoke(ref Fn cell, string name, params ReadOnlySpan<Value> args)
    {
        Fn g = cell ??= Library.Instance?.ResolveExport(name)
            ?? throw new LeanPanicException($"LeanInterpreter: exported Lean function '{name}' is not available (library not loaded?)");
        if (g.Arity == args.Length) return Machine.Current.Call(g, args);
        // the C ABI omits `void` parameters
        var vals = new Value[g.Arity];
        int k = 0;
        for (int j = 0; j < vals.Length; j++)
            vals[j] = g.ParamTypes[j] == IrType.Void || k >= args.Length ? Value.Of(s_box0) : args[k++];
        return Machine.Current.Call(g, vals);
    }
}
