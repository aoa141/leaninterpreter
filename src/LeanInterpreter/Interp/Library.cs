// The Lean libraries (Init, Std, Lean), loaded from the `.olean`/`.ir` files of the sysroot and
// run by the interpreter.
//
// This replaces what the native `lean` executable gets from being linked against the compiled
// libraries: the code of every library function (here: its IR from the `.ir` files), the
// `@[export]` symbols (`exportAttr` entries) and the module initializers. A native module
// initializer first initializes the imported modules and then runs the `[builtin_init]` and
// `[init]` declarations of the module in declaration order (the order of the attribute entries
// in the `.olean`); `lean_initialize` does this for `Init`, `Std` and `Lean`. Closed terms and
// other constants, which a native initializer evaluates eagerly, are evaluated on first use.

using LeanInterpreter.Runtime;
using LeanInterpreter.Runtime.Compact;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Interp;

internal sealed class Library : Scope
{
    public static Library Instance { get; private set; }

    readonly string m_libDir;
    // IR declarations of all modules, by name
    readonly Dictionary<Obj, Obj> m_decls = new(NameComparer.Instance);
    readonly Dictionary<Obj, Fn> m_fns = new(NameComparer.Instance);
    // `@[export sym]`: sym -> declaration
    readonly Dictionary<string, Obj> m_exports = new(StringComparer.Ordinal);
    // declaration -> its `[init]`/`[builtin_init]` function (box(0) for `IO Unit` initializers)
    readonly Dictionary<Obj, Obj> m_initFns = new(NameComparer.Instance);
    // modules in initialization order, with their initializer entries in declaration order
    readonly List<(string Module, List<(Obj Decl, Obj InitFn)> Inits)> m_modules = new();
    // symbols of the module initializers (`initialize_<mangled module name>`) of the loaded modules
    readonly HashSet<string> m_moduleInitSymbols = new(StringComparer.Ordinal);
    readonly HashSet<string> m_moduleNames = new(StringComparer.Ordinal);

    Library(string libDir) { m_libDir = libDir; }

    public IReadOnlyCollection<string> ModuleNames => m_moduleNames;
    public int DeclCount => m_decls.Count;

    /// <summary>Loads the given root modules and their imports from `libDir` (`&lt;sysroot&gt;/lib/lean`).</summary>
    public static Library Load(string libDir, params string[] roots)
    {
        var lib = new Library(libDir);
        // the import graph, from the main `.olean` of each module, in initialization order
        var order = new List<Module>();
        var visited = new HashSet<string>(StringComparer.Ordinal);
        foreach (var r in roots) lib.Visit(r, visited, order);
        // the other parts (most of the data), in parallel
        Parallel.ForEach(order, new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount }, lib.ReadParts);
        foreach (var m in order) lib.Add(m);
        Instance = lib;
        return lib;
    }

    sealed class Module
    {
        public string Name;
        public CompactedRegionData Main;
        public readonly List<Obj> Decls = new();
        public readonly List<(Obj Decl, Obj InitFn)> Inits = new();
        public readonly List<(string Sym, Obj Decl)> Exports = new();
    }

    string FileOf(string module, string ext) => Path.Combine(m_libDir, Path.Combine(module.Split('.'))) + ext;

    void Visit(string module, HashSet<string> visited, List<Module> order)
    {
        if (!visited.Add(module)) return;
        string olean = FileOf(module, ".olean");
        if (!File.Exists(olean)) throw new FileNotFoundException($"LeanInterpreter: library file of module '{module}' not found", olean);
        var main = ReadCached(olean, Array.Empty<CompactedRegionData>());
        // imports first (`initialize_<module>` initializes them before the module's own declarations)
        Obj imports = lean_ctor_get(main.Root, 0);
        for (int i = 0; i < Ir.Size(imports); i++)
            Visit(IrName.ToString(lean_ctor_get(Ir.At(imports, i), 0)), visited, order);
        order.Add(new Module { Name = module, Main = main });
    }

    void ReadParts(Module m)
    {
        string olean = FileOf(m.Name, ".olean");
        // the most complete part of the module data: `.olean.private` for modules of the module system
        var data = m.Main;
        if (File.Exists(olean + ".private") && File.Exists(olean + ".server"))
        {
            var server = ReadCached(olean + ".server", new[] { m.Main });
            data = ReadCached(olean + ".private", new[] { m.Main, server });
        }
        var seenInit = new HashSet<Obj>(NameComparer.Instance);
        bool haveIr = false;
        string irFile = FileOf(m.Name, ".ir");
        if (File.Exists(irFile) && File.Exists(irFile + ".sig"))
        {
            var sig = ReadCached(irFile + ".sig", Array.Empty<CompactedRegionData>());
            var ir = ReadCached(irFile, new[] { sig });
            haveIr = true;
            ReadEntries(m, ir.Root, decls: true, seenInit);
        }
        ReadEntries(m, data.Root, decls: !haveIr, seenInit);
    }

    /// <summary>Collects IR declarations, initializers and export names from the extension entries of a module data part.</summary>
    static void ReadEntries(Module mod, Obj moduleData, bool decls, HashSet<Obj> seenInit)
    {
        Obj entries = lean_ctor_get(moduleData, 4);
        int n = Ir.Size(entries);
        // builtin initializers before regular ones (the relative order of the two kinds is not recorded)
        foreach (string want in new[] { "Lean.builtinInitAttr", "Lean.regularInitAttr", "Lean.IR.declMapExt", "Lean.exportAttr" })
        {
            for (int i = 0; i < n; i++)
            {
                Obj e = Ir.At(entries, i);
                string ext = IrName.ToString(lean_ctor_get(e, 0));
                if (ext != want) continue;
                Obj arr = lean_ctor_get(e, 1);
                int m = Ir.Size(arr);
                switch (ext)
                {
                    case "Lean.IR.declMapExt":
                        if (!decls) break;
                        for (int j = 0; j < m; j++) mod.Decls.Add(Ir.At(arr, j));
                        break;
                    case "Lean.builtinInitAttr":
                    case "Lean.regularInitAttr":
                        for (int j = 0; j < m; j++)
                        {
                            Obj x = Ir.At(arr, j);
                            Obj decl = lean_ctor_get(x, 0);
                            if (seenInit.Add(decl)) mod.Inits.Add((decl, lean_ctor_get(x, 1)));
                        }
                        break;
                    case "Lean.exportAttr":
                        for (int j = 0; j < m; j++)
                        {
                            Obj x = Ir.At(arr, j);
                            mod.Exports.Add((IrName.ToString(lean_ctor_get(x, 1)), lean_ctor_get(x, 0)));
                        }
                        break;
                }
            }
        }
    }

    void Add(Module m)
    {
        foreach (var d in m.Decls) m_decls.TryAdd(Ir.DeclName(d), d);
        foreach (var (decl, initFn) in m.Inits) m_initFns.TryAdd(decl, initFn);
        foreach (var (sym, decl) in m.Exports) m_exports.TryAdd(sym, decl);
        m_modules.Add((m.Name, m.Inits));
        m_moduleNames.Add(m.Name);
        // all phases: `initialize_`, and for the module system `runtime_initialize_`/`meta_initialize_`
        foreach (var prefix in new[] { "", "runtime_", "meta_" })
            m_moduleInitSymbols.Add(prefix + "initialize_" + LeanNameMangling.ModuleInitStem(m.Name));
    }

    // ------------------------------------------------------------------
    // Functions

    public bool TryResolve(Obj name, out Fn fn)
    {
        lock (m_fns)
        {
            if (m_fns.TryGetValue(name, out fn)) return true;
            if (!m_decls.TryGetValue(name, out var decl)) return false;
            fn = new Fn(Ir.DeclName(decl), decl, this);
            if (fn.Arity == 0 && m_initFns.TryGetValue(fn.Name, out var initFn) && !lean_is_scalar(initFn))
                fn.InitFn = initFn;
            m_fns[fn.Name] = fn;
            return true;
        }
    }

    public override Fn Resolve(Obj name) =>
        TryResolve(name, out var fn) ? fn : throw new InterpreterException($"(interpreter) unknown declaration '{IrName.ToString(name)}'");

    public Fn Resolve(string dottedName) => Resolve(IrName.Mk(dottedName));

    /// <summary>The function exported as `sym` (`@[export sym]`), or null.</summary>
    public Fn ResolveExport(string sym) =>
        m_exports.TryGetValue(sym, out var decl) && TryResolve(decl, out var fn) ? fn : null;

    /// <summary>Is `sym` the initializer symbol of a module of the library (initialized at startup)?</summary>
    public bool IsModuleInitializer(string sym) => m_moduleInitSymbols.Contains(sym);

    public bool ContainsModule(string module) => m_moduleNames.Contains(module);

    // ------------------------------------------------------------------
    // Initialization

    /// <summary>Runs the initializers of all modules in order (`lean_initialize`).</summary>
    public void Initialize(Action<string> trace = null)
    {
        foreach (var (module, inits) in m_modules)
        {
            trace?.Invoke(module);
            foreach (var (decl, initFn) in inits)
            {
                Obj r;
                if (lean_is_scalar(initFn))
                {
                    // `builtin_initialize <action>` / `initialize <action>`: an `IO Unit` declaration
                    if (!TryResolve(decl, out var act)) continue; // no code (e.g. `meta`-only)
                    r = RunIO(act);
                }
                else
                {
                    if (!TryResolve(decl, out var c)) continue;
                    if (Volatile.Read(ref c.ConstState) == 2) continue; // already run on first use
                    r = RunInit(c);
                }
                if (lean_io_result_is_error(r))
                {
                    InterpExports.IoResultShowError(r);
                    throw new InvalidOperationException($"LeanInterpreter: initialization of module '{module}' failed (declaration '{IrName.ToString(decl)}')");
                }
                lean_dec_ref(r);
            }
        }
    }

    static Obj RunIO(Fn f)
    {
        var args = new Value[f.Arity];
        for (int i = 0; i < args.Length; i++) args[i] = Value.Of(lean_box(0));
        return Machine.Current.Call(f, args).O;
    }

    /// <summary>Runs the initializer of the constant `c` and stores its value; returns the `IO Unit` result.</summary>
    Obj RunInit(Fn c)
    {
        if (!TryResolve(c.InitFn, out var init))
            return lean_io_result_mk_error(InterpExports.MkIoUserError(lean_mk_string($"initializer '{IrName.ToString(c.InitFn)}' of '{c.Str}' not found")));
        if (Interlocked.CompareExchange(ref c.ConstState, 1, 0) != 0)
            return lean_io_result_mk_ok(lean_box(0));
        Obj r = RunIO(init);
        if (lean_io_result_is_ok(r))
        {
            Obj v = lean_io_result_get_value(r);
            lean_inc(v);
            lean_dec_ref(r);
            Value val = Ir.IsScalar(c.RetType) ? Boxing.Unbox(v, c.RetType) : Value.Of(v);
            c.ConstState = 0;
            Constants.Publish(c, val);
            return lean_io_result_mk_ok(lean_box(0));
        }
        c.ConstState = 0;
        return r;
    }

    [ThreadStatic] static Fn t_evaluating;

    internal static void EnableRefCheck() =>
        LeanGlobalRefs.LateRefHook = r =>
        {
            if (t_evaluating != null) Console.Error.WriteLine($"[lean-interpreter] ref created by library constant '{t_evaluating.Str}'");
        };

    public static Value LoadConstant(Fn g)
    {
        if (g.InitFn != null)
        {
            // a `builtin_initialize x : T ← ...` constant used before its module's initializer ran
            Obj r = Instance.RunInit(g);
            if (lean_io_result_is_error(r))
            {
                InterpExports.IoResultShowError(r);
                throw new InterpreterException($"(interpreter) failed to run the initializer of '{g.Str}'");
            }
            lean_dec_ref(r);
            if (Volatile.Read(ref g.ConstState) == 2) return g.ConstVal;
            throw new InterpreterException($"(interpreter) initializer of '{g.Str}' depends on itself");
        }
        if (g.BodyIsUnreachable)
            throw new InterpreterException($"(interpreter) cannot evaluate constant '{g.Str}': it has no code");
        var saved = t_evaluating;
        t_evaluating = g;
        try { return Constants.Evaluate(g); }
        finally { t_evaluating = saved; }
    }
}
