// Process-wide initialization: the managed equivalent of `lean_initialize()`
// (src/initialize/init.cpp), with the Lean libraries run by the interpreter.

using LeanInterpreter.Interp;
using LeanInterpreter.Runtime;

namespace LeanInterpreter;

/// <summary>Where LeanInterpreter finds the Lean library files (`.olean`, `.ir`).</summary>
public static class LeanSysroot
{
    static string s_root;

    /// <summary>
    /// The Lean "sysroot": a directory with `lib/lean/` containing the `.olean` and `.ir` files of
    /// `Init`, `Std` and `Lean` (Lean 4.36.0-pre, commit 77f336f7ae). Defaults to the environment
    /// variable `LEAN_SYSROOT`, or `lean-sysroot` next to the LeanInterpreter assembly. Must be
    /// set before the first program runs.
    /// </summary>
    public static string Root
    {
        get
        {
            if (s_root != null) return s_root;
            var env = Environment.GetEnvironmentVariable("LEAN_SYSROOT");
            if (!string.IsNullOrEmpty(env)) return s_root = Path.GetFullPath(env);
            return s_root = Path.Combine(AppContext.BaseDirectory, "lean-sysroot");
        }
        set => s_root = value == null ? null : Path.GetFullPath(value);
    }

    public static string LibDir => Path.Combine(Root, "lib", "lean");

    static readonly string[] s_libraryExtensions = { ".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig" };

    /// <summary>
    /// Copies the files LeanInterpreter needs from the sysroot `source` (a LeanSharp or native
    /// Lean sysroot of the same Lean version) to a new sysroot `destination`: the `.olean*` and
    /// `.ir*` files of `Init`, `Std` and `Lean` (about 2 GB). Returns the number of files copied.
    /// </summary>
    public static int CopyLibrary(string source, string destination)
    {
        string from = Path.Combine(Path.GetFullPath(source), "lib", "lean");
        string to = Path.Combine(Path.GetFullPath(destination), "lib", "lean");
        int n = 0;
        foreach (var root in new[] { "Init", "Std", "Lean" })
        {
            var files = Directory.EnumerateFiles(from, root + ".*")
                .Concat(Directory.Exists(Path.Combine(from, root)) ? Directory.EnumerateFiles(Path.Combine(from, root), "*", SearchOption.AllDirectories) : []);
            foreach (var f in files)
            {
                if (!s_libraryExtensions.Any(e => f.EndsWith(e, StringComparison.Ordinal))) continue;
                var target = Path.Combine(to, Path.GetRelativePath(from, f));
                Directory.CreateDirectory(Path.GetDirectoryName(target));
                File.Copy(f, target, overwrite: true);
                n++;
            }
        }
        return n;
    }
    /// <summary>`IO.appPath` of programs: Lean derives the sysroot from the directory of its executable.</summary>
    public static string LeanExe => Path.Combine(Root, "bin", OperatingSystem.IsWindows() ? "lean.exe" : "lean");
}

public static class LeanHost
{
    static readonly object s_lock = new();
    static bool s_initialized;

    /// <summary>Stack size of the threads running Lean code (interpreted code is deeply recursive).</summary>
    public static int MainThreadStackSize = 1024 * 1024 * 1024;

    /// <summary>
    /// Loads the Lean libraries (`Init`, `Std`, `Lean`) from the sysroot and runs their module
    /// initializers. Idempotent; called implicitly by <see cref="LeanProject"/>. Must run on a
    /// thread with a large stack (see <see cref="RunWithLargeStack{T}"/>).
    /// </summary>
    public static void Initialize()
    {
        lock (s_lock)
        {
            if (s_initialized) return;
            // LEAN_INTERP_TRACE_STARTUP=1: time of each initialization step on stderr
            bool trace = Environment.GetEnvironmentVariable("LEAN_INTERP_TRACE_STARTUP") == "1";
            var sw = System.Diagnostics.Stopwatch.StartNew();
            void Step(string what)
            {
                if (trace) Console.Error.WriteLine($"[startup] {what}: {sw.Elapsed.TotalMilliseconds:F0} ms");
                sw.Restart();
            }
            if (!File.Exists(Path.Combine(LeanSysroot.LibDir, "Init.olean")))
                throw new InvalidOperationException($"LeanInterpreter: no Lean library files in '{LeanSysroot.LibDir}' (set LeanSysroot.Root or LEAN_SYSROOT)");
            try { Directory.CreateDirectory(Path.GetDirectoryName(LeanSysroot.LeanExe)); } catch (IOException) { } catch (UnauthorizedAccessException) { }
            LeanPaths.AppPath = LeanSysroot.LeanExe;
            // the library files never change: map them instead of copying them (Windows)
            LeanInterpreter.Runtime.Compact.LazyRegion.MappedRoots = new[] { Path.GetFullPath(LeanSysroot.LibDir).TrimEnd(Path.DirectorySeparatorChar) + Path.DirectorySeparatorChar };
            ExportStubs.RegisterAll();
            LeanProcess.ProcessSpawnHook = SpawnHook;
            // as in C, every task starts with a fresh count of the kernel's heartbeats
            LeanTaskManager.ResetHeartbeat = LeanInterpreter.Kernel.KernelLimits.ResetHeartbeat;
            Step("register exports");
            var lib = Library.Load(LeanSysroot.LibDir, "Init", "Std", "Lean");
            Step($"load library ({lib.ModuleNames.Count} modules, {lib.DeclCount} declarations)");
            lib.Initialize(trace && Environment.GetEnvironmentVariable("LEAN_INTERP_TRACE_INIT") == "1" ? m => Console.Error.WriteLine("[init] " + m) : null);
            Step("initialize modules");
            LeanInterpreterInit.RegisterOptions();
            // from here on every program gets its own copy of the libraries' global state
            LeanProgramState.FreezeInitialState();
            if (Environment.GetEnvironmentVariable("LEAN_INTERP_CHECK_REFS") == "1") Library.EnableRefCheck();
            Step("freeze global state");
            s_initialized = true;
        }
    }

    /// <summary>
    /// Marks the start of a program run (`lean ...`) on the current thread; dispose the result
    /// when the program has ended. The program gets a fresh logical process (working directory,
    /// environment, the values of the libraries' global `IO.Ref`s, ...) and the runtime state a
    /// previous run may have changed is reset, as in a fresh native process.
    /// </summary>
    internal static IDisposable EnterProgram()
    {
        LeanProgramState.BeginProgram();
        LeanRt.lean_set_exit_on_panic(false);
        LeanRt.lean_set_panic_messages(true);
        LeanTaskManager.ClearPendingExit();
        LeanRuntimeSettings.MaxMemory = 0;
        LeanRuntimeSettings.MaxHeartbeat = 0;
        LeanInterpreter.Kernel.KernelLimits.MaxHeartbeat = 0;
        LeanInterpreter.Kernel.KernelLimits.ResetHeartbeat();
        LeanRuntimeSettings.ThreadStackSize = 0;
        LeanHeartbeats.Set(0);
        return new ProgramScope();
    }

    sealed class ProgramScope : IDisposable
    {
        public void Dispose() => LeanProgramState.EndProgram();
    }

    /// <summary>Runs `f` on a fresh thread with a large stack and waits for it.</summary>
    public static T RunWithLargeStack<T>(Func<T> f, int? stackSize = null)
    {
        T result = default;
        System.Runtime.ExceptionServices.ExceptionDispatchInfo error = null;
        var th = new Thread(() =>
        {
            try
            {
                LeanRt.lean_declare_thread_stack(stackSize ?? MainThreadStackSize);
                result = f();
            }
            catch (Exception e) { error = System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(e); }
        }, stackSize ?? MainThreadStackSize);
        th.Start();
        th.Join();
        error?.Throw();
        return result;
    }

    /// <summary>`lean` subprocesses (e.g. spawned by Lean code) run in-process.</summary>
    static LeanChildProcess SpawnHook(SpawnRequest req)
    {
        var cmd = req.Cmd;
        bool windows = OperatingSystem.IsWindows();
        var cmp = windows ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        bool isLean = string.Equals(cmd, "lean", cmp) || string.Equals(cmd, "lean.exe", cmp);
        if (!isLean)
        {
            try { isLean = string.Equals(Path.GetFullPath(cmd, req.EffectiveCwd), LeanSysroot.LeanExe, cmp); } catch { }
        }
        if (isLean)
            return new InProcessChild(req, ctx => LeanShell.RunOnCurrentThread(req.Args.ToArray()), MainThreadStackSize);
        return null;
    }
}
