// "Logical processes": the per-process state of a Lean program that LeanInterpreter runs in-process.
//
// A native Lean program owns an OS process: its working directory, environment, standard streams,
// exit status, panic flags and cumulative profiling times are process state. LeanInterpreter runs
// several programs in one OS process (a test worker running one `lean` after the other, Lake
// running many `lean` children concurrently, see `InProcessChild`), so that state lives in a
// `LeanLogicalProcess` instead, and the runtime functions consult the logical process of the
// *current logical call context* before the real process state.
//
// The call context (`LeanCallContext`: the logical process plus the redirected standard streams)
// is an `AsyncLocal`, so it flows to threads, thread-pool work, timers and .NET tasks started by
// the program. Lean tasks are executed by pooled worker threads that are shared by all programs;
// they therefore capture the context when they are created (`TaskImp.m_ctx`) and the task manager
// installs it while the task runs.

namespace LeanInterpreter.Runtime;

/// <summary>Process-like state of one Lean program run in this OS process.</summary>
internal sealed class LeanLogicalProcess
{
    /// <summary>The OS process itself: real working directory and environment.</summary>
    public static readonly LeanLogicalProcess Root = new LeanLogicalProcess(null, null) { m_started = true, OwnsOsProcess = true };

    /// <summary>Whether the end of this program is the end of the OS process (`IO.Process.forceExit` really exits).</summary>
    public bool OwnsOsProcess;

    readonly object m_lock = new();
    /// <summary>Logical working directory (absolute), or null to use the one of the OS process.</summary>
    volatile string m_cwd;
    /// <summary>Logical environment, or null to use the one of the OS process.</summary>
    Dictionary<string, string> m_env;
    /// <summary>Whether a program has started in this process (see <see cref="LeanContext.BeginProgram"/>).</summary>
    bool m_started;

    volatile bool m_exitPending;
    int m_exitCode;
    volatile bool m_exited;

    /// <summary>`g_exit_on_panic` / `g_panic_messages` of this process (null: the process-wide values).</summary>
    public bool? ExitOnPanic, PanicMessages;

    /// <summary>`IO.appPath` of this process (null: the process-wide value).</summary>
    public volatile string AppPath;

    readonly SortedDictionary<string, double> m_cumTimes = new(StringComparer.Ordinal);

    // `LEAN_NAT_MAX_SIZE` as parsed by the kernel (cached per value of the variable).
    string m_natMaxSizeText;
    ulong m_natMaxSize;
    bool m_natMaxSizeValid;

    /// <summary>The task manager of this process.</summary>
    public readonly LeanTaskManager.ProcessState Tasks = new();

    /// <summary>Constants initialized by the IR interpreter in this process (see `IrInterpreter.InitGlobals`).</summary>
    public object InterpreterInitGlobals;

    /// <summary>
    /// `IO.initializing` of this program: true until its `main` starts
    /// (`lean_io_mark_end_initialization`), as in a fresh native process.
    /// </summary>
    public volatile bool IoInitializing = true;

    readonly HashSet<string> m_once = new(StringComparer.Ordinal);

    /// <summary>Returns true the first time it is called with `key` in this process.</summary>
    public bool TryMarkOnce(string key)
    {
        lock (m_once) return m_once.Add(key);
    }

    Obj[] m_globals;

    /// <summary>Values of the global `IO.Ref`s of the compiled Lean code in this process (see `LeanGlobalRefs`).</summary>
    public Obj[] Globals
    {
        get
        {
            var g = m_globals;
            if (g != null) return g;
            Interlocked.CompareExchange(ref m_globals, LeanGlobalRefs.NewState(), null);
            return m_globals;
        }
    }

    public LeanLogicalProcess(string cwd, Dictionary<string, string> env)
    {
        m_cwd = cwd;
        m_env = env;
    }

    static StringComparer EnvComparer => OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;

    /// <summary>A fresh process with the working directory and (a copy of) the environment of this one.</summary>
    public LeanLogicalProcess Fork()
    {
        lock (m_lock)
        {
            return new LeanLogicalProcess(m_cwd, m_env == null ? null : new Dictionary<string, string>(m_env, EnvComparer))
            {
                AppPath = AppPath,
                ExitOnPanic = ExitOnPanic,
                PanicMessages = PanicMessages,
                m_started = true,
            };
        }
    }

    /// <summary>Marks the start of a program; returns false if one has already started in this process.</summary>
    public bool TryStart()
    {
        lock (m_lock)
        {
            if (m_started) return false;
            m_started = true;
            return true;
        }
    }

    // ------------------------------------------------------------------
    // Working directory

    public bool HasLogicalCwd => m_cwd != null;

    /// <summary>The current working directory (absolute).</summary>
    public string Cwd => m_cwd ?? Directory.GetCurrentDirectory();

    /// <summary>
    /// The path the OS must be given for `path`: relative paths are resolved against the logical
    /// working directory if there is one (the path is not normalized otherwise).
    /// </summary>
    public string Resolve(string path)
    {
        string cwd = m_cwd;
        if (cwd == null || string.IsNullOrEmpty(path) || Path.IsPathRooted(path)) return path;
        return Path.Combine(cwd, path);
    }

    /// <summary>`chdir`: `fullPath` is an existing directory (absolute, symbolic links resolved).</summary>
    public void SetCwd(string fullPath)
    {
        if (m_cwd == null) Directory.SetCurrentDirectory(fullPath);
        else m_cwd = fullPath;
    }

    // ------------------------------------------------------------------
    // Environment

    public string GetEnv(string name)
    {
        var env = m_env;
        if (env == null) return System.Environment.GetEnvironmentVariable(name);
        lock (m_lock) return env.TryGetValue(name, out var v) ? v : null;
    }

    /// <summary>`setenv` (`value == null`: `unsetenv`).</summary>
    public void SetEnv(string name, string value)
    {
        var env = m_env;
        if (env == null)
        {
            System.Environment.SetEnvironmentVariable(name, value);
            return;
        }
        lock (m_lock)
        {
            if (value == null) env.Remove(name);
            else env[name] = value;
        }
    }

    /// <summary>A snapshot of the environment.</summary>
    public Dictionary<string, string> EnvironmentSnapshot()
    {
        var env = m_env;
        if (env != null)
        {
            lock (m_lock) return new Dictionary<string, string>(env, EnvComparer);
        }
        var r = new Dictionary<string, string>(EnvComparer);
        foreach (System.Collections.DictionaryEntry e in System.Environment.GetEnvironmentVariables())
            r[(string)e.Key] = (string)e.Value ?? "";
        return r;
    }

    /// <summary>The kernel's `LEAN_NAT_MAX_SIZE` (bytes) for this process.</summary>
    public ulong NatMaxSize(ulong defaultValue)
    {
        string s = GetEnv("LEAN_NAT_MAX_SIZE");
        lock (m_lock)
        {
            if (m_natMaxSizeValid && string.Equals(s, m_natMaxSizeText, StringComparison.Ordinal)) return m_natMaxSize;
            // `read_nat_size_env`: `strtoull` of the whole string, else the default
            ulong v = defaultValue;
            if (s != null)
            {
                string t = s.TrimStart(' ', '\t', '\n', '\v', '\f', '\r');
                if (t.StartsWith('+')) t = t.Substring(1);
                if (t.Length > 0 && t.All(c => c >= '0' && c <= '9'))
                    v = ulong.TryParse(t, System.Globalization.NumberStyles.None, System.Globalization.CultureInfo.InvariantCulture, out ulong p) ? p : ulong.MaxValue;
            }
            m_natMaxSizeText = s;
            m_natMaxSize = v;
            m_natMaxSizeValid = true;
            return v;
        }
    }

    // ------------------------------------------------------------------
    // Exit

    /// <summary>`IO.Process.exit` was called in a task of this process (see `LeanTaskManager`).</summary>
    public bool ExitPending => m_exitPending;
    public int ExitCode => Volatile.Read(ref m_exitCode);

    /// <summary>The program has ended (its remaining tasks should stop).</summary>
    public bool Exited => m_exited;

    public void RequestExit(int code)
    {
        lock (m_lock)
        {
            if (m_exitPending) return;
            Volatile.Write(ref m_exitCode, code);
            m_exitPending = true;
        }
    }

    public void ClearPendingExit() => m_exitPending = false;

    public void MarkExited()
    {
        m_exited = true;
        Tasks.EndProgram();
    }

    // ------------------------------------------------------------------
    // Cumulative profiling times (library/time_task.cpp)

    public void AddProfilingTime(string category, double seconds)
    {
        lock (m_cumTimes)
        {
            m_cumTimes.TryGetValue(category, out var t);
            m_cumTimes[category] = t + seconds;
        }
    }

    public KeyValuePair<string, double>[] ProfilingTimes()
    {
        lock (m_cumTimes) return m_cumTimes.ToArray();
    }
}

/// <summary>The logical call context: redirected standard streams and the logical process (immutable).</summary>
internal sealed class LeanCallContext
{
    /// <summary>Redirected standard streams (null: the process-level streams of `LeanIO`).</summary>
    public readonly Stream In, Out, Err;
    /// <summary>The logical process (null: <see cref="LeanLogicalProcess.Root"/>).</summary>
    public readonly LeanLogicalProcess Proc;

    public LeanCallContext(Stream stdin, Stream stdout, Stream stderr, LeanLogicalProcess proc)
    {
        In = stdin; Out = stdout; Err = stderr; Proc = proc;
    }
}

internal static class LeanContext
{
    static readonly AsyncLocal<LeanCallContext> s_current = new();

    /// <summary>The context of the current logical call context (null: no redirection, root process).</summary>
    public static LeanCallContext Current
    {
        get => s_current.Value;
        set => s_current.Value = value;
    }

    /// <summary>The logical process of the current logical call context.</summary>
    public static LeanLogicalProcess Proc => s_current.Value?.Proc ?? LeanLogicalProcess.Root;

    public static LeanLogicalProcess ProcOf(LeanCallContext ctx) => ctx?.Proc ?? LeanLogicalProcess.Root;

    /// <summary>`path` as the OS must be given it (see <see cref="LeanLogicalProcess.Resolve"/>).</summary>
    public static string ResolvePath(string path)
    {
        var p = s_current.Value?.Proc;
        return p == null ? path : p.Resolve(path);
    }

    /// <summary>Installs `proc` as the logical process of the current call context.</summary>
    public static void SetProcess(LeanLogicalProcess proc)
    {
        var c = s_current.Value;
        s_current.Value = new LeanCallContext(c?.In, c?.Out, c?.Err, proc);
    }

    /// <summary>
    /// Marks the start of a Lean program (the `main` of `lean`, `lake`, ...) on the current thread.
    /// Natively every program starts in a fresh OS process; here it gets a fresh logical process
    /// (inheriting the working directory and environment of the current one), so that per-process
    /// state (pending exit, cumulative profiling times, ...) of an earlier program run by the same
    /// host cannot leak into it. A logical process created for an in-process child
    /// (`InProcessChild`) in which no program has started yet is used as is.
    /// </summary>
    public static void BeginProgram()
    {
        var proc = Proc;
        if (proc.TryStart()) return;
        var p = proc.Fork();
        p.OwnsOsProcess = ReferenceEquals(proc, LeanLogicalProcess.Root) && LeanProgramState.TopLevelProgramOwnsProcess;
        SetProcess(p);
    }
}
