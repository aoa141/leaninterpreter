// Global state of the compiled Lean code, per logical process.
//
// The Lean libraries keep their global state in `IO.Ref`s created by `builtin_initialize`
// (registered options and attributes, environment extensions, the search path, the "importing"
// and "run initializers" flags, ...). Natively every program (`lean`, `lake`, each `lean` child of
// Lake) runs in its own OS process and finds that state as module initialization left it.
// LeanInterpreter initializes the compiled modules once per OS process and runs many programs in it,
// some of them concurrently, so the *values* of those refs are kept per logical process:
//
//  * a ref created while the host initializes the compiled modules gets a slot number;
//  * when initialization is complete (`LeanProgramState.FreezeInitialState`) the values are made
//    persistent and become the initial state of every program;
//  * afterwards reads and writes of such a ref go to the slot of the current logical process
//    (`LeanLogicalProcess.Globals`, a copy of the initial state made on first use).
//
// Refs created later (by a program) are ordinary objects.

namespace LeanInterpreter.Runtime;

internal static class LeanGlobalRefs
{
    static readonly object s_lock = new();
    static readonly List<RefObj> s_refs = new();
    static Obj[] s_initial;

    /// <summary>Whether new refs are global (true until the initial state is frozen).</summary>
    public static bool Recording = true;

    /// <summary>Called for refs created after the initial state was frozen (debugging aid).</summary>
    public static Action<RefObj> LateRefHook;

    /// <summary>Whether the initial state has been frozen (global refs are per logical process).</summary>
    public static bool Frozen;

    public static void Register(RefObj r)
    {
        lock (s_lock)
        {
            if (!Recording) return;
            s_refs.Add(r);
            r.m_slot = s_refs.Count;
        }
    }

    public static void Freeze()
    {
        lock (s_lock)
        {
            if (!Recording) return;
            Recording = false;
            var initial = new Obj[s_refs.Count + 1];
            foreach (var r in s_refs)
            {
                Obj v = r.m_value;
                // the value is shared by all logical processes from now on: never update it in place
                LeanRt.lean_mark_persistent(v);
                initial[r.m_slot] = v;
            }
            s_initial = initial;
            Volatile.Write(ref Frozen, true);
        }
    }

    public static Obj[] NewState() => (Obj[])s_initial.Clone();

    public static ref Obj Slot(RefObj r) => ref LeanContext.Proc.Globals[r.m_slot];
}

/// <summary>Host interface to the per-program state of the runtime.</summary>
public static class LeanProgramState
{
    /// <summary>
    /// Called by the host once all compiled Lean modules are initialized: the current values of
    /// the global `IO.Ref`s become the initial state of every program run in this OS process.
    /// </summary>
    public static void FreezeInitialState() => LeanGlobalRefs.Freeze();

    /// <summary>Returns true the first time it is called with `key` in the current program.</summary>
    public static bool TryMarkOnce(string key) => LeanContext.Proc.TryMarkOnce(key);

    /// <summary>
    /// Set by a host whose OS process exists only to run one Lean program (a command-line tool):
    /// `IO.Process.forceExit` in that program then terminates the OS process, as it does natively.
    /// Otherwise it only ends the program (the host keeps running).
    /// </summary>
    public static bool TopLevelProgramOwnsProcess;

    /// <summary>
    /// Marks the start of a Lean program (`lean`, `lake`, ...) on the current thread: it gets a
    /// fresh logical process (working directory and environment inherited from the current one,
    /// global state as initialization left it). In an in-process child the logical process
    /// created for the child is used.
    /// </summary>
    public static void BeginProgram() => LeanContext.BeginProgram();

    /// <summary>
    /// Marks the end of the program started by <see cref="BeginProgram"/> on the current thread.
    /// Natively its remaining threads die with the process: here its tasks see a cancellation
    /// request and its worker threads exit.
    /// </summary>
    public static void EndProgram()
    {
        var p = LeanContext.Proc;
        if (!ReferenceEquals(p, LeanLogicalProcess.Root)) p.MarkExited();
    }
}
