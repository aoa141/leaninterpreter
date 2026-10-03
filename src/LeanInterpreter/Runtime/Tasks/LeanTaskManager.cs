// Port of the task manager of `runtime/object.cpp` (Lean 4): `lean_task_imp`, `task_manager`,
// `deactivate_task`, `deactivate_promise`.
//
// Structure and locking discipline mirror the C++ code: a single manager mutex (here a .NET
// monitor) protects the priority queues, the dependency lists (`m_head_dep`/`m_next_dep`) and the
// worker counters. Functions with a `_core` suffix (and `run_task`, `handle_finished`, ...) are
// called with the mutex held and may temporarily release it, exactly like the C++ functions that
// take a `unique_lock<mutex> &`.
//
// Differences with C:
//  * Worker threads are plain .NET threads created with a large stack
//    (`LeanTaskManager.ThreadStackSize`, 256 MB by default) because Lean code is deeply recursive.
//  * The C++ condition variables are emulated by `LeanCondVar` (FIFO of waiters, so `notify_one`
//    wakes exactly one waiter of *that* condition variable).
//  * Exceptions escaping a task closure (C has none: Lean code does not throw) are caught. The task
//    is finished with a `TaskFailure` value that `lean_task_get` rethrows (see `LeanTaskManager`).
//  * The manager is created lazily when a task is spawned before `lean_init_task_manager`.

using System.Runtime.CompilerServices;
using System.Runtime.ExceptionServices;

namespace LeanInterpreter.Runtime;

/// <summary>`lean_task_imp`: data required for executing a task; dropped once the task has finished.</summary>
internal sealed class TaskImp
{
    public Obj m_closure;
    public TaskObj m_head_dep;
    public TaskObj m_next_dep;
    public uint m_prio;
    public volatile bool m_canceled;
    /// <summary>If true, the task is not deactivated until it has finished (owns one RC token of itself).</summary>
    public bool m_keep_alive;
    public bool m_deleted;
    /// <summary>
    /// The logical call context (logical process, redirected standard streams) of the code that
    /// created the task; installed while the task runs, since worker threads are shared by all
    /// Lean programs running in this OS process.
    /// </summary>
    public readonly LeanCallContext m_ctx = LeanContext.Current;

    public TaskImp(Obj c, uint prio, bool keep_alive)
    {
        m_closure = c;
        m_prio = prio;
        m_keep_alive = keep_alive;
    }
}

/// <summary>
/// Value stored in `TaskObj.m_value` when the task closure threw a .NET exception (e.g.
/// `LeanPanicException` from an internal panic, or `LeanExitException` from `IO.Process.exit`).
/// It is a persistent, field-less constructor object so that code that inspects `m_value` directly
/// sees a harmless value; `lean_task_get` rethrows the original exception.
/// </summary>
public sealed class TaskFailure : Ctor
{
    public readonly ExceptionDispatchInfo Error;
    public TaskFailure(Exception e)
    {
        m_rc = 0; m_tag = 0; m_other = 0;
        Error = ExceptionDispatchInfo.Capture(e);
    }
    public Exception Exception => Error.SourceException;

    [System.Diagnostics.CodeAnalysis.DoesNotReturn]
    public void Rethrow()
    {
        if (Error.SourceException is LeanExitException ex)
            throw new LeanExitException(ex.ExitCode);
        Error.Throw();
    }
}

/// <summary>
/// A condition variable usable with a .NET monitor or a `SemaphoreSlim` used as a mutex (the
/// managed counterpart of `std::condition_variable`). `NotifyOne` wakes exactly one waiter.
/// Spurious wake-ups do not happen, but callers should re-check their predicate as in C++.
/// </summary>
public sealed class LeanCondVar
{
    sealed class Waiter { public bool Signaled; }
    readonly Queue<Waiter> m_waiters = new();

    Waiter Register()
    {
        var w = new Waiter();
        lock (m_waiters) m_waiters.Enqueue(w);
        return w;
    }

    static void Block(Waiter w)
    {
        lock (w)
        {
            while (!w.Signaled) Monitor.Wait(w);
        }
    }

    static void Signal(Waiter w)
    {
        lock (w)
        {
            w.Signaled = true;
            Monitor.Pulse(w);
        }
    }

    /// <summary>Atomically release `monitor` (held exactly once by the caller), wait for a notification, re-acquire `monitor`.</summary>
    public void Wait(object monitor)
    {
        var w = Register();
        Monitor.Exit(monitor);
        try { Block(w); }
        finally { Monitor.Enter(monitor); }
    }

    /// <summary>Same as `Wait(object)` for a mutex implemented by a `SemaphoreSlim(1, 1)` held by the caller.</summary>
    public void Wait(SemaphoreSlim mutex)
    {
        var w = Register();
        mutex.Release();
        try { Block(w); }
        finally { mutex.Wait(); }
    }

    public void NotifyOne()
    {
        Waiter w;
        lock (m_waiters)
        {
            if (!m_waiters.TryDequeue(out w)) return;
        }
        Signal(w);
    }

    public void NotifyAll()
    {
        Waiter[] ws;
        lock (m_waiters)
        {
            if (m_waiters.Count == 0) return;
            ws = m_waiters.ToArray();
            m_waiters.Clear();
        }
        foreach (var w in ws) Signal(w);
    }
}

/// <summary>Port of the C++ `task_manager` class.</summary>
internal sealed unsafe class TaskManager
{
    public const uint LEAN_MAX_PRIO = 8;
    public const uint LEAN_SYNC_PRIO = uint.MaxValue;

    readonly object m_mutex = new();
    readonly List<Thread> m_std_workers = new();
    int m_idle_std_workers;
    int m_max_std_workers;
    int m_num_dedicated_workers;
    readonly Queue<TaskObj>[] m_queues = new Queue<TaskObj>[LEAN_MAX_PRIO + 1];
    int m_queues_size;
    uint m_max_prio;
    readonly LeanCondVar m_queue_cv = new();
    readonly LeanCondVar m_task_finished_cv = new();
    readonly LeanCondVar m_dedicated_finished_cv = new();
    volatile bool m_shutting_down;

    public TaskManager(int max_std_workers)
    {
        m_max_std_workers = max_std_workers;
        for (int i = 0; i < m_queues.Length; i++) m_queues[i] = new Queue<TaskObj>();
    }

    // ------------------------------------------------------------------
    // lock helpers (the C++ code passes `unique_lock<mutex> & lock` around)

    void Lock() => Monitor.Enter(m_mutex);
    void Unlock() => Monitor.Exit(m_mutex);
    void UnlockIfHeld() { if (Monitor.IsEntered(m_mutex)) Monitor.Exit(m_mutex); }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static TaskImp ImpOf(TaskObj t) => Unsafe.As<TaskImp>(t.m_imp);

    // ------------------------------------------------------------------

    TaskObj dequeue()
    {
        var q = m_queues[m_max_prio];
        TaskObj result = q.Dequeue();
        m_queues_size--;
        if (q.Count == 0)
        {
            while (m_max_prio > 0)
            {
                --m_max_prio;
                if (m_queues[m_max_prio].Count != 0) break;
            }
        }
        return result;
    }

    void enqueue_core(TaskObj t)
    {
        TaskImp imp = ImpOf(t);
        uint prio = imp.m_prio;
        if (prio == LEAN_SYNC_PRIO)
        {
            run_task(t);
            return;
        }
        if (prio > LEAN_MAX_PRIO)
        {
            spawn_dedicated_worker(t);
            return;
        }
        if (prio > m_max_prio) m_max_prio = prio;
        m_queues[prio].Enqueue(t);
        m_queues_size++;
        if (m_idle_std_workers == 0 && m_std_workers.Count < m_max_std_workers)
            spawn_worker();
        else
            m_queue_cv.NotifyOne();
    }

    void deactivate_task_core(TaskObj t)
    {
        TaskImp imp = ImpOf(t);
        Obj c = imp.m_closure;
        TaskObj it = imp.m_head_dep;
        imp.m_closure = null;
        imp.m_head_dep = null;
        imp.m_deleted = true;
        imp.m_canceled = true;
        Unlock();
        try
        {
            // The dependent tasks have already been deactivated (they hold an owned reference to
            // `t`); in C they are freed here. Nothing to free with a GC.
            while (it != null)
            {
                TaskImp it_imp = ImpOf(it);
                TaskObj next_it = it_imp?.m_next_dep;
                it = next_it;
            }
            if (c != null) LeanRt.lean_dec_ref(c);
        }
        finally { Lock(); }
    }

    void spawn_worker()
    {
        if (m_shutting_down) return;
        // `mk_thread_proc`: a new thread inherits the creating thread's heartbeat limit
        ulong maxHeartbeat = LeanInterpreter.Kernel.KernelLimits.MaxHeartbeat;
        var th = new Thread(() => { LeanInterpreter.Kernel.KernelLimits.MaxHeartbeat = maxHeartbeat; WorkerMain(); }, LeanTaskManager.ThreadStackSize)
        {
            IsBackground = true,
            Name = "Lean worker",
        };
        m_std_workers.Add(th);
        th.Start();
    }

    void WorkerMain()
    {
        LeanRt.lean_declare_thread_stack(LeanTaskManager.ThreadStackSize);
        Lock();
        try
        {
            m_idle_std_workers++;
            while (true)
            {
                if (m_queues_size == 0)
                {
                    if (m_shutting_down) break; // We're done
                    // Wait for new tasks
                    m_queue_cv.Wait(m_mutex);
                    continue;
                }

                // There's work to be done. If we have reached the maximum number of standard
                // workers (because the maximum was decreased by `task_get`), wait for someone else
                // to become idle before picking up new work (but not during shutdown).
                if (!m_shutting_down && m_std_workers.Count - m_idle_std_workers >= m_max_std_workers)
                {
                    m_queue_cv.Wait(m_mutex);
                    continue;
                }

                TaskObj t = dequeue();
                m_idle_std_workers--;
                run_task(t);
                m_idle_std_workers++;
                LeanTaskManager.ResetHeartbeat?.Invoke();
                LeanRt.IoResetThreadStreams();
            }
            m_idle_std_workers--;
        }
        catch (Exception e)
        {
            // Only reachable through a runtime bug: task exceptions are caught in `run_task`.
            LeanTaskManager.ReportInternalError("worker thread", e);
        }
        finally { UnlockIfHeld(); }
    }

    void spawn_dedicated_worker(TaskObj t)
    {
        m_num_dedicated_workers++;
        ulong maxHeartbeat = LeanInterpreter.Kernel.KernelLimits.MaxHeartbeat;
        var th = new Thread(() =>
        {
            LeanInterpreter.Kernel.KernelLimits.MaxHeartbeat = maxHeartbeat;
            LeanRt.lean_declare_thread_stack(LeanTaskManager.ThreadStackSize);
            Lock();
            try
            {
                run_task(t);
            }
            catch (Exception e)
            {
                LeanTaskManager.ReportInternalError("dedicated worker thread", e);
                if (!Monitor.IsEntered(m_mutex)) Lock();
            }
            finally
            {
                m_num_dedicated_workers--;
                m_dedicated_finished_cv.NotifyAll();
                UnlockIfHeld();
            }
        }, LeanTaskManager.ThreadStackSize)
        {
            IsBackground = true,
            Name = "Lean dedicated worker",
        };
        th.Start();
    }

    /// <summary>Runs the closure of `t`. Called and returns with the mutex held.</summary>
    void run_task(TaskObj t)
    {
        TaskImp imp = ImpOf(t);
        if (imp.m_deleted) return; // free_task(t)
        LeanTaskManager.ResetHeartbeat?.Invoke();
        Obj v = null;
        {
            TaskObj prev = LeanTaskManager.t_current_task;
            LeanTaskManager.t_current_task = t;
            // Run the task in the logical call context of its creator. Worker threads keep the
            // context of their last task (it is replaced by the next task anyway); a `sync` task
            // runs on the thread that finished its dependency, whose context must be restored.
            LeanCallContext prevCtx = LeanContext.Current;
            bool switchCtx = !ReferenceEquals(prevCtx, imp.m_ctx);
            bool restoreCtx = switchCtx && imp.m_prio == LEAN_SYNC_PRIO;
            if (switchCtx) LeanContext.Current = imp.m_ctx;
            try
            {
                Obj c = imp.m_closure;
                imp.m_closure = null;
                Unlock();
                try
                {
                    v = LeanRt.lean_apply_1(c, LeanRt.lean_box(0));
                }
                catch (Exception e)
                {
                    v = LeanTaskManager.MkFailure(e);
                }
                // If deactivation was delayed by `m_keep_alive`, deactivate after the final execution (`v != null`)
                if (v != null && imp.m_keep_alive)
                    LeanRt.lean_dec_ref(t);
            }
            finally
            {
                LeanTaskManager.t_current_task = prev;
                if (restoreCtx) LeanContext.Current = prevCtx;
                if (!Monitor.IsEntered(m_mutex)) Lock();
            }
        }
        if (imp.m_deleted)
        {
            Unlock();
            try { if (v != null) LeanRt.lean_dec(v); }
            finally { Lock(); }
        }
        else if (v != null)
        {
            resolve_core(t, v);
        }
        else
        {
            // `bind` task has not finished yet, re-add as dependency of nested task.
            // NOTE: the closure MUST be extracted before unlocking the mutex as otherwise another
            // thread could deactivate the task and empty `m_closure` in between.
            Obj c = imp.m_closure;
            Unlock();
            try { add_dep(Unsafe.As<TaskObj>(Unsafe.As<Closure>(c).m_objs[0]), t); }
            finally { Lock(); }
        }
    }

    void resolve_core(TaskObj t, Obj v)
    {
        LeanRt.lean_mark_mt(v);
        t.m_value = v;
#pragma warning disable CS0420
        TaskImp imp = Unsafe.As<TaskImp>(Interlocked.Exchange(ref t.m_imp, null));
#pragma warning restore CS0420
        handle_finished(t, imp);
        // After the task has been finished and we propagated dependencies, `imp` can be released.
        m_task_finished_cv.NotifyAll();
    }

    void handle_finished(TaskObj t, TaskImp imp)
    {
        TaskObj it = imp.m_head_dep;
        imp.m_head_dep = null;
        while (it != null)
        {
            TaskImp it_imp = ImpOf(it);
            if (imp.m_canceled) it_imp.m_canceled = true;
            TaskObj next_it = it_imp.m_next_dep;
            it_imp.m_next_dep = null;
            if (!it_imp.m_deleted)
                enqueue_core(it);
            it = next_it;
        }
    }

    static Obj wait_any_check(Obj task_list)
    {
        Obj it = task_list;
        while (!LeanRt.lean_is_scalar(it))
        {
            Obj head = LeanRt.lean_ctor_get(it, 0);
            if (Unsafe.As<TaskObj>(head).m_value != null) return head;
            it = LeanRt.lean_ctor_get(it, 1);
        }
        return null;
    }

    // ------------------------------------------------------------------
    // public interface

    public bool shutting_down() => m_shutting_down;

    public int MaxStdWorkers
    {
        get { lock (m_mutex) return m_max_std_workers; }
    }

    public int NumStdWorkers
    {
        get { lock (m_mutex) return m_std_workers.Count; }
    }

    /// <summary>Adjust the number of standard workers (used when `lean_init_task_manager_using` is called after lazy initialization).</summary>
    public void AdjustMaxStdWorkers(int delta)
    {
        Lock();
        try
        {
            m_max_std_workers = Math.Max(1, m_max_std_workers + delta);
            m_queue_cv.NotifyAll();
        }
        finally { UnlockIfHeld(); }
    }

    /// <summary>Lets the workers exit once the queue is empty, without waiting for them.</summary>
    public void BeginShutdown()
    {
        lock (m_mutex) m_shutting_down = true;
        m_queue_cv.NotifyAll();
    }

    /// <summary>`~task_manager`: waits for all queued tasks and dedicated workers.</summary>
    public void Shutdown()
    {
        Lock();
        try
        {
            m_shutting_down = true;
            // we can assume that `m_std_workers` will not be changed after this line
        }
        finally { UnlockIfHeld(); }
        m_queue_cv.NotifyAll();
        // wait for all workers to finish
        Thread[] workers;
        lock (m_mutex) workers = m_std_workers.ToArray();
        foreach (var th in workers)
            if (th != Thread.CurrentThread) th.Join();
        Lock();
        try
        {
            while (m_num_dedicated_workers != 0) m_dedicated_finished_cv.Wait(m_mutex);
        }
        finally { UnlockIfHeld(); }
    }

    public void enqueue(TaskObj t)
    {
        Lock();
        try { enqueue_core(t); }
        finally { UnlockIfHeld(); }
    }

    public void resolve(TaskObj t, Obj v)
    {
        if (t.m_value != null)
        {
            LeanRt.lean_dec(v);
            return;
        }
        Lock();
        try
        {
            if (t.m_value != null)
            {
                Unlock(); // `dec(v)` could lead to `deactivate_task` trying to take the lock
                LeanRt.lean_dec(v);
                return;
            }
            resolve_core(t, v);
        }
        finally { UnlockIfHeld(); }
    }

    public void add_dep(TaskObj t1, TaskObj t2)
    {
        if (t1.m_value != null)
        {
            enqueue(t2);
            return;
        }
        Lock();
        try
        {
            if (t1.m_value != null)
            {
                enqueue_core(t2);
                return;
            }
            ImpOf(t2).m_next_dep = ImpOf(t1).m_head_dep;
            ImpOf(t1).m_head_dep = t2;
        }
        finally { UnlockIfHeld(); }
    }

    public void wait_for(TaskObj t)
    {
        if (t.m_value != null) return;
        Lock();
        try
        {
            if (t.m_value != null) return;
            // see `Task.get`
            TaskObj cur = LeanTaskManager.t_current_task;
            TaskImp cur_imp = cur == null ? null : ImpOf(cur);
            bool in_pool = cur_imp != null && cur_imp.m_prio <= LEAN_MAX_PRIO;
            if (cur_imp != null && cur_imp.m_prio == LEAN_SYNC_PRIO)
                LeanRt.lean_panic("`Task.get` called from a `(sync := true)` task");
            if (in_pool)
            {
                m_max_std_workers++;
                if (m_idle_std_workers == 0)
                    spawn_worker();
                else
                    m_queue_cv.NotifyOne();
            }
            try
            {
                while (t.m_value == null)
                {
                    LeanTaskManager.ThrowIfExitPending();
                    m_task_finished_cv.Wait(m_mutex);
                }
            }
            finally
            {
                if (in_pool) m_max_std_workers--;
            }
        }
        finally { UnlockIfHeld(); }
    }

    public Obj wait_any(Obj task_list)
    {
        Obj r = wait_any_check(task_list);
        if (r != null) return r;
        Lock();
        try
        {
            while (true)
            {
                r = wait_any_check(task_list);
                if (r != null) return r;
                LeanTaskManager.ThrowIfExitPending();
                m_task_finished_cv.Wait(m_mutex);
            }
        }
        finally { UnlockIfHeld(); }
    }

    /// <summary>Wake up all threads blocked in `wait_for`/`wait_any` (used for exit propagation).</summary>
    public void WakeAllWaiters()
    {
        Lock();
        try { m_task_finished_cv.NotifyAll(); }
        finally { UnlockIfHeld(); }
    }

    public void deactivate_task(TaskObj t)
    {
        Lock();
        try
        {
            Obj v = t.m_value;
            if (v != null)
            {
                Unlock();
                LeanRt.lean_dec(v);
                return;
            }
            deactivate_task_core(t);
        }
        finally { UnlockIfHeld(); }
    }

    public void cancel(TaskObj t)
    {
        Lock();
        try
        {
            TaskImp imp = ImpOf(t);
            if (imp != null) imp.m_canceled = true;
        }
        finally { UnlockIfHeld(); }
    }

    public byte get_task_state(TaskObj t)
    {
        Lock();
        try
        {
            TaskImp imp = ImpOf(t);
            if (imp != null)
                return imp.m_closure != null ? (byte)0 /* waiting (waiting/queued) */ : (byte)1 /* running (running/promised) */;
            return 2; // finished
        }
        finally { UnlockIfHeld(); }
    }
}

/// <summary>
/// Public configuration and state of the LeanInterpreter task manager.
///
/// Exceptions in tasks: C Lean code never throws, but LeanInterpreter uses .NET exceptions for internal
/// panics (`LeanPanicException`) and `IO.Process.exit` (`LeanExitException`). An exception escaping a
/// task closure finishes the task with a `TaskFailure` value:
///  * `Task.get`/`IO.wait`/`IO.waitAny` on such a task rethrow the original exception;
///    `Task.map`/`Task.bind` on it produce a failed task as well (the failure propagates along
///    the dependency chain without running the continuation).
///  * Non-exit exceptions are reported once to stderr (`ReportTaskExceptions`), so that they are
///    not lost if nobody ever waits for the task.
///  * `LeanExitException` (exit from a task; in C `exit()` terminates the process from any thread):
///    the exit code is recorded (`PendingExitCode`), `ExitHandler` is invoked if set (a host may
///    call `Environment.Exit` there for exact C behavior), and every thread blocked in, or later
///    calling, a blocking task operation (`Task.get` on an unfinished task, `IO.waitAny`) throws a
///    new `LeanExitException` with that code. `IO.checkCanceled` returns true afterwards. This
///    propagates the exit to the main thread as long as it (transitively) waits for tasks, which is
///    the normal situation (`lean` waits for its elaboration tasks). `ClearPendingExit` resets it
///    (for in-process hosts that run several programs).
/// </summary>
public static class LeanTaskManager
{
    /// <summary>Stack size of worker threads (default 256 MB; Lean code is deeply recursive).</summary>
    public static int ThreadStackSize = 256 * 1024 * 1024;

    /// <summary>Called when a worker starts running a task (C: `reset_heartbeat()`), to be set by the IO area.</summary>
    public static Action ResetHeartbeat;

    /// <summary>C: `g_lean_report_task_get_blocked_time`; receives the time (ns) a `Task.get` was blocked.</summary>
    public static Action<long> ReportTaskGetBlockedTime;

    /// <summary>Invoked (from the task's thread) when a task throws `LeanExitException`.</summary>
    public static Action<int> ExitHandler;

    /// <summary>Report exceptions escaping task closures to stderr (once per exception).</summary>
    public static bool ReportTaskExceptions = true;

    [ThreadStatic] internal static TaskObj t_current_task;

    /// <summary>
    /// The task manager of one logical process. Natively every program has its own pool of
    /// worker threads; a shared pool deadlocks as soon as all workers of a parent (Lake waiting
    /// for the output of its `lean` children) are blocked while the children need workers.
    /// </summary>
    internal sealed class ProcessState
    {
        public readonly object initLock = new();
        public volatile TaskManager tm;
        /// <summary>Tasks are run synchronously when spawned (C: no task manager; `-j0` or after finalization).</summary>
        public volatile bool syncSpawn;
        public int configuredWorkers;

        /// <summary>The program has ended: let the worker threads exit once the queue is empty.</summary>
        public void EndProgram()
        {
            lock (initLock) syncSpawn = true;
            tm?.BeginShutdown();
        }
    }

    static ProcessState S => LeanContext.Proc.Tasks;

    /// <summary>The task currently executed by this thread (null on non-task threads).</summary>
    public static TaskObj CurrentTask => t_current_task;

    public static bool IsInitialized => S.tm != null && !S.tm.shutting_down();

    /// <summary>Maximum number of standard worker threads currently allowed (grows while workers are blocked in `Task.get`).</summary>
    public static int MaxWorkers => S.tm?.MaxStdWorkers ?? 0;

    /// <summary>Number of standard worker threads that have been created.</summary>
    public static int NumWorkerThreads => S.tm?.NumStdWorkers ?? 0;

    /// <summary>The exit code requested by a task of the current logical process, if any.</summary>
    public static int? PendingExitCode
    {
        get
        {
            var p = LeanContext.Proc;
            return p.ExitPending ? p.ExitCode : null;
        }
    }

    /// <summary>Forget a pending exit of the current logical process.</summary>
    public static void ClearPendingExit() => LeanContext.Proc.ClearPendingExit();

    /// <summary>`LEAN_NUM_THREADS` or the hardware concurrency (C: `get_lean_num_threads`).</summary>
    public static int DefaultNumThreads()
    {
        var s = LeanContext.Proc.GetEnv("LEAN_NUM_THREADS");
        if (s != null)
        {
            // atoi semantics
            int i = 0, n = 0;
            while (i < s.Length && char.IsWhiteSpace(s[i])) i++;
            while (i < s.Length && s[i] >= '0' && s[i] <= '9') { n = n * 10 + (s[i] - '0'); i++; }
            return n;
        }
        return Environment.ProcessorCount;
    }

    internal static void InstallHooks()
    {
        if (LeanRt.TaskDeactivateHook == null) LeanRt.TaskDeactivateHook = LeanRt.deactivate_task;
        if (LeanRt.PromiseDeactivateHook == null) LeanRt.PromiseDeactivateHook = LeanRt.deactivate_promise;
    }

    /// <summary>The manager used to spawn tasks, or null if tasks must run synchronously.</summary>
    internal static TaskManager SpawnManager()
    {
        if (S.syncSpawn) return null;
        return S.tm ?? CreateLazily();
    }

    /// <summary>The manager (created lazily if needed); used for promises and dependencies.</summary>
    internal static TaskManager Manager() => S.tm ?? CreateLazily();

    /// <summary>The manager if it exists.</summary>
    internal static TaskManager Existing => S.tm;

    static TaskManager CreateLazily()
    {
        lock (S.initLock)
        {
            InstallHooks();
            if (S.tm == null)
            {
                int n = DefaultNumThreads();
                S.configuredWorkers = Math.Max(1, n);
                S.tm = new TaskManager(S.configuredWorkers);
            }
            return S.tm;
        }
    }

    internal static void Init(int num_workers)
    {
        TaskManager old = null;
        lock (S.initLock)
        {
            InstallHooks();
            if (num_workers <= 0)
            {
                // C: no task manager, tasks are executed synchronously.
                S.syncSpawn = true;
                return;
            }
            S.syncSpawn = false;
            if (S.tm != null && !S.tm.shutting_down())
            {
                // Already created lazily: adjust the number of workers.
                S.tm.AdjustMaxStdWorkers(num_workers - S.configuredWorkers);
                S.configuredWorkers = num_workers;
                return;
            }
            S.configuredWorkers = num_workers;
            S.tm = new TaskManager(num_workers);
        }
    }

    internal static void FinalizeManager()
    {
        TaskManager tm;
        lock (S.initLock)
        {
            tm = S.tm;
            // C sets `g_task_manager = nullptr`: later spawns run synchronously. We keep the
            // (shut down) manager for operations on existing tasks and promises.
            S.syncSpawn = true;
        }
        tm?.Shutdown();
    }

    // A pending exit belongs to the logical process of the task that called `IO.Process.exit`:
    // an exiting in-process child must not terminate its parent (e.g. Lake) or its siblings.

    internal static bool IsExitPending => LeanContext.Proc.ExitPending;

    /// <summary>Whether the tasks of the logical process `ctx` belongs to should stop (exit requested or program ended).</summary>
    internal static bool IsProcessEnding(LeanCallContext ctx)
    {
        var p = LeanContext.ProcOf(ctx);
        return p.ExitPending || p.Exited;
    }

    internal static void ThrowIfExitPending()
    {
        var p = LeanContext.Proc;
        if (p.ExitPending) throw new LeanExitException(p.ExitCode);
    }

    internal static void RequestExit(int code)
    {
        LeanContext.Proc.RequestExit(code);
        ExitHandler?.Invoke(code);
        S.tm?.WakeAllWaiters();
    }

    static readonly ConditionalWeakTable<Exception, object> s_reported = new();

    internal static TaskFailure MkFailure(Exception e)
    {
        if (e is LeanExitException ex)
        {
            RequestExit(ex.ExitCode);
        }
        else if (e is LeanPanicException)
        {
            // `lean_internal_panic` has printed the message; natively the process exits with 1
            RequestExit(1);
        }
        else if (ReportTaskExceptions)
        {
            // Natively an exception escaping a task (e.g. an interpreter error outside of
            // `evalConst`) terminates the process. Without this, a thread waiting for a promise
            // the failed task was going to resolve would wait forever.
            RequestExit(1);
            bool first;
            lock (s_reported) first = s_reported.TryAdd(e, null);
            if (first)
            {
                try
                {
                    string msg = e is LeanPanicException
                        ? $"LeanInterpreter: task failed with internal panic: {e.Message}\n"
                        : $"LeanInterpreter: uncaught exception in task: {e}\n";
                    LeanIO.StderrWrite(msg);
                }
                catch { }
            }
        }
        return new TaskFailure(e);
    }

    internal static void ReportInternalError(string where, Exception e)
    {
        try { LeanIO.StderrWrite($"LeanInterpreter: internal error in {where}: {e}\n"); } catch { }
    }

    /// <summary>If `t` finished with an exception, returns it.</summary>
    public static bool TryGetTaskException(TaskObj t, out Exception e)
    {
        if (t.m_value is TaskFailure f) { e = f.Exception; return true; }
        e = null;
        return false;
    }
}
