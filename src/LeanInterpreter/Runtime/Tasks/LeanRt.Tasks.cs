// Port of thunks, tasks and promises: `lean.h` (inline functions) and `runtime/object.cpp`
// (`lean_thunk_get_core`, `lean_task_*`, `lean_promise_*`, `deactivate_task`,
// `deactivate_promise`), plus the task externs of `runtime/io.cpp` (`lean_io_as_task`, ...).
//
// Representation: BaseIO actions have their world argument erased in extern signatures, and a
// `BaseIO α` closure is applied to `lean_box(0)` and returns the `α` directly (as in C).

using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    // =======================================
    // Thunks

    public static Obj lean_mk_thunk(Obj c) => CountHeartbeat(new ThunkObj { m_tag = LeanThunk, m_closure = c });

    /// <summary>`Thunk.pure : A -> Thunk A`</summary>
    public static Obj lean_thunk_pure(Obj v) => CountHeartbeat(new ThunkObj { m_tag = LeanThunk, m_value = v });

    /// <summary>Evaluate a thunk (borrowed argument, borrowed result).</summary>
    public static Obj lean_thunk_get_core(Obj t)
    {
        var th = Unsafe.As<ThunkObj>(t);
        while (true)
        {
#pragma warning disable CS0420
            Obj c = Interlocked.Exchange(ref th.m_closure, null);
#pragma warning restore CS0420
            if (c != null)
            {
                // Recall that a closure uses the standard calling convention. `thunk_get`
                // "consumes" the result `r` by storing it at `m_value`, then returns a reference to
                // it. `apply_1` also consumes `c`'s RC.
                Obj r;
                try
                {
                    r = lean_apply_1(c, lean_box(0));
                }
                catch (Exception e)
                {
                    // Not in C (Lean code does not throw): poison the thunk so that every
                    // evaluation (including by threads waiting below) rethrows the exception.
                    th.m_closure = MkThunkRethrowClosure(e);
                    throw;
                }
                lean_mark_mt(r);
                th.m_value = r;
                return r;
            }
            // There is another thread executing the closure. We keep waiting for `m_value` to be
            // set by another thread.
            Obj v;
            while ((v = th.m_value) == null)
            {
                if (th.m_closure != null) break; // poisoned by an exception: retry
                Thread.Yield();
            }
            if (v != null) return v;
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_thunk_get(Obj t)
    {
        Obj r = Unsafe.As<ThunkObj>(t).m_value;
        if (r != null) return r;
        return lean_thunk_get_core(t);
    }

    /// <summary>Primitive for implementing `Thunk.get : Thunk A -> A` (borrowed argument).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_thunk_get_own(Obj t)
    {
        Obj r = lean_thunk_get(t);
        lean_inc(r);
        return r;
    }

    static Obj MkThunkRethrowClosure(Exception e)
    {
        var c = lean_alloc_closure((delegate*<Obj, Obj, Obj>)&ThunkRethrowFn, 2, 1);
        lean_closure_set(c, 0, new TaskFailure(e));
        c.m_rc = 0; // persistent: applying it does not touch RCs
        return c;
    }

    static Obj ThunkRethrowFn(Obj failure, Obj unit)
    {
        Unsafe.As<TaskFailure>(failure).Rethrow();
        return null;
    }

    // =======================================
    // Tasks

    public const uint LEAN_MAX_PRIO = TaskManager.LEAN_MAX_PRIO;
    public const uint LEAN_SYNC_PRIO = TaskManager.LEAN_SYNC_PRIO;
    public const byte LEAN_TASK_STATE_WAITING = 0;
    public const byte LEAN_TASK_STATE_RUNNING = 1;
    public const byte LEAN_TASK_STATE_FINISHED = 2;

    public static void lean_init_task_manager() => lean_init_task_manager_using((uint)LeanTaskManager.DefaultNumThreads());

    public static void lean_init_task_manager_using(uint num_workers) => LeanTaskManager.Init((int)Math.Min(num_workers, int.MaxValue));

    public static void lean_finalize_task_manager() => LeanTaskManager.FinalizeManager();

    /// <summary>`Task.Priority` (a `Nat`) as used by the task manager (C: `lean_unbox(prio)`).</summary>
    static uint TaskPrio(Obj prio)
    {
        if (lean_is_scalar(prio))
        {
            ulong p = lean_unbox(prio);
            return p <= LEAN_MAX_PRIO ? (uint)p : LEAN_MAX_PRIO + 1;
        }
        lean_dec(prio);
        return LEAN_MAX_PRIO + 1; // huge priority: dedicated
    }

    // `lean_set_task_header`: tasks managed by the task manager are multi-threaded objects.
    static TaskObj alloc_task(Obj c, uint prio, bool keep_alive)
    {
        lean_mark_mt(c);
        LeanHeartbeats.t_count += 2; // task object and `lean_task_imp`
        var o = new TaskObj { m_rc = -1, m_tag = LeanTask };
        o.m_imp = new TaskImp(c, prio, keep_alive);
        if (keep_alive) lean_inc_ref(o);
        return o;
    }

    static TaskObj alloc_task(Obj v)
    {
        if (TaskDeactivateHook == null) LeanTaskManager.InstallHooks();
        LeanHeartbeats.t_count++;
        return new TaskObj { m_tag = LeanTask, m_value = v };
    }

    public static Obj lean_task_spawn_core(Obj c, uint prio, bool keep_alive)
    {
        var tm = LeanTaskManager.SpawnManager();
        if (tm == null)
        {
            return lean_task_pure(ApplyCatching(c));
        }
        TaskObj new_task = alloc_task(c, prio, keep_alive);
        tm.enqueue(new_task);
        return new_task;
    }

    /// <summary>Run a closure `Unit -> A` as a `Task A`.</summary>
    public static Obj lean_task_spawn(Obj c, Obj prio) => lean_task_spawn_core(c, TaskPrio(prio), false);

    /// <summary>Convert a value `a : A` into `Task A`.</summary>
    public static Obj lean_task_pure(Obj a) => alloc_task(a);

    /// <summary>Synchronous execution (no task manager): exceptions other than exit become task failures.</summary>
    static Obj ApplyCatching(Obj c)
    {
        try { return lean_apply_1(c, lean_box(0)); }
        catch (LeanExitException) { throw; }
        catch (Exception e) { return LeanTaskManager.MkFailure(e); }
    }

    static Obj task_map_fn(Obj f, Obj t, Obj w)
    {
        Obj v = Unsafe.As<TaskObj>(t).m_value;
        if (v is TaskFailure)
        {
            lean_dec_ref(t);
            lean_dec(f);
            return v; // propagate the failure
        }
        lean_inc(v);
        lean_dec_ref(t);
        return lean_apply_1(f, v);
    }

    static Obj MkClosure3_2(delegate*<Obj, Obj, Obj, Obj> fn, Obj a, Obj b)
    {
        var c = lean_alloc_closure(fn, 3, 2);
        lean_closure_set(c, 0, a);
        lean_closure_set(c, 1, b);
        return c;
    }

    public static Obj lean_task_map_core(Obj f, Obj t, uint prio, bool sync, bool keep_alive)
    {
        var task = Unsafe.As<TaskObj>(t);
        var tm = LeanTaskManager.SpawnManager();
        if ((tm == null || sync) && task.m_value != null)
        {
            if (task.m_value is TaskFailure failure)
            {
                lean_dec(f); lean_dec(t);
                return lean_task_pure(failure);
            }
            if (tm == null) return lean_task_pure(ApplyCatching1(f, lean_task_get_own(t)));
            return lean_task_pure(lean_apply_1(f, lean_task_get_own(t)));
        }
        // No task manager but the dependency is not finished yet (a promise): C would block here;
        // we register the continuation with the (lazily created) manager instead.
        tm ??= LeanTaskManager.Manager();
        TaskObj new_task = alloc_task(MkClosure3_2(&task_map_fn, f, t), sync ? LEAN_SYNC_PRIO : prio, keep_alive);
        tm.add_dep(task, new_task);
        return new_task;
    }

    static Obj ApplyCatching1(Obj f, Obj a)
    {
        try { return lean_apply_1(f, a); }
        catch (LeanExitException) { throw; }
        catch (Exception e) { return LeanTaskManager.MkFailure(e); }
    }

    /// <summary>`Task.map (f : A -> B) (t : Task A) (prio : Nat) (sync : Bool) : Task B`</summary>
    public static Obj lean_task_map(Obj f, Obj t, Obj prio, byte sync) => lean_task_map_core(f, t, TaskPrio(prio), sync != 0, false);

    /// <summary>Wait for a task (borrowed argument, borrowed result). Rethrows the exception of a failed task.</summary>
    public static Obj lean_task_get(Obj t)
    {
        var task = Unsafe.As<TaskObj>(t);
        Obj v = task.m_value;
        if (v == null)
        {
            var tm = LeanTaskManager.Existing ?? LeanTaskManager.Manager();
            var report = LeanTaskManager.ReportTaskGetBlockedTime;
            if (report != null)
            {
                long start = System.Diagnostics.Stopwatch.GetTimestamp();
                tm.wait_for(task);
                long end = System.Diagnostics.Stopwatch.GetTimestamp();
                report((long)((end - start) * (1e9 / System.Diagnostics.Stopwatch.Frequency)));
            }
            else
            {
                tm.wait_for(task);
            }
            v = task.m_value;
        }
        if (v is TaskFailure f) f.Rethrow();
        return v;
    }

    /// <summary>Primitive for implementing `Task.get : Task A -> A`.</summary>
    public static Obj lean_task_get_own(Obj t)
    {
        Obj r = lean_task_get(t);
        lean_inc(r);
        lean_dec(t);
        return r;
    }

    static Obj task_bind_fn2(Obj t, Obj unit)
    {
        Obj v = Unsafe.As<TaskObj>(t).m_value;
        lean_inc(v);
        lean_dec_ref(t);
        return v;
    }

    static Obj task_bind_fn1(Obj x, Obj f, Obj unit)
    {
        Obj v = Unsafe.As<TaskObj>(x).m_value;
        if (v is TaskFailure)
        {
            lean_dec_ref(x);
            lean_dec(f);
            return v; // propagate the failure
        }
        lean_inc(v);
        lean_dec_ref(x);
        Obj new_task = lean_apply_1(f, v);
        v = Unsafe.As<TaskObj>(new_task).m_value;
        if (v != null)
        {
            lean_inc(v);
            lean_dec_ref(new_task);
            return v;
        }
        else
        {
            var cur = LeanTaskManager.t_current_task;
            TaskImp imp = Unsafe.As<TaskImp>(cur.m_imp);
            Obj c = lean_alloc_closure((delegate*<Obj, Obj, Obj>)&task_bind_fn2, 2, 1);
            lean_closure_set(c, 0, new_task);
            lean_mark_mt(c);
            imp.m_closure = c;
            return null; // notify queue that task did not finish yet.
        }
    }

    public static Obj lean_task_bind_core(Obj x, Obj f, uint prio, bool sync, bool keep_alive)
    {
        var task = Unsafe.As<TaskObj>(x);
        var tm = LeanTaskManager.SpawnManager();
        if ((tm == null || sync) && task.m_value != null)
        {
            if (task.m_value is TaskFailure failure)
            {
                lean_dec(f); lean_dec(x);
                return lean_task_pure(failure);
            }
            if (tm == null)
            {
                Obj r = ApplyCatching1(f, lean_task_get_own(x));
                return r is TaskFailure ? lean_task_pure(r) : r;
            }
            return lean_apply_1(f, lean_task_get_own(x));
        }
        tm ??= LeanTaskManager.Manager();
        TaskObj new_task = alloc_task(MkClosure3_2(&task_bind_fn1, x, f), sync ? LEAN_SYNC_PRIO : prio, keep_alive);
        tm.add_dep(task, new_task);
        return new_task;
    }

    /// <summary>`Task.bind (x : Task A) (f : A -> Task B) (prio : Nat) (sync : Bool) : Task B`</summary>
    public static Obj lean_task_bind(Obj x, Obj f, Obj prio, byte sync) => lean_task_bind_core(x, f, TaskPrio(prio), sync != 0, false);

    public static bool lean_io_check_canceled_core()
    {
        TaskObj t = LeanTaskManager.t_current_task;
        if (t != null)
        {
            var imp = t.m_imp as TaskImp;
            if (imp != null && imp.m_canceled) return true;
            var tm = LeanTaskManager.Existing;
            if (tm != null && tm.shutting_down()) return true;
            // the task's logical process is exiting or has ended (natively the task would be dead)
            return LeanTaskManager.IsProcessEnding(imp != null ? imp.m_ctx : LeanContext.Current);
        }
        return false;
    }

    public static void lean_io_cancel_core(Obj t)
    {
        var task = Unsafe.As<TaskObj>(t);
        if (task.m_value != null) return;
        LeanTaskManager.Manager().cancel(task);
    }

    public static byte lean_io_get_task_state_core(Obj t)
    {
        var o = Unsafe.As<TaskObj>(t);
        if (o.m_imp == null) return LEAN_TASK_STATE_FINISHED;
        return LeanTaskManager.Manager().get_task_state(o);
    }

    /// <summary>Returns (borrowed) the first finished task of a non-empty `List (Task α)` (borrowed).</summary>
    public static Obj lean_io_wait_any_core(Obj task_list) => LeanTaskManager.Manager().wait_any(task_list);

    /// <summary>`deactivate_task`: the RC of `t` dropped to zero.</summary>
    internal static void deactivate_task(TaskObj t)
    {
        var tm = LeanTaskManager.Existing;
        if (tm != null)
        {
            tm.deactivate_task(t);
        }
        else
        {
            Obj v = t.m_value;
            if (v != null) lean_dec(v);
        }
    }

    // =======================================
    // Promises

    public static Obj lean_promise_new()
    {
        LeanTaskManager.Manager(); // C panics if the task manager is not running; we create it lazily
        LeanHeartbeats.t_count += 3; // task object, `lean_task_imp`, promise object
        var t = new TaskObj { m_rc = -1, m_tag = LeanTask };
        t.m_imp = new TaskImp(null, 0, false);
        // the promise takes ownership of one task token
        return new PromiseObj { m_tag = LeanPromise, m_result = t };
    }

    /// <summary>`value` owned, `promise` borrowed.</summary>
    public static void lean_promise_resolve(Obj value, Obj promise)
    {
        LeanTaskManager.Manager().resolve(Unsafe.As<PromiseObj>(promise).m_result, lean_mk_option_some(value));
    }

    public static Obj lean_io_promise_new() => lean_promise_new();

    public static Obj lean_io_promise_resolve(Obj value, Obj promise)
    {
        lean_promise_resolve(value, promise);
        return lean_box(0);
    }

    public static Obj lean_io_promise_result_opt(Obj promise)
    {
        Obj t = Unsafe.As<PromiseObj>(promise).m_result;
        lean_inc_ref(t);
        return t;
    }

    /// <summary>Whether the promise's underlying task has been resolved.</summary>
    public static bool promise_is_resolved(Obj p) =>
        lean_io_get_task_state_core(Unsafe.As<PromiseObj>(p).m_result) == LEAN_TASK_STATE_FINISHED;

    internal static void deactivate_promise(PromiseObj promise)
    {
        TaskObj r = promise.m_result;
        LeanTaskManager.Manager().resolve(r, lean_mk_option_none());
        lean_dec_ref(r);
    }

    // =======================================
    // IO task primitives (io.cpp)

    /// <summary>`{α : Type} (act : BaseIO α) (_ : IO.RealWorld) : α`</summary>
    static Obj lean_io_as_task_fn(Obj act, Obj w) => lean_apply_1(act, lean_io_mk_world());

    /// <summary>`asTask {α : Type} (act : BaseIO α) (prio : Nat) : BaseIO (Task α)`</summary>
    public static Obj lean_io_as_task(Obj act, Obj prio)
    {
        Obj c = lean_alloc_closure((delegate*<Obj, Obj, Obj>)&lean_io_as_task_fn, 2, 1);
        lean_closure_set(c, 0, act);
        return lean_task_spawn_core(c, TaskPrio(prio), /* keep_alive */ true);
    }

    /// <summary>`{α β : Type} (f : α → BaseIO β) (a : α) : β`</summary>
    static Obj lean_io_bind_task_fn(Obj f, Obj a) => lean_apply_2(f, a, lean_io_mk_world());

    /// <summary>`mapTask (f : α → BaseIO β) (t : Task α) (prio : Nat) (sync : Bool) : BaseIO (Task β)`</summary>
    public static Obj lean_io_map_task(Obj f, Obj t, Obj prio, byte sync)
    {
        Obj c = lean_alloc_closure((delegate*<Obj, Obj, Obj>)&lean_io_bind_task_fn, 2, 1);
        lean_closure_set(c, 0, f);
        return lean_task_map_core(c, t, TaskPrio(prio), sync != 0, /* keep_alive */ true);
    }

    /// <summary>`bindTask (t : Task α) (f : α → BaseIO (Task β)) (prio : Nat) (sync : Bool) : BaseIO (Task β)`</summary>
    public static Obj lean_io_bind_task(Obj t, Obj f, Obj prio, byte sync)
    {
        Obj c = lean_alloc_closure((delegate*<Obj, Obj, Obj>)&lean_io_bind_task_fn, 2, 1);
        lean_closure_set(c, 0, f);
        return lean_task_bind_core(t, c, TaskPrio(prio), sync != 0, /* keep_alive */ true);
    }

    public static byte lean_io_check_canceled() => lean_io_check_canceled_core() ? (byte)1 : (byte)0;

    public static Obj lean_io_cancel(Obj t)
    {
        lean_io_cancel_core(t);
        return lean_box(0);
    }

    public static byte lean_io_get_task_state(Obj t) => lean_io_get_task_state_core(t);

    public static Obj lean_io_wait(Obj t) => lean_task_get_own(t);

    public static Obj lean_io_wait_any(Obj task_list)
    {
        Obj t = lean_io_wait_any_core(task_list);
        Obj v = lean_task_get(t);
        lean_inc(v);
        return v;
    }
}
