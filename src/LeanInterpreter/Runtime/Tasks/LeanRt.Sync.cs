// Port of the ST ref primitives (`runtime/io.cpp`), the mutex/condition variable externs
// (`runtime/mutex.cpp`), and a few small runtime externs (`lean_runtime_*`, `lean_io_get_tid`,
// `lean_strict_and/or`).
//
// Mutexes are external objects wrapping .NET primitives:
//  * `Std.BaseMutex`          -> `SemaphoreSlim(1, 1)` (not thread-affine, so `Condvar.wait` can
//                                release/re-acquire it; like `std::mutex` it is not recursive)
//  * `Std.BaseRecursiveMutex` -> a .NET monitor (recursive, thread-affine like `std::recursive_mutex`)
//  * `Std.BaseSharedMutex`    -> `ReaderWriterLockSlim` (no recursion, like `std::shared_mutex`)
//  * `Std.Condvar`            -> `LeanCondVar`

using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    // =======================================
    // ST ref primitives
    //
    // Important: `ST.Ref` values created during initialization are marked persistent, so to make
    // the API thread-safe persistent refs are treated like multi-threaded ones. Whenever we store a
    // value into a (maybe) multi-threaded ref we mark it multi-threaded: the runtime relies on the
    // fact that a single-threaded object cannot be reached from a multi-threaded object.

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool ref_maybe_mt(Obj r) => r.m_rc <= 0;

#pragma warning disable CS0420 // Interlocked on volatile fields is fine

    // A ref created during module initialization (`builtin_initialize foo : IO.Ref _ ← ...`) is
    // global state of the program. Its value is kept per logical process (see `LeanGlobalRefs`).
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static bool ref_is_global(RefObj o) => o.m_slot != 0 && LeanGlobalRefs.Frozen;

    static Obj AtomicGet(ref Obj loc)
    {
        var sw = new SpinWait();
        while (true)
        {
            // We cannot simply read `val` and `inc` it since someone else could write to the
            // ref in between and remove the last owning reference to the object. Instead, we
            // take ownership of the RC token in the ref via `exchange`, duplicate it, then put
            // one RC token back.
            Obj val = Interlocked.Exchange(ref loc, null);
            if (val != null)
            {
                lean_inc(val);
                if (Interlocked.CompareExchange(ref loc, val, null) != null)
                {
                    // Another thread stored a value (`put` without `take`) in between; the
                    // ref owns that one now, so drop the token we took from it.
                    lean_dec(val);
                }
                return val;
            }
            sw.SpinOnce(sleep1Threshold: -1);
        }
    }

    static Obj AtomicTake(ref Obj loc)
    {
        var sw = new SpinWait();
        while (true)
        {
            Obj val = Interlocked.Exchange(ref loc, null);
            if (val != null) return val;
            sw.SpinOnce(sleep1Threshold: -1);
        }
    }

    static Obj AtomicPut(ref Obj loc, Obj a)
    {
        lean_mark_mt(a);
        Obj old_a = Interlocked.Exchange(ref loc, a);
        if (old_a != null) lean_dec(old_a); // C asserts `old_a == nullptr` (put after take)
        return lean_box(0);
    }

    static Obj AtomicSwap(ref Obj loc, Obj a)
    {
        lean_mark_mt(a);
        var sw = new SpinWait();
        while (true)
        {
            Obj old_a = Volatile.Read(ref loc);
            if (old_a != null && ReferenceEquals(Interlocked.CompareExchange(ref loc, a, old_a), old_a))
                return old_a;
            sw.SpinOnce(sleep1Threshold: -1);
        }
    }

    public static Obj lean_st_ref_get(Obj r)
    {
        var o = Unsafe.As<RefObj>(r);
        if (ref_is_global(o)) return AtomicGet(ref LeanGlobalRefs.Slot(o));
        if (ref_maybe_mt(r)) return AtomicGet(ref o.m_value);
        Obj val = o.m_value;
        lean_inc(val);
        return val;
    }

    public static Obj lean_st_ref_take(Obj r)
    {
        var o = Unsafe.As<RefObj>(r);
        if (ref_is_global(o)) return AtomicTake(ref LeanGlobalRefs.Slot(o));
        if (ref_maybe_mt(r)) return AtomicTake(ref o.m_value);
        {
            Obj val = o.m_value;
            o.m_value = null;
            return val;
        }
    }

    /// <summary>`ST.Prim.Ref.put`: store into a ref that has been emptied by `take`.</summary>
    public static Obj lean_st_ref_put(Obj r, Obj a)
    {
        var o = Unsafe.As<RefObj>(r);
        if (ref_is_global(o)) return AtomicPut(ref LeanGlobalRefs.Slot(o), a);
        if (ref_maybe_mt(r)) return AtomicPut(ref o.m_value, a);
        if (o.m_value != null) lean_dec(o.m_value);
        o.m_value = a;
        return lean_box(0);
    }

    /// <summary>Alias of `lean_st_ref_put` (older Lean versions exported `ST.Prim.Ref.set` as `lean_st_ref_set`).</summary>
    public static Obj lean_st_ref_set(Obj r, Obj a) => lean_st_ref_put(r, a);

    public static Obj lean_st_ref_swap(Obj r, Obj a)
    {
        var o = Unsafe.As<RefObj>(r);
        if (ref_is_global(o)) return AtomicSwap(ref LeanGlobalRefs.Slot(o), a);
        if (ref_maybe_mt(r)) return AtomicSwap(ref o.m_value, a);
        {
            Obj old_a = o.m_value;
            if (old_a == null)
                throw lean_internal_panic("null reference read");
            o.m_value = a;
            return old_a;
        }
    }

#pragma warning restore CS0420

    public static byte lean_st_ref_ptr_eq(Obj r1, Obj r2) => ReferenceEquals(r1, r2) ? (byte)1 : (byte)0;

    // =======================================
    // Mutexes and condition variables (mutex.cpp)

    static readonly ExternalClass s_basemutexClass = new(null, null);
    static readonly ExternalClass s_condvarClass = new(null, null);
    static readonly ExternalClass s_baserecmutexClass = new(null, null);
    static readonly ExternalClass s_basesharedmutexClass = new(null, null);

    static Obj MkExternal(ExternalClass cls, object data) => lean_alloc_external(cls, data);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static T ExternalData<T>(Obj o) where T : class => Unsafe.As<T>(Unsafe.As<ExternalObj>(o).m_data);

    static SemaphoreSlim basemutex_get(Obj m) => ExternalData<SemaphoreSlim>(m);
    static LeanCondVar condvar_get(Obj c) => ExternalData<LeanCondVar>(c);
    static RecursiveMutex baserecmutex_get(Obj m) => ExternalData<RecursiveMutex>(m);
    static ReaderWriterLockSlim basesharedmutex_get(Obj m) => ExternalData<ReaderWriterLockSlim>(m);

    sealed class RecursiveMutex { }

    public static Obj lean_io_basemutex_new() => MkExternal(s_basemutexClass, new SemaphoreSlim(1, 1));

    public static Obj lean_io_basemutex_lock(Obj mtx)
    {
        basemutex_get(mtx).Wait();
        return lean_box(0);
    }

    public static byte lean_io_basemutex_try_lock(Obj mtx) => basemutex_get(mtx).Wait(0) ? (byte)1 : (byte)0;

    public static Obj lean_io_basemutex_unlock(Obj mtx)
    {
        var s = basemutex_get(mtx);
        // unlocking an unlocked mutex is UB in C++; ignore it instead of overflowing the semaphore
        try { s.Release(); } catch (SemaphoreFullException) { }
        return lean_box(0);
    }

    public static Obj lean_io_condvar_new() => MkExternal(s_condvarClass, new LeanCondVar());

    public static Obj lean_io_condvar_wait(Obj condvar, Obj mtx)
    {
        condvar_get(condvar).Wait(basemutex_get(mtx));
        return lean_box(0);
    }

    public static Obj lean_io_condvar_notify_one(Obj condvar)
    {
        condvar_get(condvar).NotifyOne();
        return lean_box(0);
    }

    public static Obj lean_io_condvar_notify_all(Obj condvar)
    {
        condvar_get(condvar).NotifyAll();
        return lean_box(0);
    }

    public static Obj lean_io_baserecmutex_new() => MkExternal(s_baserecmutexClass, new RecursiveMutex());

    public static Obj lean_io_baserecmutex_lock(Obj mtx)
    {
        Monitor.Enter(baserecmutex_get(mtx));
        return lean_box(0);
    }

    public static byte lean_io_baserecmutex_try_lock(Obj mtx) => Monitor.TryEnter(baserecmutex_get(mtx)) ? (byte)1 : (byte)0;

    public static Obj lean_io_baserecmutex_unlock(Obj mtx)
    {
        var m = baserecmutex_get(mtx);
        if (Monitor.IsEntered(m)) Monitor.Exit(m); // unlocking a mutex not owned by this thread is UB in C++
        return lean_box(0);
    }

    public static Obj lean_io_basesharedmutex_new() =>
        MkExternal(s_basesharedmutexClass, new ReaderWriterLockSlim(LockRecursionPolicy.NoRecursion));

    public static Obj lean_io_basesharedmutex_write(Obj mtx)
    {
        basesharedmutex_get(mtx).EnterWriteLock();
        return lean_box(0);
    }

    public static byte lean_io_basesharedmutex_try_write(Obj mtx)
    {
        try { return basesharedmutex_get(mtx).TryEnterWriteLock(0) ? (byte)1 : (byte)0; }
        catch (LockRecursionException) { return 0; }
    }

    public static Obj lean_io_basesharedmutex_unlock_write(Obj mtx)
    {
        var l = basesharedmutex_get(mtx);
        if (l.IsWriteLockHeld) l.ExitWriteLock();
        return lean_box(0);
    }

    public static Obj lean_io_basesharedmutex_read(Obj mtx)
    {
        basesharedmutex_get(mtx).EnterReadLock();
        return lean_box(0);
    }

    public static byte lean_io_basesharedmutex_try_read(Obj mtx)
    {
        try { return basesharedmutex_get(mtx).TryEnterReadLock(0) ? (byte)1 : (byte)0; }
        catch (LockRecursionException) { return 0; }
    }

    public static Obj lean_io_basesharedmutex_unlock_read(Obj mtx)
    {
        var l = basesharedmutex_get(mtx);
        if (l.IsReadLockHeld) l.ExitReadLock();
        return lean_box(0);
    }

    // =======================================
    // Misc

    /// <summary>`IO.getTID`. The managed thread id (unique among live threads of the process).</summary>
    public static ulong lean_io_get_tid() => (ulong)Environment.CurrentManagedThreadId;

    public static Obj lean_runtime_mark_multi_threaded(Obj a)
    {
        lean_mark_mt(a);
        return a;
    }

    public static Obj lean_runtime_mark_persistent(Obj a)
    {
        lean_mark_persistent(a);
        return a;
    }

    /// <summary>`Runtime.forget`: consumes `o` without releasing it (C only informs the leak sanitizer).</summary>
    public static Obj lean_runtime_forget(Obj o) => lean_box(0);

    /// <summary>`Runtime.hold` (borrowed argument): keeps `a` alive until this point.</summary>
    public static Obj lean_runtime_hold(Obj a)
    {
        GC.KeepAlive(a);
        return lean_box(0);
    }

    public static byte lean_strict_or(byte b1, byte b2) => (b1 != 0 || b2 != 0) ? (byte)1 : (byte)0;

    public static byte lean_strict_and(byte b1, byte b2) => (b1 != 0 && b2 != 0) ? (byte)1 : (byte)0;
}
