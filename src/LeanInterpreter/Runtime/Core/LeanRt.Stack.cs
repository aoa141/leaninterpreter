// Stack overflow detection.
//
// Natively a stack overflow in compiled Lean code hits the guard page; Lean's signal handler
// prints "Stack overflow detected. Aborting." and aborts the process. A .NET stack overflow cannot
// be caught and terminates the OS process, which here may host many Lean programs (a test
// worker, Lake with its in-process `lean` children). So the generated code checks the stack
// itself: `lean_stack_probe()` is emitted at the start of every function that can be part of a
// recursion (and in `lean_apply_N`, through which every recursion via closures passes), and when
// the stack of the thread is nearly used up the program ends like the native one: the message on
// its standard error and exit status 134 (128 + SIGABRT), as an `IO.Process.exit` that unwinds
// the thread.

using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    /// <summary>Lowest stack address generated code may use on this thread (0: unknown, no check).</summary>
    [ThreadStatic] static nuint t_stackLimit;

    /// <summary>
    /// Declares the stack of the current thread: must be called near the start of a thread that
    /// was created with `stackSize` bytes of stack and will run Lean code.
    /// </summary>
    [MethodImpl(MethodImplOptions.NoInlining)]
    public static void lean_declare_thread_stack(long stackSize)
    {
        byte here;
        // Keep room below the limit for the frames between two probes (functions that are not
        // recursive have none, and generated frames can be large) and for unwinding.
        long reserve = Math.Min(stackSize / 4, 16L << 20);
        long usable = stackSize - reserve - (256 << 10);
        t_stackLimit = usable > 0 && (nuint)(&here) > (nuint)usable ? (nuint)(&here) - (nuint)usable : 0;
    }

    /// <summary>Ends the program with Lean's stack overflow message if the thread's stack is nearly exhausted.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_stack_probe()
    {
        byte here;
        if ((nuint)(&here) < t_stackLimit) StackOverflowDetected();
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    static void StackOverflowDetected()
    {
        // one report per thread: while unwinding, code may probe again
        t_stackLimit = 0;
        LeanStdStreams.WriteProcessStderr("\nStack overflow detected. Aborting.\n");
        throw new LeanExitException(134);
    }
}
