// Kernel infrastructure: reference counting conventions, access to Lean-exported functions,
// natural number helpers, list helpers, resource limits (heartbeats, recursion depth,
// cancellation) and the kernel exception hierarchy (port of kernel/kernel_exception.h and
// runtime/interrupt.cpp).
//
// Reference counting conventions used throughout the kernel port
// ----------------------------------------------------------------
// The C++ kernel manipulates Lean objects through `object_ref` wrappers whose copies `inc` and
// whose destructors `dec`. In C# memory is reclaimed by the GC, so reference counts only matter
// for Lean's destructive updates (`lean_is_exclusive`). A missing `inc` can cause an object we
// still use to be destructively updated, while a leaked `inc` only disables an optimization.
// Therefore:
//   * Kernel-internal values (`Expr`, `Level`, `Name`, raw `Obj`) are *borrowed views*; binding them
//     to locals, fields of C# objects, or cache entries does not touch reference counts.
//   * Whenever a value is passed to a Lean function taking an owned argument, or stored into a
//     Lean object, it is `inc`ed first (`RC.Own`). Results of Lean functions are owned and are
//     simply kept (and never `dec`ed, i.e., leaked), except for the linearly threaded objects
//     (environments, local contexts, metavariable contexts, diagnostics) which are moved exactly
//     as in the C++ code.
//   * Extern results are `inc`ed unless they are known to be fresh or transferred ownership.

using System.Numerics;
using System.Runtime.CompilerServices;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

internal static class RC
{
    /// <summary>`to_obj_arg()`: increment the reference count and return the object (to be passed as owned argument).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj Own(Obj o) { lean_inc(o); return o; }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Dec(Obj o) { if (o != null) lean_dec(o); }

    /// <summary>Allocate a constructor object with the given (owned) object fields.</summary>
    public static Obj MkCnstr(uint tag, params Obj[] fields)
    {
        var r = lean_alloc_ctor(tag, (uint)fields.Length, 0);
        for (int i = 0; i < fields.Length; i++) lean_ctor_set(r, (uint)i, fields[i]);
        return r;
    }

    /// <summary>`is_exclusive`-based sharing test used by the C++ caches (`is_shared`).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool IsShared(Obj o) => o.m_rc != 1;

    /// <summary>`is_likely_unshared`: RC is 1 (single threaded) or -1 (multi threaded).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool IsLikelyUnshared(Obj o) => o.m_rc == 1 || o.m_rc == -1;
}

/// <summary>Reference-identity key for pairs of objects (pointer-pair caches).</summary>
internal readonly struct ObjPair : IEquatable<ObjPair>
{
    public readonly Obj A, B;
    public ObjPair(Obj a, Obj b) { A = a; B = b; }
    public bool Equals(ObjPair o) => ReferenceEquals(A, o.A) && ReferenceEquals(B, o.B);
    public override bool Equals(object obj) => obj is ObjPair p && Equals(p);
    public override int GetHashCode() => HashCode.Combine(RuntimeHelpers.GetHashCode(A), RuntimeHelpers.GetHashCode(B));
}

/// <summary>Reference-identity key for (object, offset) caches.</summary>
internal readonly struct ObjOffset : IEquatable<ObjOffset>
{
    public readonly Obj O;
    public readonly uint Offset;
    public ObjOffset(Obj o, uint offset) { O = o; Offset = offset; }
    public bool Equals(ObjOffset o) => ReferenceEquals(O, o.O) && Offset == o.Offset;
    public override bool Equals(object obj) => obj is ObjOffset p && Equals(p);
    public override int GetHashCode() => HashCode.Combine(RuntimeHelpers.GetHashCode(O), Offset);
}

/// <summary>Natural number helpers (`util/nat.h`), on `Nat` objects (boxed or `MpzObj`).</summary>
internal static class Nat
{
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool IsSmall(Obj n) => lean_is_scalar(n);

    public static BigInteger ToBig(Obj n) => lean_nat_to_big(n);

    public static Obj OfBig(BigInteger v) => lean_big_to_nat(v);

    public static Obj Of(ulong v) => lean_usize_to_nat(v);

    public static bool Eq(Obj a, Obj b)
    {
        if (ReferenceEquals(a, b)) return true;
        if (lean_is_scalar(a) && lean_is_scalar(b)) return lean_unbox(a) == lean_unbox(b);
        if (lean_is_scalar(a) != lean_is_scalar(b)) return false; // invariant: small values are always boxed
        return ToBig(a) == ToBig(b);
    }

    public static bool Eq(Obj a, ulong b) => lean_is_scalar(a) && lean_unbox(a) == b;

    public static bool Lt(Obj a, Obj b)
    {
        if (lean_is_scalar(a) && lean_is_scalar(b)) return lean_unbox(a) < lean_unbox(b);
        return ToBig(a) < ToBig(b);
    }

    public static bool Le(Obj a, Obj b)
    {
        if (lean_is_scalar(a) && lean_is_scalar(b)) return lean_unbox(a) <= lean_unbox(b);
        return ToBig(a) <= ToBig(b);
    }

    /// <summary>`n >= k` for a machine integer `k`.</summary>
    public static bool Ge(Obj n, ulong k) => !lean_is_scalar(n) || lean_unbox(n) >= k;

    public static bool IsZero(Obj n) => lean_is_scalar(n) && lean_unbox(n) == 0;

    public static Obj Add(Obj a, ulong k)
    {
        if (lean_is_scalar(a))
        {
            ulong v = lean_unbox(a);
            ulong r = v + k;
            if (r >= v && r <= LEAN_MAX_SMALL_NAT) return lean_box(r);
        }
        return OfBig(ToBig(a) + k);
    }

    /// <summary>Truncated subtraction.</summary>
    public static Obj Sub(Obj a, ulong k)
    {
        if (lean_is_scalar(a))
        {
            ulong v = lean_unbox(a);
            return lean_box(v >= k ? v - k : 0);
        }
        var r = ToBig(a) - k;
        return OfBig(r.Sign < 0 ? BigInteger.Zero : r);
    }

    /// <summary>`lean_nat_size_in_bytes`.</summary>
    public static ulong SizeInBytes(Obj n)
    {
        if (lean_is_scalar(n)) return 8;
        var v = ToBig(n);
        // number of limbs * 8 (GMP uses 64-bit limbs)
        long bits = (long)v.GetBitLength();
        long limbs = (bits + 63) / 64;
        if (limbs == 0) limbs = 1;
        return (ulong)(limbs * 8);
    }

    public static string ToDecimal(Obj n) => lean_is_scalar(n) ? lean_unbox(n).ToString() : ToBig(n).ToString();
}

/// <summary>Helpers for Lean `List` objects (`list_ref`).</summary>
internal static class KList
{
    public static readonly Obj Nil = lean_box(0);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool IsNil(Obj l) => lean_is_scalar(l);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj Head(Obj l) => lean_ctor_get(l, 0);
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj Tail(Obj l) => lean_ctor_get(l, 1);

    public static int Length(Obj l)
    {
        int n = 0;
        while (!lean_is_scalar(l)) { n++; l = lean_ctor_get(l, 1); }
        return n;
    }

    /// <summary>Borrowed elements of the list.</summary>
    public static List<Obj> ToList(Obj l)
    {
        var r = new List<Obj>();
        while (!lean_is_scalar(l)) { r.Add(lean_ctor_get(l, 0)); l = lean_ctor_get(l, 1); }
        return r;
    }

    public static IEnumerable<Obj> Iter(Obj l)
    {
        while (!lean_is_scalar(l)) { yield return lean_ctor_get(l, 0); l = lean_ctor_get(l, 1); }
    }

    /// <summary>`cons` taking owned arguments.</summary>
    public static Obj Cons(Obj h, Obj t) => lean_mk_list_cons(h, t);

    /// <summary>Build a list from borrowed elements (each element is `inc`ed).</summary>
    public static Obj OfBorrowed(IReadOnlyList<Obj> xs)
    {
        Obj r = lean_box(0);
        for (int i = xs.Count - 1; i >= 0; i--) r = lean_mk_list_cons(RC.Own(xs[i]), r);
        return r;
    }

    public static Obj OfBorrowed(IReadOnlyList<Expr> xs)
    {
        Obj r = lean_box(0);
        for (int i = xs.Count - 1; i >= 0; i--) r = lean_mk_list_cons(RC.Own(xs[i].Raw), r);
        return r;
    }

    public static Obj OfBorrowed(IReadOnlyList<Name> xs)
    {
        Obj r = lean_box(0);
        for (int i = xs.Count - 1; i >= 0; i--) r = lean_mk_list_cons(RC.Own(xs[i].Raw), r);
        return r;
    }

    public static Obj OfBorrowed(IReadOnlyList<Level> xs)
    {
        Obj r = lean_box(0);
        for (int i = xs.Count - 1; i >= 0; i--) r = lean_mk_list_cons(RC.Own(xs[i].Raw), r);
        return r;
    }

    /// <summary>Build a list from owned elements.</summary>
    public static Obj OfOwned(IReadOnlyList<Obj> xs)
    {
        Obj r = lean_box(0);
        for (int i = xs.Count - 1; i >= 0; i--) r = lean_mk_list_cons(xs[i], r);
        return r;
    }

    /// <summary>`option_ref`: return the value of `some v` (borrowed from the option object), or null for `none`.</summary>
    public static Obj OptionVal(Obj o) => lean_is_scalar(o) ? null : lean_ctor_get(o, 0);
}

// ----------------------------------------------------------------------------------------------
// Resource limits (port of the parts of runtime/interrupt.cpp used by the kernel)

/// <summary>Heartbeats, recursion depth and cancellation for the kernel.</summary>
/// <remarks>
/// As in the C++ runtime (`g_heartbeat`, `g_max_heartbeat` in interrupt.cpp) the kernel counts its
/// own `check_heartbeat` calls per thread, separately from the allocation counter that
/// `IO.getNumHeartbeats` reads. The count is reset when a task starts.
/// </remarks>
public static class KernelLimits
{
    [ThreadStatic] static ulong t_heartbeat;
    [ThreadStatic] static ulong t_maxHeartbeat;
    [ThreadStatic] static ulong t_maxRecDepth;
    [ThreadStatic] static ulong t_recDepth;
    [ThreadStatic] static Obj t_cancelTk;

    /// <summary>`g_kernel_rec_depth_factor`.</summary>
    public const ulong KernelRecDepthFactor = 16;

    /// <summary>`g_heartbeat`: number of `check_heartbeat` calls on this thread since the current task started.</summary>
    public static ulong Heartbeat => t_heartbeat;

    public static ulong MaxHeartbeat { get => t_maxHeartbeat; set => t_maxHeartbeat = value; }

    public static void AddHeartbeats(ulong n) => t_heartbeat += n;

    public static void ResetHeartbeat() => t_heartbeat = 0;

    /// <summary>`check_heartbeat`.</summary>
    public static void CheckHeartbeat()
    {
        AddHeartbeats(1);
        ulong max = t_maxHeartbeat;
        if (max > 0 && Heartbeat > max)
            throw new HeartbeatException();
    }

    /// <summary>`check_interrupted`: the cancel token's `setRef : IO.Ref Bool` is field 1.</summary>
    public static void CheckInterrupted()
    {
        var tk = t_cancelTk;
        if (tk != null)
        {
            Obj setRef = lean_ctor_get(tk, 1);
            Obj v = ((RefObj)setRef).m_value;
            if (v != null && lean_unbox(v) != 0)
                throw new KernelInterruptedException();
        }
    }

    /// <summary>`check_stack`: throw a (catchable) stack space exception instead of overflowing the thread stack.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void CheckStack(string component)
    {
        if (!RuntimeHelpers.TryEnsureSufficientExecutionStack())
            throw new StackSpaceException(component);
    }

    /// <summary>`check_system`.</summary>
    public static void CheckSystem(string component, bool doCheckInterrupted = false)
    {
        CheckStack(component);
        if (doCheckInterrupted)
        {
            CheckInterrupted();
            CheckHeartbeat();
        }
    }

    /// <summary>`scope_rec_depth` constructor. Must be paired with <see cref="LeaveRecDepth"/>.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void EnterRecDepth()
    {
        ulong d = ++t_recDepth;
        ulong max = t_maxRecDepth;
        if (max > 0 && d > max * KernelRecDepthFactor)
        {
            t_recDepth--;
            throw new StackSpaceException("type checker");
        }
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void LeaveRecDepth() => t_recDepth--;

    /// <summary>Saved state of the scoped limits (`scope_max_heartbeat`, `scope_max_rec_depth`, `scope_cancel_tk`).</summary>
    public readonly struct Scope : IDisposable
    {
        readonly ulong m_maxHeartbeat, m_maxRecDepth, m_recDepth;
        readonly Obj m_cancelTk;
        readonly bool m_setHb, m_setRec, m_setTk;

        public Scope(ulong? maxHeartbeat, ulong? maxRecDepth, bool setCancelTk, Obj cancelTk)
        {
            m_maxHeartbeat = t_maxHeartbeat; m_maxRecDepth = t_maxRecDepth; m_recDepth = t_recDepth; m_cancelTk = t_cancelTk;
            m_setHb = maxHeartbeat.HasValue; m_setRec = maxRecDepth.HasValue; m_setTk = setCancelTk;
            if (maxHeartbeat.HasValue) t_maxHeartbeat = maxHeartbeat.Value;
            if (maxRecDepth.HasValue) { t_maxRecDepth = maxRecDepth.Value; t_recDepth = 0; }
            if (setCancelTk) t_cancelTk = cancelTk;
        }

        public void Dispose()
        {
            if (m_setHb) t_maxHeartbeat = m_maxHeartbeat;
            if (m_setRec) { t_maxRecDepth = m_maxRecDepth; t_recDepth = m_recDepth; }
            if (m_setTk) t_cancelTk = m_cancelTk;
        }
    }
}

// ----------------------------------------------------------------------------------------------
// Exceptions (port of kernel/kernel_exception.h and runtime/exception.h)

/// <summary>`lean::exception`: generic error, reported as `Kernel.Exception.other msg`.</summary>
public class KernelError : Exception
{
    public KernelError(string msg) : base(msg) { }
}

/// <summary>`heartbeat_exception` (`deterministicTimeout`).</summary>
public sealed class HeartbeatException : Exception
{
    public HeartbeatException() : base("(deterministic) timeout") { }
}

/// <summary>`memory_exception` (`excessiveMemory`).</summary>
public sealed class KernelMemoryException : Exception
{
    public KernelMemoryException(string component) : base("excessive memory consumption detected at '" + component + "'") { }
}

/// <summary>`stack_space_exception` (`deepRecursion`).</summary>
public sealed class StackSpaceException : Exception
{
    public StackSpaceException(string component) : base("deep recursion was detected at '" + component + "'") { }
}

/// <summary>`interrupted` (`interrupted`).</summary>
public sealed class KernelInterruptedException : Exception
{
    public KernelInterruptedException() : base("interrupted") { }
}

/// <summary>`kernel_exception`. All fields are owned by the exception (as C++ copies them).</summary>
public class KernelException : KernelError
{
    /// <summary>Owned reference to the environment.</summary>
    public readonly Obj Env;
    public KernelException(Obj env, string msg) : base(msg) { Env = RC.Own(env); }
    public KernelException(Obj env) : this(env, "kernel exception") { }

    /// <summary>Build the `Kernel.Exception` object (owned). Returns null for exceptions reported as `other`.</summary>
    public virtual Obj ToLean() => null;

    protected static Obj O(Obj o) => RC.Own(o);
}

internal sealed class UnknownConstantException : KernelException
{
    readonly Obj m_n;
    public UnknownConstantException(Obj env, Name n) : base(env, "unknown constant '" + n + "'") { m_n = O(n.Raw); }
    public override Obj ToLean() => RC.MkCnstr(0, O(Env), O(m_n));
}

internal sealed class AlreadyDeclaredException : KernelException
{
    readonly Obj m_n;
    public AlreadyDeclaredException(Obj env, Name n) : base(env, "already declared '" + n + "'") { m_n = O(n.Raw); }
    public override Obj ToLean() => RC.MkCnstr(1, O(Env), O(m_n));
}

internal sealed class DefinitionTypeMismatchException : KernelException
{
    readonly Obj m_decl, m_given;
    public DefinitionTypeMismatchException(Obj env, Obj decl, Expr givenType) : base(env) { m_decl = O(decl); m_given = O(givenType.Raw); }
    public override Obj ToLean() => RC.MkCnstr(2, O(Env), O(m_decl), O(m_given));
}

internal sealed class DeclarationHasMetavarsException : KernelException
{
    readonly Obj m_n, m_e;
    public DeclarationHasMetavarsException(Obj env, Name n, Expr e) : base(env) { m_n = O(n.Raw); m_e = O(e.Raw); }
    public override Obj ToLean() => RC.MkCnstr(3, O(Env), O(m_n), O(m_e));
}

internal sealed class DeclarationHasFreeVarsException : KernelException
{
    readonly Obj m_n, m_e;
    public DeclarationHasFreeVarsException(Obj env, Name n, Expr e) : base(env) { m_n = O(n.Raw); m_e = O(e.Raw); }
    public override Obj ToLean() => RC.MkCnstr(4, O(Env), O(m_n), O(m_e));
}

/// <summary>`kernel_exception_with_lctx`.</summary>
internal class KernelExceptionWithLCtx : KernelException
{
    public readonly Obj LCtx;
    public KernelExceptionWithLCtx(Obj env, Obj lctx) : base(env) { LCtx = O(lctx); }
}

internal sealed class FunctionExpectedException : KernelExceptionWithLCtx
{
    readonly Obj m_fn;
    public FunctionExpectedException(Obj env, Obj lctx, Expr fn) : base(env, lctx) { m_fn = O(fn.Raw); }
    public override Obj ToLean() => RC.MkCnstr(5, O(Env), O(LCtx), O(m_fn));
}

internal sealed class TypeExpectedException : KernelExceptionWithLCtx
{
    readonly Obj m_type;
    public TypeExpectedException(Obj env, Obj lctx, Expr type) : base(env, lctx) { m_type = O(type.Raw); }
    public override Obj ToLean() => RC.MkCnstr(6, O(Env), O(LCtx), O(m_type));
}

internal sealed class DefTypeMismatchException : KernelExceptionWithLCtx
{
    readonly Obj m_n, m_given, m_expected;
    public DefTypeMismatchException(Obj env, Obj lctx, Name n, Expr given, Expr expected) : base(env, lctx)
    { m_n = O(n.Raw); m_given = O(given.Raw); m_expected = O(expected.Raw); }
    public override Obj ToLean() => RC.MkCnstr(7, O(Env), O(LCtx), O(m_n), O(m_given), O(m_expected));
}

internal sealed class ExprTypeMismatchException : KernelExceptionWithLCtx
{
    readonly Obj m_e, m_expected;
    public ExprTypeMismatchException(Obj env, Obj lctx, Expr e, Expr expected) : base(env, lctx) { m_e = O(e.Raw); m_expected = O(expected.Raw); }
    public override Obj ToLean() => RC.MkCnstr(8, O(Env), O(LCtx), O(m_e), O(m_expected));
}

internal sealed class AppTypeMismatchException : KernelExceptionWithLCtx
{
    readonly Obj m_app, m_fnType, m_argType;
    public AppTypeMismatchException(Obj env, Obj lctx, Expr app, Expr funType, Expr argType) : base(env, lctx)
    { m_app = O(app.Raw); m_fnType = O(funType.Raw); m_argType = O(argType.Raw); }
    public override Obj ToLean() => RC.MkCnstr(9, O(Env), O(LCtx), O(m_app), O(m_fnType), O(m_argType));
}

internal sealed class InvalidProjException : KernelExceptionWithLCtx
{
    readonly Obj m_proj;
    public InvalidProjException(Obj env, Obj lctx, Expr proj) : base(env, lctx) { m_proj = O(proj.Raw); }
    public override Obj ToLean() => RC.MkCnstr(10, O(Env), O(LCtx), O(m_proj));
}

internal sealed class TheoremTypeIsNotPropException : KernelException
{
    readonly Obj m_n, m_type;
    public TheoremTypeIsNotPropException(Obj env, Name n, Expr type) : base(env) { m_n = O(n.Raw); m_type = O(type.Raw); }
    public override Obj ToLean() => RC.MkCnstr(11, O(Env), O(m_n), O(m_type));
}

internal static class KernelExceptions
{
    /// <summary>
    /// `catch_kernel_exceptions`: run `f` (which returns an owned object) and wrap the result into
    /// `Except Kernel.Exception α`.
    /// </summary>
    public static Obj Catch(Func<Obj> f)
    {
        try
        {
            Obj a = f();
            return RC.MkCnstr(1, a);
        }
        catch (KernelError ex)
        {
            if (ex is KernelException kex && kex.ToLean() is Obj kobj)
                return RC.MkCnstr(0, kobj);
            // 12 | other (msg : String)
            return RC.MkCnstr(0, RC.MkCnstr(12, lean_mk_string(ex.Message)));
        }
        catch (HeartbeatException)
        {
            return RC.MkCnstr(0, lean_box(13));
        }
        catch (KernelMemoryException)
        {
            return RC.MkCnstr(0, lean_box(14));
        }
        catch (StackSpaceException)
        {
            return RC.MkCnstr(0, lean_box(15));
        }
        catch (InsufficientExecutionStackException)
        {
            return RC.MkCnstr(0, lean_box(15));
        }
        catch (KernelInterruptedException)
        {
            return RC.MkCnstr(0, lean_box(16));
        }
    }
}
