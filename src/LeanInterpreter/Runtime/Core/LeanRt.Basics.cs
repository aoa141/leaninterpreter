// Basic helpers shared by all parts of the runtime: strings, arrays, natural numbers, options,
// panics and the table of functions exported from Lean code (`@[export]`).

using System.Numerics;
using System.Runtime.CompilerServices;
using System.Text;

namespace LeanInterpreter.Runtime;

/// <summary>Raised for unrecoverable runtime errors (`lean_internal_panic`).</summary>
public sealed class LeanPanicException : Exception
{
    public LeanPanicException(string msg) : base(msg) { }
}

/// <summary>Raised by `IO.Process.exit`.</summary>
public sealed class LeanExitException : Exception
{
    public readonly int ExitCode;
    public LeanExitException(int code) : base($"exit {code}") { ExitCode = code; }
}

/// <summary>
/// Functions implemented in Lean and exported with `@[export sym]`. The runtime and kernel call
/// them through this table since the generated code lives in assemblies that depend on the runtime.
/// Generated assemblies register their exports at startup.
/// </summary>
public static unsafe class LeanExports
{
    static readonly Dictionary<string, nint> s_table = new();
    static readonly object s_lock = new();

    public static void Register(string name, nint fn)
    {
        lock (s_lock) s_table[name] = fn;
    }

    public static nint Get(string name)
    {
        lock (s_lock)
        {
            if (s_table.TryGetValue(name, out var f)) return f;
        }
        throw new LeanPanicException($"LeanInterpreter: exported Lean function '{name}' is not available (library not loaded?)");
    }

    public static bool TryGet(string name, out nint fn)
    {
        lock (s_lock) return s_table.TryGetValue(name, out fn);
    }
}

public static unsafe partial class LeanRt
{
    // ------------------------------------------------------------------
    // Panics

    // Process-wide values; a logical process other than the root one (an in-process child, see
    // IO/LeanLogicalProcess.cs) has its own flags, as a native child process would.
    public static bool g_exit_on_panic = false;
    public static bool g_panic_messages = true;

    static bool ExitOnPanic => LeanContext.Proc.ExitOnPanic ?? g_exit_on_panic;
    static bool PanicMessages => LeanContext.Proc.PanicMessages ?? g_panic_messages;

    /// <summary>Returns an exception to be thrown by generated code for `unreachable`.</summary>
    public static Exception lean_internal_panic_unreachable() => new LeanPanicException("unreachable code has been reached");

    public static Exception lean_internal_panic(string msg)
    {
        // C: `fprintf(stderr, "INTERNAL PANIC: %s\n", msg); exit(1)`. The message goes to the
        // standard error of the current program; the hosts turn the exception into exit code 1.
        try
        {
            var b = System.Text.Encoding.UTF8.GetBytes("INTERNAL PANIC: " + msg + "\n");
            var err = LeanStdStreams.Stderr;
            lock (LeanStdStreams.s_writeLock) { err.Write(b, 0, b.Length); err.Flush(); }
        }
        catch { }
        return new LeanPanicException(msg);
    }

    public static Exception lean_internal_panic_out_of_memory() => lean_internal_panic("out of memory");
    public static Exception lean_internal_panic_overflow() => lean_internal_panic("integer overflow in runtime computation");
    public static Exception lean_internal_panic_rc_overflow() => lean_internal_panic("reference counter overflowed");

    public static void lean_set_exit_on_panic(bool flag)
    {
        var p = LeanContext.Proc;
        if (ReferenceEquals(p, LeanLogicalProcess.Root)) g_exit_on_panic = flag;
        else p.ExitOnPanic = flag;
    }

    public static void lean_set_panic_messages(bool flag)
    {
        var p = LeanContext.Proc;
        if (ReferenceEquals(p, LeanLogicalProcess.Root)) g_panic_messages = flag;
        else p.PanicMessages = flag;
    }

    /// <summary>Hook used to report panics (can be replaced by the host, e.g. to capture stderr).</summary>
    public static Action<string> PanicHandler = msg =>
    {
        // `std::cerr` of the current (logical) process
        LeanStdStreams.WriteProcessStderr(msg + "\n");
    };

    static delegate*<Obj, Obj> s_ioEprintln;

    // `panic_eprintln`: unless the process is about to die, panics go through Lean's `IO.eprintln`
    // so that redirected/isolated standard streams (e.g. `#guard_msgs`) see them.
    static void PanicEprintln(string msg, bool force_stderr)
    {
        if (!force_stderr && !ExitOnPanic)
        {
            if (s_ioEprintln == null && LeanExports.TryGet("lean_io_eprintln", out var p))
                s_ioEprintln = (delegate*<Obj, Obj>)p;
            if (s_ioEprintln != null)
            {
                try
                {
                    lean_dec(s_ioEprintln(lean_mk_string(msg)));
                    return;
                }
                catch (Exception) { }
            }
        }
        PanicHandler(msg);
    }

    public static void lean_panic(string msg, bool force_stderr = false)
    {
        if (PanicMessages || force_stderr)
            PanicEprintln(msg, force_stderr);
        if (ExitOnPanic)
            throw new LeanExitException(1);
    }

    public static Obj lean_panic_fn(Obj default_val, Obj msg)
    {
        lean_panic(lean_string_to_net(msg));
        lean_dec(msg);
        return default_val;
    }

    public static Obj lean_panic_fn_borrowed(Obj default_val, Obj msg)
    {
        lean_inc(default_val);
        return lean_panic_fn(default_val, msg);
    }

    // ------------------------------------------------------------------
    // Strings (object level; the string library lives in Runtime/String*.cs)

    public static Obj lean_alloc_string(ulong size, ulong capacity, ulong len)
    {
        return new StrObj { m_tag = LeanString, m_data = new byte[Math.Max(capacity, 1)], m_size = (long)size, m_length = (long)len };
    }

    /// <summary>Create a Lean string from UTF-8 bytes (without NUL) with known code point count.</summary>
    public static Obj lean_mk_string_unchecked(ReadOnlySpan<byte> s, ulong sz, ulong len)
    {
        var data = new byte[sz + 1];
        s.Slice(0, (int)sz).CopyTo(data);
        return new StrObj { m_tag = LeanString, m_data = data, m_size = (long)sz + 1, m_length = (long)len };
    }

    public static Obj lean_mk_string_unchecked(byte[] s, ulong sz, ulong len) => lean_mk_string_unchecked(new ReadOnlySpan<byte>(s), sz, len);

    /// <summary>Create a Lean string from (possibly invalid) UTF-8 bytes; invalid sequences are replaced by U+FFFD.</summary>
    public static Obj lean_mk_string_from_bytes(ReadOnlySpan<byte> s) => lean_mk_string_from_bytes_lossy(s);

    public static Obj lean_mk_string_from_bytes_unchecked(ReadOnlySpan<byte> s) =>
        lean_mk_string_unchecked(s, (ulong)s.Length, (ulong)Utf8Util.CountCodePoints(s));

    /// <summary>Create a Lean string from a .NET string.</summary>
    public static Obj lean_mk_string(string s)
    {
        s ??= "";
        int n = Encoding.UTF8.GetByteCount(s);
        var data = new byte[n + 1];
        Encoding.UTF8.GetBytes(s, 0, s.Length, data, 0);
        long len = 0;
        for (int i = 0; i < s.Length; i++)
        {
            if (char.IsHighSurrogate(s[i]) && i + 1 < s.Length && char.IsLowSurrogate(s[i + 1])) i++;
            len++;
        }
        return new StrObj { m_tag = LeanString, m_data = data, m_size = n + 1, m_length = len };
    }

    public static Obj lean_mk_ascii_string_unchecked(string s) => lean_mk_string(s);

    /// <summary>Convert a Lean string to a .NET string.</summary>
    public static string lean_string_to_net(Obj o)
    {
        var s = Unsafe.As<StrObj>(o);
        return Encoding.UTF8.GetString(s.m_data, 0, (int)(s.m_size - 1));
    }

    /// <summary>The UTF-8 bytes of a Lean string (without the terminating NUL).</summary>
    public static ReadOnlySpan<byte> lean_string_span(Obj o)
    {
        var s = Unsafe.As<StrObj>(o);
        return new ReadOnlySpan<byte>(s.m_data, 0, (int)(s.m_size - 1));
    }

    /// <summary>Raw buffer of a Lean string (NUL terminated; capacity may exceed size).</summary>
    public static byte[] lean_string_cstr(Obj o) => Unsafe.As<StrObj>(o).m_data;
    public static ulong lean_string_size(Obj o) => (ulong)Unsafe.As<StrObj>(o).m_size;
    public static ulong lean_string_len(Obj o) => (ulong)Unsafe.As<StrObj>(o).m_length;
    public static ulong lean_string_capacity(Obj o) => (ulong)Unsafe.As<StrObj>(o).m_data.Length;

    // ------------------------------------------------------------------
    // Arrays (object level; the array library lives in Runtime/Array*.cs)

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_alloc_array(ulong size, ulong capacity)
    {
        return new ArrayObj { m_tag = LeanArray, m_data = capacity == 0 ? Array.Empty<Obj>() : new Obj[capacity], m_size = (long)size };
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong lean_array_size(Obj o) => (ulong)Unsafe.As<ArrayObj>(o).m_size;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong lean_array_capacity(Obj o) => (ulong)Unsafe.As<ArrayObj>(o).m_data.Length;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj[] lean_array_cptr(Obj o) => Unsafe.As<ArrayObj>(o).m_data;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_array_set_size(Obj o, ulong sz) => Unsafe.As<ArrayObj>(o).m_size = (long)sz;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_array_get_core(Obj o, ulong i) => Unsafe.As<ArrayObj>(o).m_data[i];
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void lean_array_set_core(Obj o, ulong i, Obj v) => Unsafe.As<ArrayObj>(o).m_data[i] = v;
    public static Obj lean_mk_empty_array() => lean_alloc_array(0, 0);

    /// <summary>Build a Lean array from managed objects (takes ownership of the elements).</summary>
    public static Obj MkArray(IReadOnlyList<Obj> xs)
    {
        var a = lean_alloc_array((ulong)xs.Count, (ulong)xs.Count);
        var d = Unsafe.As<ArrayObj>(a).m_data;
        for (int i = 0; i < xs.Count; i++) d[i] = xs[i];
        return a;
    }

    // Scalar arrays (object level)

    public static Obj lean_alloc_sarray(uint elem_size, ulong size, ulong capacity)
    {
        return new SArrayObj
        {
            m_tag = LeanScalarArray,
            m_other = (byte)elem_size,
            m_data = new byte[checked(elem_size * capacity)],
            m_size = (long)size,
            m_capacity = (long)capacity,
        };
    }

    public static uint lean_sarray_elem_size(Obj o) => (uint)(o.m_other & ~LEAN_LINEAR_MARK_MASK);
    public static ulong lean_sarray_size(Obj o) => (ulong)Unsafe.As<SArrayObj>(o).m_size;
    public static ulong lean_sarray_capacity(Obj o) => (ulong)Unsafe.As<SArrayObj>(o).m_capacity;
    public static byte[] lean_sarray_cptr(Obj o) => Unsafe.As<SArrayObj>(o).m_data;
    public static void lean_sarray_set_size(Obj o, ulong sz) => Unsafe.As<SArrayObj>(o).m_size = (long)sz;

    /// <summary>Create a `ByteArray` holding a copy of `data`.</summary>
    public static Obj MkByteArray(ReadOnlySpan<byte> data)
    {
        var r = lean_alloc_sarray(1, (ulong)data.Length, (ulong)data.Length);
        data.CopyTo(Unsafe.As<SArrayObj>(r).m_data);
        return r;
    }

    public static ReadOnlySpan<byte> ByteArraySpan(Obj o)
    {
        var a = Unsafe.As<SArrayObj>(o);
        return new ReadOnlySpan<byte>(a.m_data, 0, (int)a.m_size);
    }

    // ------------------------------------------------------------------
    // Natural numbers (object level; arithmetic lives in Runtime/Nat*.cs)

    public static Obj lean_alloc_mpz(BigInteger v) => CountHeartbeat(new MpzObj { m_tag = LeanMPZ, m_value = v });

    /// <summary>Normalize a big integer to a Lean `Nat`/`Int` object (boxing small values). For `Nat`, `v` must be non-negative.</summary>
    public static Obj lean_big_to_nat(BigInteger v)
    {
        if (v.Sign >= 0 && v <= LEAN_MAX_SMALL_NAT) return lean_box((ulong)v);
        return lean_alloc_mpz(v);
    }

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_unsigned_to_nat(uint n) => lean_box(n);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_usize_to_nat(ulong n) => n <= LEAN_MAX_SMALL_NAT ? lean_box(n) : lean_alloc_mpz(n);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj lean_uint64_to_nat(ulong n) => n <= LEAN_MAX_SMALL_NAT ? lean_box(n) : lean_alloc_mpz(n);

    public static Obj lean_cstr_to_nat(string s) => lean_big_to_nat(BigInteger.Parse(s, System.Globalization.CultureInfo.InvariantCulture));

    /// <summary>Value of a `Nat` object as a big integer.</summary>
    public static BigInteger lean_nat_to_big(Obj o) =>
        o.m_tag == LeanBoxTag ? new BigInteger(Unsafe.As<Box>(o).m_value) : Unsafe.As<MpzObj>(o).m_value;

    // ------------------------------------------------------------------
    // Common inductive values

    public static Obj lean_mk_option_none() => lean_box(0);

    public static Obj lean_mk_option_some(Obj v)
    {
        var r = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(r, 0, v);
        return r;
    }

    public static Obj lean_mk_pair(Obj a, Obj b)
    {
        var r = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(r, 0, a);
        lean_ctor_set(r, 1, b);
        return r;
    }

    public static Obj lean_mk_list_cons(Obj head, Obj tail)
    {
        var r = lean_alloc_ctor(1, 2, 0);
        lean_ctor_set(r, 0, head);
        lean_ctor_set(r, 1, tail);
        return r;
    }

    /// <summary>Build a Lean `List` from managed objects (takes ownership of the elements).</summary>
    public static Obj MkList(IReadOnlyList<Obj> xs)
    {
        Obj r = lean_box(0);
        for (int i = xs.Count - 1; i >= 0; i--) r = lean_mk_list_cons(xs[i], r);
        return r;
    }

    /// <summary>Elements of a Lean `List` (borrowed).</summary>
    public static List<Obj> ListToManaged(Obj l)
    {
        var r = new List<Obj>();
        while (!lean_is_scalar(l))
        {
            r.Add(lean_ctor_get(l, 0));
            l = lean_ctor_get(l, 1);
        }
        return r;
    }
}

/// <summary>UTF-8 helpers.</summary>
public static class Utf8Util
{
    public static bool IsValid(ReadOnlySpan<byte> s) => System.Text.Unicode.Utf8.IsValid(s);

    public static long CountCodePoints(ReadOnlySpan<byte> s)
    {
        long n = 0;
        foreach (byte b in s) if ((b & 0xC0) != 0x80) n++;
        return n;
    }
}

/// <summary>
/// Per-thread heartbeat counter (`lean_inc_heartbeat`, read by `IO.getNumHeartbeats`). As
/// natively it counts the allocations made with `lean_alloc_small_object`: constructor objects,
/// thunks, refs, external objects, big-number objects, tasks (2: object and implementation) and
/// promises (3). Closures, arrays, scalar arrays and strings are allocated with
/// `lean_alloc_object` and do not count. The kernel's `check_heartbeat` has its own counter
/// (`KernelLimits`).
/// </summary>
public static class LeanHeartbeats
{
    [ThreadStatic] internal static ulong t_count;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Increment() => t_count++;
    public static void Add(ulong n) => t_count += n;
    public static ulong Get() => t_count;
    public static void Set(ulong n) => t_count = n;
}

public static unsafe partial class LeanRt
{
    public static void lean_inc_heartbeat() => LeanHeartbeats.t_count++;

    /// <summary>`lean_alloc_external`.</summary>
    public static Obj lean_alloc_external(ExternalClass cls, object data) =>
        CountHeartbeat(new ExternalObj { m_tag = LeanExternal, m_class = cls, m_data = data });

    /// <summary>Counts one heartbeat for a newly allocated small object.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    internal static Obj CountHeartbeat(Obj o)
    {
        LeanHeartbeats.t_count++;
        return o;
    }

    public static object lean_get_external_data(Obj o) => Unsafe.As<ExternalObj>(o).m_data;
    public static ExternalClass lean_get_external_class(Obj o) => Unsafe.As<ExternalObj>(o).m_class;
    public static ExternalClass lean_register_external_class(Action<object> finalize, Action<object, Obj> foreach_) =>
        new ExternalClass(finalize, foreach_);

    /// <summary>Pointer equality as in C: boxed scalars are equal iff their values are.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool lean_ptr_eq(Obj a, Obj b) =>
        ReferenceEquals(a, b) || (a.m_tag == LeanBoxTag && b.m_tag == LeanBoxTag && Unsafe.As<Box>(a).m_value == Unsafe.As<Box>(b).m_value);

    /// <summary>Used by the generated code to convert `uint8` results of externs (which may be implemented as `bool` or `byte`).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_u8(byte b) => b;
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static byte lean_u8(bool b) => b ? (byte)1 : (byte)0;
}
