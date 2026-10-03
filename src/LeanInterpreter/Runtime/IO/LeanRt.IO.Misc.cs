// Port of the remaining externs of runtime/io.cpp, runtime/platform.cpp, runtime/object.cpp
// (runtime info, debugging helpers, `sorry`), library/time_task.cpp (`profileit`),
// util/ffi.cpp, library/dynlib.cpp and the C math functions used by `Float`/`Float32`.

using System.Diagnostics;
using System.Globalization;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;

namespace LeanInterpreter.Runtime;

/// <summary>
/// Heartbeats (runtime/alloc.cpp): a per-thread counter that the C runtime increments on every
/// small allocation. LeanInterpreter increments it explicitly (see <see cref="Increment"/>) in hot
/// runtime paths.
/// </summary>

/// <summary>Cumulative profiling times (library/time_task.cpp).</summary>
public static class LeanProfiling
{
    // The cumulative times are kept per logical process (natively: per OS process).

    internal sealed class TimeTask
    {
        public string Category;
        public TimeTask Parent;
        public double Excluded;
    }

    [ThreadStatic] internal static TimeTask t_current;

    /// <summary>`report_profiling_time`.</summary>
    public static void ReportTime(string category, double seconds)
    {
        LeanContext.Proc.AddProfilingTime(category, seconds);
    }

    /// <summary>`exclude_profiling_time_from_current_task`.</summary>
    public static void ExcludeFromCurrentTask(double seconds)
    {
        var t = t_current;
        if (t != null) t.Excluded += seconds;
    }

    /// <summary>`has_no_block_profiling_task`.</summary>
    public static bool HasNoBlockProfilingTask() => t_current != null && t_current.Category != "blocked";

    /// <summary>`display_profiling_time`: C++ `setprecision(3)` formatting of a duration.</summary>
    public static string DisplayTime(double seconds) =>
        seconds < 1 ? FormatG(seconds * 1000, 3) + "ms" : FormatG(seconds, 3) + "s";

    /// <summary>C `%.{p}g` formatting.</summary>
    public static string FormatG(double v, int p)
    {
        if (double.IsNaN(v)) return "nan";
        if (double.IsInfinity(v)) return v > 0 ? "inf" : "-inf";
        if (v == 0) return "0";
        string e = v.ToString("E" + (p - 1), CultureInfo.InvariantCulture);
        int ei = e.IndexOf('E');
        int x = int.Parse(e.Substring(ei + 1), CultureInfo.InvariantCulture);
        if (x < p && x >= -4)
        {
            string f = v.ToString("F" + (p - 1 - x), CultureInfo.InvariantCulture);
            if (f.Contains('.')) f = f.TrimEnd('0').TrimEnd('.');
            return f;
        }
        string m = e.Substring(0, ei);
        if (m.Contains('.')) m = m.TrimEnd('0').TrimEnd('.');
        return m + "e" + (x < 0 ? "-" : "+") + Math.Abs(x).ToString("00", CultureInfo.InvariantCulture);
    }

    internal static string CumulativeReport()
    {
        var times = LeanContext.Proc.ProfilingTimes();
        if (times.Length == 0) return null;
        var sb = new StringBuilder("cumulative profiling times:\n");
        foreach (var kv in times) sb.Append('\t').Append(kv.Key).Append(' ').Append(DisplayTime(kv.Value)).Append('\n');
        return sb.ToString();
    }
}

public static unsafe partial class LeanRt
{
    // ------------------------------------------------------------------
    // Initialization flag

    static volatile bool g_io_initializing = true;

    /// <summary>
    /// Called by the `main` of every Lean program right before the program proper starts (as in
    /// the C `main` functions emitted by Lean). The per-process state that LeanInterpreter keeps per
    /// *logical* process is set up earlier, when the host enters the program
    /// (see <see cref="LeanProgramState.BeginProgram"/>).
    /// </summary>
    public static void lean_io_mark_end_initialization()
    {
        g_io_initializing = false;
        LeanContext.Proc.IoInitializing = false;
    }

    /* IO.initializing : BaseIO Bool */
    public static byte lean_io_initializing()
    {
        // per program; the OS process itself (module initialization by the host, stray threads)
        // uses the process-wide flag
        var p = LeanContext.Proc;
        bool v = ReferenceEquals(p, LeanLogicalProcess.Root) ? g_io_initializing : p.IoInitializing;
        return v ? (byte)1 : (byte)0;
    }

    // ------------------------------------------------------------------
    // Printing to Lean's stderr stream

    /// <summary>`io_eprintln` (takes ownership of `s`): print through Lean's `IO.eprintln`.</summary>
    internal static void IoEprintln(Obj s)
    {
        if (LeanExports.TryGet("lean_io_eprintln", out var f))
        {
            var r = ((delegate*<Obj, Obj>)f)(s);
            if (lean_io_result_is_error(r)) lean_io_result_show_error(r);
            lean_dec(r);
        }
        else
        {
            LeanStdStreams.WriteProcessStderr(lean_string_to_net(s) + "\n");
            lean_dec(s);
        }
    }

    /// <summary>`io_eprint` (kernel/trace.cpp, used by `tout`).</summary>
    internal static void IoEprint(Obj s)
    {
        if (LeanExports.TryGet("lean_io_eprint", out var f))
        {
            var r = ((delegate*<Obj, Obj>)f)(s);
            if (lean_io_result_is_error(r)) lean_io_result_show_error(r);
            lean_dec(r);
        }
        else
        {
            LeanStdStreams.WriteProcessStderr(lean_string_to_net(s));
            lean_dec(s);
        }
    }

    // ------------------------------------------------------------------
    // Time and randomness

    static readonly long s_ioTicksPerSec = Stopwatch.Frequency;

    static ulong IoMonoNanos()
    {
        long t = Stopwatch.GetTimestamp();
        long sec = t / s_ioTicksPerSec, rem = t % s_ioTicksPerSec;
        return (ulong)sec * 1_000_000_000UL + (ulong)(rem * 1_000_000_000L / s_ioTicksPerSec);
    }

    /* monoMsNow : BaseIO Nat */
    public static Obj lean_io_mono_ms_now() => lean_uint64_to_nat(IoMonoNanos() / 1_000_000UL);

    /* monoNanosNow : BaseIO Nat */
    public static Obj lean_io_mono_nanos_now() => lean_uint64_to_nat(IoMonoNanos());

    /* Std.Time.Timestamp.now : IO Timestamp */
    public static Obj lean_get_current_time()
    {
        long ns = (DateTime.UtcNow.Ticks - DateTime.UnixEpoch.Ticks) * 100;
        long secs = ns / 1_000_000_000L;
        long nano = ns % 1_000_000_000L;
        var ts = lean_alloc_ctor(0, 2, 0);
        lean_ctor_set(ts, 0, IoInt64ToInt(secs));
        lean_ctor_set(ts, 1, IoInt64ToInt(nano));
        return lean_io_result_mk_ok(ts);
    }

    /* Std.Time.Database.Windows.getNextTransition : @&String -> Int64 -> Bool -> IO (Option (Int64 × TimeZone)) */
    public static Obj lean_windows_get_next_transition(Obj timezone_str, ulong tm_obj, byte default_time)
    {
        if (!OperatingSystem.IsWindows())
            return lean_io_result_mk_error(LeanIOErrors.Mk("lean_mk_io_error_invalid_argument", (uint)LeanErrno.EINVAL,
                lean_mk_string("failed to get timezone, its windows only.")));
        // Natively this uses the ICU of Windows; here `TimeZoneInfo` (which knows the rules of
        // the Windows time zone database, not the full history of the IANA one).
        TimeZoneInfo tz;
        try { tz = TimeZoneInfo.FindSystemTimeZoneById(lean_string_to_net(timezone_str)); }
        catch (Exception) { tz = TimeZoneInfo.Utc; } // ICU: an unknown identifier is GMT
        try
        {
            DateTimeOffset at = default_time != 0 ? DateTimeOffset.UtcNow : DateTimeOffset.FromUnixTimeSeconds((long)tm_obj);
            long next = 0;
            if (default_time == 0)
            {
                long? n = WinNextTransition(tz, (long)tm_obj);
                if (n == null) return lean_io_result_mk_ok(lean_mk_option_none());
                next = n.Value;
            }
            bool isDst = tz.IsDaylightSavingTime(at);
            var offset = tz.GetUtcOffset(at);
            var ltz = lean_alloc_ctor(0, 3, 1);
            lean_ctor_set(ltz, 0, IoInt64ToInt((long)offset.TotalSeconds));
            lean_ctor_set(ltz, 1, lean_mk_string(isDst ? tz.DaylightName : tz.StandardName));
            lean_ctor_set(ltz, 2, lean_mk_string(WinZoneAbbreviation(tz, isDst, offset)));
            lean_ctor_set_uint8(ltz, 8 * 3, isDst ? (byte)1 : (byte)0);
            var pair = lean_alloc_ctor(0, 2, 0);
            lean_ctor_set(pair, 0, lean_box_uint64((ulong)next));
            lean_ctor_set(pair, 1, ltz);
            return lean_io_result_mk_ok(lean_mk_option_some(pair));
        }
        catch (Exception)
        {
            return lean_io_result_mk_error(LeanIOErrors.Mk("lean_mk_io_error_invalid_argument", (uint)LeanErrno.EINVAL,
                lean_mk_string("failed to get next transition")));
        }
    }

    const long WinLastTransitionSecs = 32503690800; // year 3000: where `getZoneRules` stops

    static (TimeSpan, bool) WinZoneState(TimeZoneInfo tz, long secs)
    {
        var t = DateTimeOffset.FromUnixTimeSeconds(secs);
        return (tz.GetUtcOffset(t), tz.IsDaylightSavingTime(t));
    }

    /// <summary>The first second after `secs` at which the offset or the daylight saving state of `tz` changes.</summary>
    static long? WinNextTransition(TimeZoneInfo tz, long secs)
    {
        if (tz.GetAdjustmentRules().Length == 0) return null;
        var state = WinZoneState(tz, secs);
        const long step = 7 * 86400;
        long lo = secs;
        while (lo <= WinLastTransitionSecs)
        {
            long hi = lo + step;
            if (WinZoneState(tz, hi) != state)
            {
                while (hi - lo > 1)
                {
                    long mid = lo + (hi - lo) / 2;
                    if (WinZoneState(tz, mid) != state) hi = mid; else lo = mid;
                }
                return hi;
            }
            lo = hi;
        }
        return null;
    }

    /// <summary>Short name of a zone as ICU prints it for `en_US`: an abbreviation for the zones of the US, `GMT+1` otherwise.</summary>
    static string WinZoneAbbreviation(TimeZoneInfo tz, bool isDst, TimeSpan offset)
    {
        string id = tz.Id;
        if (tz.HasIanaId && TimeZoneInfo.TryConvertIanaIdToWindowsId(id, out var win)) id = win;
        switch (id)
        {
            case "UTC": return "UTC";
            case "Eastern Standard Time": return isDst ? "EDT" : "EST";
            case "Central Standard Time": return isDst ? "CDT" : "CST";
            case "Mountain Standard Time": return isDst ? "MDT" : "MST";
            case "US Mountain Standard Time": return "MST";
            case "Pacific Standard Time": return isDst ? "PDT" : "PST";
            case "Alaskan Standard Time": return isDst ? "AKDT" : "AKST";
            case "Hawaiian Standard Time": return "HST";
        }
        if (offset == TimeSpan.Zero) return "GMT";
        var abs = offset.Duration();
        return "GMT" + (offset < TimeSpan.Zero ? "-" : "+") + abs.Hours + (abs.Minutes != 0 ? ":" + abs.Minutes.ToString("00") : "");
    }

    /* Std.Time.Database.Windows.getLocalTimeZoneIdentifierAt : Int64 → IO String */
    public static Obj lean_get_windows_local_timezone_id_at(ulong tm_obj)
    {
        if (!OperatingSystem.IsWindows())
            return lean_io_result_mk_error(LeanIOErrors.Mk("lean_mk_io_error_invalid_argument", (uint)LeanErrno.EINVAL,
                lean_mk_string("timezone retrieval is Windows-only")));
        // an IANA identifier, as ICU returns it
        string id = TimeZoneInfo.Local.Id;
        if (!TimeZoneInfo.Local.HasIanaId && TimeZoneInfo.TryConvertWindowsIdToIanaId(id, out var iana)) id = iana;
        return lean_io_result_mk_ok(lean_mk_string(id));
    }

    /* getRandomBytes (nBytes : USize) : IO ByteArray */
    public static Obj lean_io_get_random_bytes(ulong nbytes)
    {
        if (nbytes == 0) return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
        if (nbytes > int.MaxValue - 64) return LeanIOErrors.DecodeResult(LeanErrno.ENOMEM, null);
        var res = lean_alloc_sarray(1, 0, nbytes);
        RandomNumberGenerator.Fill(new Span<byte>(lean_sarray_cptr(res), 0, (int)nbytes));
        lean_sarray_set_size(res, nbytes);
        return lean_io_result_mk_ok(res);
    }

    // ------------------------------------------------------------------
    // Heartbeats

    /* getNumHeartbeats : BaseIO Nat */
    public static Obj lean_io_get_num_heartbeats() => lean_uint64_to_nat(LeanHeartbeats.Get());

    /* setNumHeartbeats (count : Nat) : BaseIO Unit */
    public static Obj lean_io_set_heartbeats(Obj count)
    {
        LeanHeartbeats.Set(IoUInt64OfNat(count));
        lean_dec(count);
        return lean_box(0);
    }

    // ------------------------------------------------------------------
    // Process exit

    static void IoFlushStd()
    {
        try { LeanStdStreams.Stdout.Flush(); } catch (Exception) { }
        try { LeanStdStreams.Stderr.Flush(); } catch (Exception) { }
    }

    /* IO.Process.exit : UInt8 → IO α. Throws `LeanExitException` so that hosts can catch it. */
    public static Obj lean_io_exit(byte code)
    {
        IoFlushStd();
        throw new LeanExitException(code);
    }

    /* IO.Process.forceExit : UInt8 → IO α */
    public static Obj lean_io_force_exit(byte code)
    {
        IoFlushStd();
        // Natively this ends the OS process without running finalizers. A program that shares
        // the OS process with its host (an in-process child, a program run by a test worker or
        // through `LeanProject`) must only end itself: its logical process is marked as exiting
        // (its tasks stop, threads blocked in task operations are released) and the calling
        // thread unwinds like for `IO.Process.exit`.
        var p = LeanContext.Proc;
        if (p.OwnsOsProcess) System.Environment.Exit(code);
        LeanTaskManager.RequestExit(code);
        throw new LeanExitException(code);
    }

    // ------------------------------------------------------------------
    // timeit / allocprof / profileit

    /* timeit {α : Type} (msg : @& String) (fn : IO α) : IO α */
    public static Obj lean_io_timeit(Obj msg, Obj fn)
    {
        long start = Stopwatch.GetTimestamp();
        Obj w = lean_apply_1(fn, lean_io_mk_world());
        double diff = Stopwatch.GetElapsedTime(start).TotalSeconds;
        string m = lean_string_to_net(msg);
        string s = diff < 1
            ? m + " " + LeanProfiling.FormatG(diff * 1000, 3) + "ms"
            : m + " " + LeanProfiling.FormatG(diff, 3) + "s";
        IoEprintln(lean_mk_string(s));
        return w;
    }

    /* allocprof {α : Type} (msg : @& String) (fn : IO α) : IO α */
    public static Obj lean_io_allocprof(Obj msg, Obj fn)
    {
        Obj res = lean_apply_1(fn, lean_io_mk_world());
        IoEprintln(lean_mk_string(lean_string_to_net(msg) + "\n" +
            "Allocation profiling data is not available, compile lean using `-D RUNTIME_STATS=ON`\n"));
        return res;
    }

    /// <summary>Display a `Lean.Name` like the C++ `operator<<(std::ostream&, name const&)`.</summary>
    internal static string IoNameToString(Obj n)
    {
        if (lean_is_scalar(n)) return "[anonymous]";
        var parts = new List<string>();
        while (!lean_is_scalar(n))
        {
            var v = lean_ctor_get(n, 1);
            if (lean_obj_tag(n) == 1)
            {
                var s = lean_string_to_net(v);
                parts.Add(s.Length == 0 ? "«»" : s);
            }
            else parts.Add(lean_nat_to_big(v).ToString(CultureInfo.InvariantCulture));
            n = lean_ctor_get(n, 0);
        }
        parts.Reverse();
        return string.Join(".", parts);
    }

    /* profileit {α : Type} (category : @& String) (opts : @& Options) (fn : Unit → α) (decl : Name) : α */
    public static Obj lean_profileit(Obj category, Obj opts, Obj fn, Obj decl)
    {
        lean_inc(opts);
        bool profiler = ((delegate*<Obj, byte>)LeanExports.Get("lean_get_profiler"))(opts) != 0;
        if (!profiler)
        {
            lean_dec(decl);
            return lean_apply_1(fn, lean_box(0));
        }
        lean_inc(opts);
        double threshold = ((delegate*<Obj, double>)LeanExports.Get("lean_get_profiler_threshold"))(opts);
        var task = new LeanProfiling.TimeTask { Category = lean_string_to_net(category), Parent = LeanProfiling.t_current };
        LeanProfiling.t_current = task;
        long start = Stopwatch.GetTimestamp();
        try
        {
            return lean_apply_1(fn, lean_box(0));
        }
        finally
        {
            double inclusive = Stopwatch.GetElapsedTime(start).TotalSeconds;
            double elapsed = inclusive - task.Excluded;
            LeanProfiling.t_current = task.Parent;
            LeanProfiling.ReportTime(task.Category, elapsed);
            if (task.Parent != null) task.Parent.Excluded += inclusive;
            if (elapsed >= threshold)
            {
                var sb = new StringBuilder(task.Category);
                if (!lean_is_scalar(decl)) sb.Append(" of ").Append(IoNameToString(decl));
                sb.Append(" took ").Append(LeanProfiling.DisplayTime(elapsed)).Append('\n');
                IoEprint(lean_mk_string(sb.ToString()));
            }
            lean_dec(decl);
        }
    }

    /* displayCumulativeProfilingTimes : BaseIO Unit */
    public static Obj lean_display_cumulative_profiling_times()
    {
        var s = LeanProfiling.CumulativeReport();
        if (s != null) LeanStdStreams.WriteProcessStderr(s);
        return lean_box(0);
    }

    // ------------------------------------------------------------------
    // Debugging helpers (runtime/object.cpp)

    /* dbgTrace {α : Type u} (message : String) (f : Unit → α) : α */
    public static Obj lean_dbg_trace(Obj s, Obj fn)
    {
        IoEprintln(s);
        return lean_apply_1(fn, lean_box(0));
    }

    /* dbgSleep {α : Type u} (ms : UInt32) (f : Unit → α) : α */
    public static Obj lean_dbg_sleep(uint ms, Obj fn)
    {
        Thread.Sleep(TimeSpan.FromMilliseconds(ms));
        return lean_apply_1(fn, lean_box(0));
    }

    /* dbgTraceIfShared {α : Type u} (s : @& String) (a : α) : α */
    public static Obj lean_dbg_trace_if_shared(Obj s, Obj a)
    {
        if (!lean_is_scalar(a) && !lean_is_exclusive(a))
            IoEprintln(lean_mk_string("shared RC " + lean_string_to_net(s)));
        return a;
    }

    /* dbgStackTrace {α : Type u} (f : Unit → α) : α */
    public static Obj lean_dbg_stack_trace(Obj fn)
    {
        var st = new StackTrace(1, false).ToString().TrimEnd('\r', '\n');
        foreach (var line in st.Split('\n'))
            IoEprintln(lean_mk_string(line.TrimEnd('\r')));
        return lean_apply_1(fn, lean_box(0));
    }

    /* sorryAx (α : Sort u) (synthetic : Bool) : α */
    public static Obj lean_sorry(byte synthetic) => throw lean_internal_panic("executed 'sorry'");

    /* Option.getOrBlock! [Nonempty α] : Option α → α */
    public static Obj lean_option_get_or_block(Obj o_opt)
    {
        if (!lean_is_scalar(o_opt))
        {
            var v = lean_ctor_get(o_opt, 0);
            lean_inc(v);
            lean_dec(o_opt);
            return v;
        }
        lean_panic("PANIC: Promise.result!: promise has been dropped without ever being resolved", true);
        // only reachable when using non-fatal panics
        Thread.Sleep(Timeout.Infinite);
        return lean_box(0);
    }

    // ------------------------------------------------------------------
    // Runtime / build information

    public const string LEAN_GITHASH = "77f336f7ae6a60419d3882e0d5ca7ac3a2155528";
    public const uint LEAN_VERSION_MAJOR = 4;
    public const uint LEAN_VERSION_MINOR = 36;
    public const uint LEAN_VERSION_PATCH = 0;
    public const byte LEAN_VERSION_IS_RELEASE = 0;
    public const string LEAN_SPECIAL_VERSION_DESC = "";
    public const string LEAN_MANUAL_ROOT = "";

    public static Obj lean_closure_max_args(Obj unit) => lean_unsigned_to_nat((uint)LEAN_CLOSURE_MAX_ARGS);
    public static Obj lean_max_small_nat(Obj unit) => lean_usize_to_nat(LEAN_MAX_SMALL_NAT);
    public static Obj lean_get_max_ctor_fields(Obj unit) => lean_box(LEAN_MAX_CTOR_FIELDS);
    public static Obj lean_get_max_ctor_scalars_size(Obj unit) => lean_box(LEAN_MAX_CTOR_SCALARS_SIZE);
    public static Obj lean_get_usize_size(Obj unit) => lean_box(8);
    public static Obj lean_get_max_ctor_tag(Obj unit) => lean_box(LeanMaxCtorTag);

    public static Obj lean_version_get_major(Obj unit) => lean_box(LEAN_VERSION_MAJOR);
    public static Obj lean_version_get_minor(Obj unit) => lean_box(LEAN_VERSION_MINOR);
    public static Obj lean_version_get_patch(Obj unit) => lean_box(LEAN_VERSION_PATCH);
    public static byte lean_version_get_is_release(Obj unit) => LEAN_VERSION_IS_RELEASE;
    public static Obj lean_version_get_special_desc(Obj unit) => lean_mk_string(LEAN_SPECIAL_VERSION_DESC);
    public static Obj lean_manual_get_root(Obj unit) => lean_mk_string(LEAN_MANUAL_ROOT);
    public static Obj lean_get_githash(Obj unit) => lean_mk_string(LEAN_GITHASH);

    // The managed Uv layer emulates the libuv 1.48 API surface that Lean uses.
    public static Obj lean_libuv_version(Obj unit) => lean_box((1UL << 16) | (48UL << 8));
    // Lean only reports this number (nothing in Lean calls into OpenSSL yet); we report the
    // OpenSSL 3.0.0 version number, which is what the native build links against API-wise.
    public static Obj lean_openssl_version(Obj unit) => lean_box(0x30000000UL);

    // util/ffi.cpp: flags for compiling/linking C code emitted by Lean (not used by LeanInterpreter).
    public static Obj lean_get_leanc_extra_flags(Obj unit) =>
        lean_mk_string(" -fstack-clash-protection -ffp-contract=off -fdata-sections -ffunction-sections -fvisibility=hidden");
    public static Obj lean_get_leanc_internal_flags(Obj unit) => lean_mk_string("");
    public static Obj lean_get_linker_flags(byte link_static) => lean_mk_string("");
    public static Obj lean_get_internal_linker_flags(Obj unit) => lean_mk_string("");

    public static Obj lean_system_platform_nbits(Obj unit) => lean_box((ulong)IntPtr.Size * 8);
    public static byte lean_system_platform_windows(Obj unit) => OperatingSystem.IsWindows() ? (byte)1 : (byte)0;
    public static byte lean_system_platform_osx(Obj unit) => OperatingSystem.IsMacOS() ? (byte)1 : (byte)0;
    public static byte lean_system_platform_linux(Obj unit) => OperatingSystem.IsLinux() ? (byte)1 : (byte)0;
    public static byte lean_system_platform_emscripten(Obj unit) => OperatingSystem.IsBrowser() || OperatingSystem.IsWasi() ? (byte)1 : (byte)0;

    static string s_ioPlatformTarget;

    /// <summary>The LLVM target triple of the host (`LEAN_PLATFORM_TARGET`).</summary>
    public static string LeanPlatformTarget
    {
        get
        {
            if (s_ioPlatformTarget != null) return s_ioPlatformTarget;
            string arch = RuntimeInformation.OSArchitecture switch
            {
                Architecture.X64 => "x86_64",
                Architecture.Arm64 => OperatingSystem.IsMacOS() ? "arm64" : "aarch64",
                Architecture.X86 => "i686",
                Architecture.Arm => "armv7",
                Architecture.Wasm => "wasm32",
                Architecture.RiscV64 => "riscv64",
                _ => RuntimeInformation.OSArchitecture.ToString().ToLowerInvariant(),
            };
            string t;
            if (OperatingSystem.IsMacOS())
            {
                // The triple contains the Darwin kernel version (`uname -r`), but .NET reports the
                // macOS version: map it (macOS 11..15 = Darwin 20..24, macOS 26 = Darwin 25).
                var parts = RuntimeInformation.OSDescription.Split(' ');
                string ver;
                if (parts.Length > 1 && parts[0] == "Darwin") ver = parts[1];
                else
                {
                    var v = System.Environment.OSVersion.Version;
                    int major = v.Major >= 26 ? v.Major - 1 : v.Major + 9;
                    ver = $"{major}.{Math.Max(v.Minor, 0)}.0";
                }
                t = arch + "-apple-darwin" + ver;
            }
            else if (OperatingSystem.IsWindows()) t = arch + "-w64-windows-gnu";
            else if (OperatingSystem.IsLinux()) t = arch + "-unknown-linux-gnu";
            else if (OperatingSystem.IsBrowser() || OperatingSystem.IsWasi()) t = "wasm32-unknown-emscripten";
            else t = arch + "-unknown-" + RuntimeInformation.OSDescription.Split(' ')[0].ToLowerInvariant();
            return s_ioPlatformTarget = t;
        }
        set => s_ioPlatformTarget = value;
    }

    public static Obj lean_system_platform_target(Obj unit) => lean_mk_string(LeanPlatformTarget);

    // ------------------------------------------------------------------
    // Dynamic libraries (library/dynlib.cpp): not supported.

    /* Dynlib.load : @& System.FilePath -> IO Dynlib */
    public static Obj lean_dynlib_load(Obj path) =>
        LeanIOErrors.UserErrorResult("error loading library, dynamic libraries are not supported by LeanInterpreter: " + lean_string_to_net(path));

    /* Dynlib.get? : (dynlib : @& Dynlib) -> @& String -> Option dynlib.Symbol */
    public static Obj lean_dynlib_get(Obj dynlib, Obj name) => lean_mk_option_none();

    /* Dynlib.Symbol.runAsInit : {Dynlib} -> Symbol -> IO Unit */
    public static Obj lean_dynlib_symbol_run_as_init(Obj dynlib, Obj sym) =>
        LeanIOErrors.UserErrorResult("dynamic libraries are not supported by LeanInterpreter");

    // ------------------------------------------------------------------
    // C math functions used by `Float` / `Float32`

    public static double acosh(double x) => Math.Acosh(x);
    public static double asinh(double x) => Math.Asinh(x);
    public static double atanh(double x) => Math.Atanh(x);
    public static double cosh(double x) => Math.Cosh(x);
    public static double sinh(double x) => Math.Sinh(x);
    public static double tanh(double x) => Math.Tanh(x);
    public static double atan2(double y, double x) => Math.Atan2(y, x);
    public static double exp2(double x) => double.Exp2(x);
    public static double log10(double x) => Math.Log10(x);
    public static double log2(double x) => Math.Log2(x);

    public static float acoshf(float x) => MathF.Acosh(x);
    public static float asinhf(float x) => MathF.Asinh(x);
    public static float atanhf(float x) => MathF.Atanh(x);
    public static float coshf(float x) => MathF.Cosh(x);
    public static float sinhf(float x) => MathF.Sinh(x);
    public static float tanhf(float x) => MathF.Tanh(x);
    public static float atan2f(float y, float x) => MathF.Atan2(y, x);
    public static float exp2f(float x) => float.Exp2(x);
    public static float log10f(float x) => MathF.Log10(x);
    public static float log2f(float x) => MathF.Log2(x);
}
