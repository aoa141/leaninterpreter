// Port of the error handling part of runtime/io.cpp (`decode_io_error`, `lean_crt_to_uv_err`,
// `decode_uv_error_impl`). `IO.Error` values are built by the Lean functions exported with
// `@[export lean_mk_io_error_*]` (see Init/System/IOError.lean).
//
// Errno values follow the host OS (Linux numbering by default, BSD numbering on macOS), since
// that is what the C runtime stores in `IO.Error` values.

using System.ComponentModel;

namespace LeanInterpreter.Runtime;

/// <summary>`errno` constants of the host platform (Linux numbering, macOS numbering on macOS).</summary>
public static class LeanErrno
{
    static readonly bool Mac = OperatingSystem.IsMacOS() || OperatingSystem.IsIOS() || OperatingSystem.IsFreeBSD();

    public const int EPERM = 1, ENOENT = 2, ESRCH = 3, EINTR = 4, EIO = 5, ENXIO = 6, E2BIG = 7,
        ENOEXEC = 8, EBADF = 9, ECHILD = 10, ENOMEM = 12, EACCES = 13, EFAULT = 14, EBUSY = 16,
        EEXIST = 17, EXDEV = 18, ENODEV = 19, ENOTDIR = 20, EISDIR = 21, EINVAL = 22, ENFILE = 23,
        EMFILE = 24, ENOTTY = 25, ETXTBSY = 26, EFBIG = 27, ENOSPC = 28, ESPIPE = 29, EROFS = 30,
        EMLINK = 31, EPIPE = 32, EDOM = 33, ERANGE = 34;

    public static readonly int EAGAIN = Mac ? 35 : 11;
    public static readonly int EWOULDBLOCK = EAGAIN;
    public static readonly int EDEADLK = Mac ? 11 : 35;
    public static readonly int ENAMETOOLONG = Mac ? 63 : 36;
    public static readonly int ENOLCK = Mac ? 77 : 37;
    public static readonly int ENOSYS = Mac ? 78 : 38;
    public static readonly int ENOTEMPTY = Mac ? 66 : 39;
    public static readonly int ELOOP = Mac ? 62 : 40;
    public static readonly int ENOTSUP = Mac ? 45 : 95;
    public static readonly int EADDRINUSE = Mac ? 48 : 98;
    public static readonly int EADDRNOTAVAIL = Mac ? 49 : 99;
    public static readonly int ENETDOWN = Mac ? 50 : 100;
    public static readonly int ENETUNREACH = Mac ? 51 : 101;
    public static readonly int ECONNABORTED = Mac ? 53 : 103;
    public static readonly int ECONNRESET = Mac ? 54 : 104;
    public static readonly int ENOBUFS = Mac ? 55 : 105;
    public static readonly int EISCONN = Mac ? 56 : 106;
    public static readonly int ENOTCONN = Mac ? 57 : 107;
    public static readonly int ETIMEDOUT = Mac ? 60 : 110;
    public static readonly int ECONNREFUSED = Mac ? 61 : 111;
    public static readonly int EHOSTUNREACH = Mac ? 65 : 113;
    public static readonly int EPROTO = Mac ? 100 : 71;
    public static readonly int EPROTONOSUPPORT = Mac ? 43 : 93;
    public static readonly int EPROTOTYPE = Mac ? 41 : 91;
    public static readonly int EAFNOSUPPORT = Mac ? 47 : 97;
    public static readonly int EMSGSIZE = Mac ? 40 : 90;
    public static readonly int ENOPROTOOPT = Mac ? 42 : 92;
    public static readonly int ENOTSOCK = Mac ? 38 : 88;
    public static readonly int EDESTADDRREQ = Mac ? 39 : 89;
    public static readonly int EILSEQ = Mac ? 92 : 84;
    public static readonly int ENODATA = Mac ? 96 : 61;
}

/// <summary>An I/O failure with a known `errno` value.</summary>
public sealed class LeanErrnoException : IOException
{
    public readonly int Errno;
    public LeanErrnoException(int errno, string msg = null) : base(msg ?? LeanIOErrors.StrError(errno)) { Errno = errno; }
}

/// <summary>Construction of `IO.Error` values (through the Lean exports) and error decoding.</summary>
public static unsafe class LeanIOErrors
{
    enum Kind
    {
        Interrupted, InvalidArgument, NoFileOrDirectory, PermissionDenied, ResourceExhausted,
        InappropriateType, NoSuchThing, AlreadyExists, HardwareFault, UnsatisfiedConstraints,
        IllegalOperation, ResourceVanished, ProtocolError, TimeExpired, ResourceBusy,
        UnsupportedOperation, OtherError,
    }

    // ------------------------------------------------------------------
    // Exported constructors (cached function pointers)

    static readonly Dictionary<string, nint> s_cache = new();

    static nint Fn(string name)
    {
        lock (s_cache)
        {
            if (s_cache.TryGetValue(name, out var f)) return f;
        }
        var g = LeanExports.Get(name);
        lock (s_cache) s_cache[name] = g;
        return g;
    }

    /// <summary>`lean_mk_io_error_*` without file name (takes ownership of `details`).</summary>
    public static Obj Mk(string export, uint errnum, Obj details) =>
        ((delegate*<uint, Obj, Obj>)Fn(export))(errnum, details);

    /// <summary>`lean_mk_io_error_*_file` (takes ownership of `fname` and `details`).</summary>
    public static Obj MkFile(string export, Obj fname, uint errnum, Obj details) =>
        ((delegate*<Obj, uint, Obj, Obj>)Fn(export))(fname, errnum, details);

    /// <summary>`IO.userError` (takes ownership of `msg`).</summary>
    public static Obj UserError(Obj msg) => ((delegate*<Obj, Obj>)Fn("lean_mk_io_user_error"))(msg);

    public static Obj UserError(string msg) => UserError(LeanRt.lean_mk_string(msg));

    /// <summary>`IO.Error.mkEofError ()`.</summary>
    public static Obj EofError() => ((delegate*<Obj, Obj>)Fn("lean_mk_io_error_eof"))(LeanRt.lean_box(0));

    /// <summary>`io_result_mk_error(msg)`: an `IO` result holding a user error.</summary>
    public static Obj UserErrorResult(string msg) => LeanRt.lean_io_result_mk_error(UserError(msg));

    /// <summary>`IO.Error.toString` (takes ownership of `err`).</summary>
    public static Obj ToString(Obj err) => ((delegate*<Obj, Obj>)Fn("lean_io_error_to_string"))(err);

    // ------------------------------------------------------------------
    // errno classification (the composition of `lean_crt_to_uv_err` and `decode_uv_error_impl`)

    static Kind Classify(int e)
    {
        if (e == LeanErrno.EINTR) return Kind.Interrupted;
        if (e == LeanErrno.ELOOP || e == LeanErrno.ENAMETOOLONG || e == LeanErrno.EDESTADDRREQ ||
            e == LeanErrno.EBADF || e == LeanErrno.EINVAL || e == LeanErrno.EILSEQ ||
            e == LeanErrno.ENOTCONN || e == LeanErrno.ENOTSOCK || e == LeanErrno.ENOEXEC ||
            e == LeanErrno.EDOM)
            return Kind.InvalidArgument;
        if (e == LeanErrno.ENOENT) return Kind.NoFileOrDirectory;
        if (e == LeanErrno.EACCES || e == LeanErrno.EROFS || e == LeanErrno.ECONNABORTED ||
            e == LeanErrno.EFBIG || e == LeanErrno.EPERM)
            return Kind.PermissionDenied;
        if (e == LeanErrno.EMFILE || e == LeanErrno.ENFILE || e == LeanErrno.ENOSPC ||
            e == LeanErrno.E2BIG || e == LeanErrno.EAGAIN || e == LeanErrno.EMLINK ||
            e == LeanErrno.EMSGSIZE || e == LeanErrno.ENOBUFS || e == LeanErrno.ENOMEM ||
            e == LeanErrno.ENOLCK)
            return Kind.ResourceExhausted;
        if (e == LeanErrno.EISDIR || e == LeanErrno.ENOTDIR) return Kind.InappropriateType;
        if (e == LeanErrno.ENXIO || e == LeanErrno.EHOSTUNREACH || e == LeanErrno.ENETUNREACH ||
            e == LeanErrno.ECONNREFUSED || e == LeanErrno.ENODATA || e == LeanErrno.ESRCH ||
            e == LeanErrno.ECHILD)
            return Kind.NoSuchThing;
        if (e == LeanErrno.EEXIST || e == LeanErrno.EISCONN) return Kind.AlreadyExists;
        if (e == LeanErrno.EIO) return Kind.HardwareFault;
        if (e == LeanErrno.ENOTEMPTY) return Kind.UnsatisfiedConstraints;
        if (e == LeanErrno.ENOTTY) return Kind.IllegalOperation;
        if (e == LeanErrno.ECONNRESET || e == LeanErrno.ENETDOWN || e == LeanErrno.EPIPE)
            return Kind.ResourceVanished;
        if (e == LeanErrno.EPROTO || e == LeanErrno.EPROTONOSUPPORT || e == LeanErrno.EPROTOTYPE)
            return Kind.ProtocolError;
        if (e == LeanErrno.ETIMEDOUT) return Kind.TimeExpired;
        if (e == LeanErrno.EADDRINUSE || e == LeanErrno.EBUSY || e == LeanErrno.ETXTBSY ||
            e == LeanErrno.EDEADLK)
            return Kind.ResourceBusy;
        if (e == LeanErrno.EADDRNOTAVAIL || e == LeanErrno.EAFNOSUPPORT || e == LeanErrno.ENODEV ||
            e == LeanErrno.ENOPROTOOPT || e == LeanErrno.ENOSYS || e == LeanErrno.ENOTSUP ||
            e == LeanErrno.ERANGE || e == LeanErrno.ESPIPE || e == LeanErrno.EXDEV)
            return Kind.UnsupportedOperation;
        return Kind.OtherError;
    }

    /// <summary>`uv_strerror` messages.</summary>
    public static string StrError(int e)
    {
        if (e == LeanErrno.EPERM) return "operation not permitted";
        if (e == LeanErrno.ENOENT) return "no such file or directory";
        if (e == LeanErrno.ESRCH || e == LeanErrno.ECHILD) return "no such process";
        if (e == LeanErrno.EINTR) return "interrupted system call";
        if (e == LeanErrno.EIO) return "i/o error";
        if (e == LeanErrno.ENXIO) return "no such device or address";
        if (e == LeanErrno.E2BIG) return "argument list too long";
        if (e == LeanErrno.ENOEXEC) return "exec format error";
        if (e == LeanErrno.EBADF) return "bad file descriptor";
        if (e == LeanErrno.EAGAIN) return "resource temporarily unavailable";
        if (e == LeanErrno.ENOMEM) return "not enough memory";
        if (e == LeanErrno.EACCES) return "permission denied";
        if (e == LeanErrno.EFAULT) return "bad address in system call argument";
        if (e == LeanErrno.EBUSY) return "resource busy or locked";
        if (e == LeanErrno.EEXIST) return "file already exists";
        if (e == LeanErrno.EXDEV) return "cross-device link not permitted";
        if (e == LeanErrno.ENODEV) return "no such device";
        if (e == LeanErrno.ENOTDIR) return "not a directory";
        if (e == LeanErrno.EISDIR) return "illegal operation on a directory";
        if (e == LeanErrno.EINVAL) return "invalid argument";
        if (e == LeanErrno.ENFILE) return "file table overflow";
        if (e == LeanErrno.EMFILE) return "too many open files";
        if (e == LeanErrno.ENOTTY) return "inappropriate ioctl for device";
        if (e == LeanErrno.ETXTBSY) return "text file is busy";
        if (e == LeanErrno.EFBIG) return "file too large";
        if (e == LeanErrno.ENOSPC) return "no space left on device";
        if (e == LeanErrno.ESPIPE) return "invalid seek";
        if (e == LeanErrno.EROFS) return "read-only file system";
        if (e == LeanErrno.EMLINK) return "too many links";
        if (e == LeanErrno.EPIPE) return "broken pipe";
        if (e == LeanErrno.EDOM) return "invalid argument";
        if (e == LeanErrno.ERANGE) return "result too large";
        if (e == LeanErrno.ENAMETOOLONG) return "name too long";
        if (e == LeanErrno.ENOSYS) return "function not implemented";
        if (e == LeanErrno.ENOTEMPTY) return "directory not empty";
        if (e == LeanErrno.ELOOP) return "too many symbolic links encountered";
        if (e == LeanErrno.ENOTSUP) return "operation not supported on socket";
        if (e == LeanErrno.ETIMEDOUT) return "connection timed out";
        if (e == LeanErrno.ECONNREFUSED) return "connection refused";
        if (e == LeanErrno.ECONNRESET) return "connection reset by peer";
        if (e == LeanErrno.EADDRINUSE) return "address already in use";
        if (e == LeanErrno.ENOBUFS) return "no buffer space available";
        if (e == LeanErrno.ENOLCK) return "resource temporarily unavailable";
        if (e == LeanErrno.EDEADLK) return "resource busy or locked";
        return $"Unknown system error {e}";
    }

    /// <summary>
    /// `lean_decode_io_error`: build an `IO.Error` from an `errno` value. `fname` is borrowed and may
    /// be null.
    /// </summary>
    public static Obj Decode(int errnum, Obj fname, string details = null)
    {
        Obj det = LeanRt.lean_mk_string(details ?? StrError(errnum));
        uint en = (uint)errnum;
        Obj F() { LeanRt.lean_inc(fname); return fname; }
        switch (Classify(errnum))
        {
            case Kind.Interrupted:
                return MkFile("lean_mk_io_error_interrupted", fname == null ? LeanRt.lean_mk_string("") : F(), en, det);
            case Kind.InvalidArgument:
                return fname == null ? Mk("lean_mk_io_error_invalid_argument", en, det)
                                     : MkFile("lean_mk_io_error_invalid_argument_file", F(), en, det);
            case Kind.NoFileOrDirectory:
                return MkFile("lean_mk_io_error_no_file_or_directory", fname == null ? LeanRt.lean_mk_string("") : F(), en, det);
            case Kind.PermissionDenied:
                return fname == null ? Mk("lean_mk_io_error_permission_denied", en, det)
                                     : MkFile("lean_mk_io_error_permission_denied_file", F(), en, det);
            case Kind.ResourceExhausted:
                return fname == null ? Mk("lean_mk_io_error_resource_exhausted", en, det)
                                     : MkFile("lean_mk_io_error_resource_exhausted_file", F(), en, det);
            case Kind.InappropriateType:
                return fname == null ? Mk("lean_mk_io_error_inappropriate_type", en, det)
                                     : MkFile("lean_mk_io_error_inappropriate_type_file", F(), en, det);
            case Kind.NoSuchThing:
                return fname == null ? Mk("lean_mk_io_error_no_such_thing", en, det)
                                     : MkFile("lean_mk_io_error_no_such_thing_file", F(), en, det);
            case Kind.AlreadyExists:
                return fname == null ? Mk("lean_mk_io_error_already_exists", en, det)
                                     : MkFile("lean_mk_io_error_already_exists_file", F(), en, det);
            case Kind.HardwareFault: return Mk("lean_mk_io_error_hardware_fault", en, det);
            case Kind.UnsatisfiedConstraints: return Mk("lean_mk_io_error_unsatisfied_constraints", en, det);
            case Kind.IllegalOperation: return Mk("lean_mk_io_error_illegal_operation", en, det);
            case Kind.ResourceVanished: return Mk("lean_mk_io_error_resource_vanished", en, det);
            case Kind.ProtocolError: return Mk("lean_mk_io_error_protocol_error", en, det);
            case Kind.TimeExpired: return Mk("lean_mk_io_error_time_expired", en, det);
            case Kind.ResourceBusy: return Mk("lean_mk_io_error_resource_busy", en, det);
            case Kind.UnsupportedOperation: return Mk("lean_mk_io_error_unsupported_operation", en, det);
            default: return Mk("lean_mk_io_error_other_error", en, det);
        }
    }

    /// <summary>An `IO` error result built from an `errno` value (`fname` borrowed, may be null).</summary>
    public static Obj DecodeResult(int errnum, Obj fname) => LeanRt.lean_io_result_mk_error(Decode(errnum, fname));

    // ------------------------------------------------------------------
    // .NET exceptions

    /// <summary>Best-effort `errno` for a .NET exception.</summary>
    public static int ErrnoOf(Exception e)
    {
        switch (e)
        {
            case LeanErrnoException le:
                return le.Errno;
            case FileNotFoundException:
            case DirectoryNotFoundException:
                return LeanErrno.ENOENT;
            case PathTooLongException:
                return LeanErrno.ENAMETOOLONG;
            case UnauthorizedAccessException ua:
                if (ua.InnerException is IOException inner && TryRawErrno(inner.HResult, out int ie)) return ie;
                return LeanErrno.EACCES;
            case EndOfStreamException:
                return LeanErrno.EIO;
            case ObjectDisposedException:
                return LeanErrno.EBADF;
            case NotSupportedException:
                return LeanErrno.EBADF;
            case OutOfMemoryException:
                return LeanErrno.ENOMEM;
            case Win32Exception w:
                if (!OperatingSystem.IsWindows() && w.NativeErrorCode > 0) return w.NativeErrorCode;
                return FromWin32(w.NativeErrorCode);
            case IOException io:
                if (TryRawErrno(io.HResult, out int en)) return en;
                if (OperatingSystem.IsWindows() && (io.HResult & 0xFFFF0000) == 0x80070000) return FromWin32(io.HResult & 0xFFFF);
                return LeanErrno.EIO;
            case ArgumentException:
                return LeanErrno.EINVAL;
            default:
                return LeanErrno.EIO;
        }
    }

    // On Unix, .NET stores the raw errno in `IOException.HResult`.
    static bool TryRawErrno(int hresult, out int errno)
    {
        errno = hresult;
        return !OperatingSystem.IsWindows() && hresult > 0 && hresult < 4096;
    }

    static int FromWin32(int code) => code switch
    {
        2 or 3 or 15 or 53 or 67 or 161 => LeanErrno.ENOENT,
        5 or 19 => LeanErrno.EACCES,
        32 or 33 => LeanErrno.EBUSY,
        80 or 183 => LeanErrno.EEXIST,
        112 or 39 => LeanErrno.ENOSPC,
        145 => LeanErrno.ENOTEMPTY,
        109 or 232 => LeanErrno.EPIPE,
        206 => LeanErrno.ENAMETOOLONG,
        87 or 123 => LeanErrno.EINVAL,
        8 or 14 => LeanErrno.ENOMEM,
        4 => LeanErrno.EMFILE,
        6 => LeanErrno.EBADF,
        17 => LeanErrno.EXDEV,
        193 => LeanErrno.ENOEXEC,
        _ => LeanErrno.EIO,
    };

    /// <summary>`IO.Error` for a .NET exception (`fname` borrowed, may be null).</summary>
    public static Obj FromException(Exception e, Obj fname)
    {
        int en = ErrnoOf(e);
        return Decode(en, fname);
    }

    public static Obj FromExceptionResult(Exception e, Obj fname) => LeanRt.lean_io_result_mk_error(FromException(e, fname));
}

public static unsafe partial class LeanRt
{
    /// <summary>`lean_decode_io_error` (`fname` borrowed, may be null).</summary>
    public static Obj lean_decode_io_error(int errnum, Obj fname) => LeanIOErrors.Decode(errnum, fname);

    /// <summary>`lean_decode_uv_error`: libuv error codes are negated `errno` values (Unix convention).</summary>
    public static Obj lean_decode_uv_error(int errnum, Obj fname) => LeanIOErrors.Decode(-errnum, fname);

    /// <summary>`lean_io_result_show_error` (borrowed): print `uncaught exception: msg` to stderr.</summary>
    public static void lean_io_result_show_error(Obj r)
    {
        Obj err = lean_io_result_get_error(r);
        lean_inc(err);
        Obj str = LeanIOErrors.ToString(err);
        LeanStdStreams.WriteProcessStderr("uncaught exception: " + lean_string_to_net(str) + "\n");
        lean_dec(str);
    }
}
