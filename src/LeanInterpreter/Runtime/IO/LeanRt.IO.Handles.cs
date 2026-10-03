// Port of the `IO.FS.Handle` primitives and standard streams of runtime/io.cpp.

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    // ------------------------------------------------------------------
    // Standard streams (`IO.getStdout` etc.). As in C, the current streams are thread local and
    // initialized from global streams built with `IO.FS.Stream.ofHandle` on the standard handles.

    static Obj s_ioStreamStdin, s_ioStreamStdout, s_ioStreamStderr;
    static readonly object s_ioStreamLock = new();
    [ThreadStatic] static Obj t_ioStreamStdin;
    [ThreadStatic] static Obj t_ioStreamStdout;
    [ThreadStatic] static Obj t_ioStreamStderr;

    static Obj IoStreamOfHandle(Obj h) =>
        ((delegate*<Obj, Obj>)LeanExports.Get("lean_stream_of_handle"))(h);

    static Obj IoGlobalStream(ref Obj cell, LeanHandle h)
    {
        var v = Volatile.Read(ref cell);
        if (v != null) return v;
        lock (s_ioStreamLock)
        {
            if (cell == null)
            {
                var s = IoStreamOfHandle(LeanHandle.Wrap(h));
                lean_mark_persistent(s);
                Volatile.Write(ref cell, s);
            }
            return cell;
        }
    }

    static Obj IoStdinCur() { if (t_ioStreamStdin == null) { var g = IoGlobalStream(ref s_ioStreamStdin, LeanHandle.StdinHandle); lean_inc(g); t_ioStreamStdin = g; } return t_ioStreamStdin; }
    static Obj IoStdoutCur() { if (t_ioStreamStdout == null) { var g = IoGlobalStream(ref s_ioStreamStdout, LeanHandle.StdoutHandle); lean_inc(g); t_ioStreamStdout = g; } return t_ioStreamStdout; }
    static Obj IoStderrCur() { if (t_ioStreamStderr == null) { var g = IoGlobalStream(ref s_ioStreamStderr, LeanHandle.StderrHandle); lean_inc(g); t_ioStreamStderr = g; } return t_ioStreamStderr; }

    /// <summary>
    /// Makes the current thread use the global standard streams again. Called by pooled worker
    /// threads between tasks: a task that was aborted by a .NET exception (panic, `IO.Process.exit`)
    /// inside `IO.setStdout`-style redirection (`withIsolatedStreams`) cannot restore the streams,
    /// and the stale stream would swallow the output of every later task run by that thread.
    /// </summary>
    internal static void IoResetThreadStreams()
    {
        var a = t_ioStreamStdin; var b = t_ioStreamStdout; var c = t_ioStreamStderr;
        if (a == null && b == null && c == null) return;
        t_ioStreamStdin = null; t_ioStreamStdout = null; t_ioStreamStderr = null;
        if (a != null) lean_dec(a);
        if (b != null) lean_dec(b);
        if (c != null) lean_dec(c);
    }

    /* getStdin : BaseIO FS.Stream */
    public static Obj lean_get_stdin() { var r = IoStdinCur(); lean_inc(r); return r; }
    /* getStdout : BaseIO FS.Stream */
    public static Obj lean_get_stdout() { var r = IoStdoutCur(); lean_inc(r); return r; }
    /* getStderr : BaseIO FS.Stream */
    public static Obj lean_get_stderr() { var r = IoStderrCur(); lean_inc(r); return r; }

    /* setStdin : FS.Stream -> BaseIO FS.Stream */
    public static Obj lean_get_set_stdin(Obj h) { var r = IoStdinCur(); t_ioStreamStdin = h; return r; }
    /* setStdout : FS.Stream -> BaseIO FS.Stream */
    public static Obj lean_get_set_stdout(Obj h) { var r = IoStdoutCur(); t_ioStreamStdout = h; return r; }
    /* setStderr : FS.Stream -> BaseIO FS.Stream */
    public static Obj lean_get_set_stderr(Obj h) { var r = IoStderrCur(); t_ioStreamStderr = h; return r; }

    // ------------------------------------------------------------------
    // Helpers

    /// <summary>Whether a Lean string contains a NUL byte (C functions reject those paths).</summary>
    internal static bool IoHasNul(Obj s) => lean_string_span(s).IndexOf((byte)0) >= 0;

    /// <summary>`mk_embedded_nul_error` (`str` borrowed).</summary>
    internal static Obj IoEmbeddedNulError(Obj str)
    {
        lean_inc(str);
        return lean_io_result_mk_error(LeanIOErrors.MkFile("lean_mk_io_error_invalid_argument_file", str,
            (uint)LeanErrno.EINVAL, lean_mk_string("string contains NUL bytes")));
    }

    internal static Obj IoOkUnit() => lean_io_result_mk_ok(lean_box(0));

    // ------------------------------------------------------------------
    // Handles

    /* Handle.mk (filename : @& String) (mode : FS.Mode) : IO Handle */
    public static Obj lean_io_prim_handle_mk(Obj filename, byte mode)
    {
        if (IoHasNul(filename)) return IoEmbeddedNulError(filename);
        string path = lean_string_to_net(filename);
        try
        {
            path = LeanContext.ResolvePath(path);
            if (Directory.Exists(path))
                return LeanIOErrors.DecodeResult(LeanErrno.EISDIR, filename);
            FileMode fm; FileAccess fa; bool append = false;
            switch (mode)
            {
                case 0: fm = FileMode.Open; fa = FileAccess.Read; break;            // read
                case 1: fm = FileMode.Create; fa = FileAccess.Write; break;         // write
                case 2: fm = FileMode.CreateNew; fa = FileAccess.Write; break;      // writeNew
                case 3: fm = FileMode.Open; fa = FileAccess.ReadWrite; break;       // readWrite
                default: fm = FileMode.OpenOrCreate; fa = FileAccess.Write; append = true; break; // append
            }
            var fs = new FileStream(path, fm, fa, FileShare.ReadWrite | FileShare.Delete, 4096, FileOptions.None);
            if (append) fs.Seek(0, SeekOrigin.End);
            return lean_io_result_mk_ok(LeanHandle.Wrap(new LeanHandle(fs, path, append)));
        }
        catch (Exception e)
        {
            return LeanIOErrors.FromExceptionResult(e, filename);
        }
    }

    /* Handle.lock : (@& Handle) → (exclusive : Bool) → IO Unit */
    public static Obj lean_io_prim_handle_lock(Obj h, byte x)
    {
        FileLocks.Lock(LeanHandle.Of(h), x != 0);
        return IoOkUnit();
    }

    /* Handle.tryLock : (@& Handle) → (exclusive : Bool) → IO Bool */
    public static Obj lean_io_prim_handle_try_lock(Obj h, byte x) =>
        lean_io_result_mk_ok(lean_box(FileLocks.TryLock(LeanHandle.Of(h), x != 0) ? 1UL : 0UL));

    /* Handle.unlock : (@& Handle) → IO Unit */
    public static Obj lean_io_prim_handle_unlock(Obj h)
    {
        FileLocks.Release(LeanHandle.Of(h));
        return IoOkUnit();
    }

    /* Handle.isTty : (@& Handle) → BaseIO Bool */
    public static byte lean_io_prim_handle_is_tty(Obj h) => LeanHandle.Of(h).IsTty() ? (byte)1 : (byte)0;

    /* Handle.flush : (@& Handle) → IO Unit */
    public static Obj lean_io_prim_handle_flush(Obj h)
    {
        try { LeanHandle.Of(h).Flush(); return IoOkUnit(); }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
    }

    /* Handle.rewind : (@& Handle) → IO Unit */
    public static Obj lean_io_prim_handle_rewind(Obj h)
    {
        try { LeanHandle.Of(h).Rewind(); return IoOkUnit(); }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
    }

    /* Handle.truncate : (@& Handle) → IO Unit */
    public static Obj lean_io_prim_handle_truncate(Obj h)
    {
        try { LeanHandle.Of(h).Truncate(); return IoOkUnit(); }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
    }

    /* Handle.read : (@& Handle) → USize → IO ByteArray */
    public static Obj lean_io_prim_handle_read(Obj h, ulong nbytes)
    {
        if (nbytes > int.MaxValue - 64)
            return LeanIOErrors.DecodeResult(LeanErrno.ENOMEM, null);
        var res = lean_alloc_sarray(1, 0, nbytes);
        if (nbytes == 0) return lean_io_result_mk_ok(res);
        try
        {
            int n = LeanHandle.Of(h).Read(lean_sarray_cptr(res), (int)nbytes);
            lean_sarray_set_size(res, (ulong)n);
            return lean_io_result_mk_ok(res);
        }
        catch (Exception e)
        {
            return LeanIOErrors.FromExceptionResult(e, null);
        }
    }

    /* Handle.write : (@& Handle) → (@& ByteArray) → IO Unit */
    public static Obj lean_io_prim_handle_write(Obj h, Obj buf)
    {
        try
        {
            LeanHandle.Of(h).Write(ByteArraySpan(buf));
            return IoOkUnit();
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
    }

    /* Handle.getLine : (@& Handle) → IO String */
    public static Obj lean_io_prim_handle_get_line(Obj h)
    {
        try
        {
            var line = LeanHandle.Of(h).GetLine();
            return lean_io_result_mk_ok(lean_mk_string_from_bytes(line));
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
    }

    /* Handle.putStr : (@& Handle) → (@& String) → IO Unit */
    public static Obj lean_io_prim_handle_put_str(Obj h, Obj s)
    {
        try
        {
            LeanHandle.Of(h).Write(lean_string_span(s));
            return IoOkUnit();
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
    }
}
