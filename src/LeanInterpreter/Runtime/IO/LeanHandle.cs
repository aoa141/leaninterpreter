// Managed counterpart of the `FILE*` wrapped by `IO.FS.Handle` in runtime/io.cpp.
//
// A handle is either a file (`FileStream`), an arbitrary stream (e.g. a pipe to a child process),
// or one of the standard streams. Standard stream handles do not own a stream: every operation
// resolves the current stream through `LeanStdStreams`, so hosts can redirect them at any time
// (process-wide through `LeanIO.Stdout` etc., or per logical call context through
// `LeanStdStreams.Redirect`).

using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

/// <summary>
/// The standard streams used by the Lean-level `IO.getStdout` etc. By default these are the
/// process-level streams of `LeanIO`; `Redirect` overrides them for the current logical call
/// context (the override flows to tasks and threads started from that context), which is used
/// for running Lean programs "in-process" as child processes.
/// </summary>
public static class LeanStdStreams
{
    internal static readonly object s_writeLock = new();

    public static Stream Stdin => LeanContext.Current?.In ?? LeanIO.Stdin;
    public static Stream Stdout => LeanContext.Current?.Out ?? LeanIO.Stdout;
    public static Stream Stderr => LeanContext.Current?.Err ?? LeanIO.Stderr;

    /// <summary>
    /// Override the standard streams for the current logical call context (null arguments keep the
    /// current stream). Dispose the result to restore the previous streams.
    /// </summary>
    public static IDisposable Redirect(Stream stdin, Stream stdout, Stream stderr)
    {
        var prev = LeanContext.Current;
        LeanContext.Current = new LeanCallContext(stdin ?? prev?.In, stdout ?? prev?.Out, stderr ?? prev?.Err, prev?.Proc);
        return new Restore(prev);
    }

    sealed class Restore : IDisposable
    {
        readonly LeanCallContext m_prev;
        bool m_done;
        public Restore(LeanCallContext prev) { m_prev = prev; }
        public void Dispose()
        {
            if (m_done) return;
            m_done = true;
            LeanContext.Current = m_prev;
        }
    }

    /// <summary>Whether `s` is one of the console streams of the .NET runtime.</summary>
    public static bool IsConsoleStream(Stream s) =>
        s != null && (s.GetType().FullName ?? "").Contains("ConsoleStream", StringComparison.Ordinal);

    /// <summary>Write directly to the current stderr stream (like `std::cerr` in the C runtime).</summary>
    public static void WriteProcessStderr(string s)
    {
        var b = System.Text.Encoding.UTF8.GetBytes(s);
        try
        {
            lock (s_writeLock)
            {
                var st = Stderr;
                st.Write(b, 0, b.Length);
                st.Flush();
            }
        }
        catch (Exception) { }
    }
}

/// <summary>`IO.FS.Handle` payload.</summary>
public sealed class LeanHandle
{
    public enum StdKind : byte { None, Stdin, Stdout, Stderr }

    readonly StdKind m_std;
    Stream m_stream;
    readonly string m_lockKey;
    readonly bool m_append;
    readonly bool m_ownsStream;
    readonly object m_lock = new();
    // Read buffer for non-seekable streams (pipes, console); seekable streams are buffered by FileStream.
    byte[] m_rbuf;
    int m_rpos, m_rlen;
    Stream m_rbufOwner;
    bool m_closed;
    internal int m_lockMode; // 0 = none, 1 = shared, 2 = exclusive (protected by FileLocks.s_lock)

    public static readonly ExternalClass Class = new ExternalClass(o => ((LeanHandle)o).Close(), null);

    public static readonly LeanHandle StdinHandle = new LeanHandle(StdKind.Stdin);
    public static readonly LeanHandle StdoutHandle = new LeanHandle(StdKind.Stdout);
    public static readonly LeanHandle StderrHandle = new LeanHandle(StdKind.Stderr);

    LeanHandle(StdKind k)
    {
        m_std = k;
        m_lockKey = "<std:" + k + ">";
    }

    /// <summary>A handle for `stream`. `path` (optional) identifies the file for `Handle.lock`.</summary>
    public LeanHandle(Stream stream, string path = null, bool append = false, bool ownsStream = true)
    {
        m_std = StdKind.None;
        m_stream = stream;
        m_append = append;
        m_ownsStream = ownsStream;
        m_lockKey = path != null ? NormalizeLockKey(path) : "<stream:" + RuntimeHelpers.GetHashCode(this) + ">";
    }

    static string NormalizeLockKey(string path)
    {
        try
        {
            var full = Path.GetFullPath(path);
            return OperatingSystem.IsWindows() || OperatingSystem.IsMacOS() ? full.ToLowerInvariant() : full;
        }
        catch (Exception) { return path; }
    }

    public StdKind Std => m_std;
    public bool IsClosed => m_closed;
    internal string LockKey => m_lockKey;

    /// <summary>The underlying stream (resolved dynamically for standard streams).</summary>
    public Stream Stream => m_std switch
    {
        StdKind.Stdin => LeanStdStreams.Stdin,
        StdKind.Stdout => LeanStdStreams.Stdout,
        StdKind.Stderr => LeanStdStreams.Stderr,
        _ => m_stream,
    };

    /// <summary>Wrap as a Lean `IO.FS.Handle` object.</summary>
    public static Obj Wrap(LeanHandle h) => LeanRt.lean_alloc_external(Class, h);

    /// <summary>The handle of an `IO.FS.Handle` object (borrowed).</summary>
    public static LeanHandle Of(Obj o) => (LeanHandle)Unsafe.As<ExternalObj>(o).m_data;

    Stream Checked()
    {
        if (m_closed) throw new ObjectDisposedException("handle");
        return Stream;
    }

    // The standard input handle is one object for all programs running in this OS process, but
    // each of them has its own stream (the logical call context). Reading must not share a
    // lock or a read buffer between them: a child blocked in `getLine` on its own stdin would
    // block every other program reading its stdin. Each stream gets its own reader.
    static readonly ConditionalWeakTable<Stream, LeanHandle> s_stdReaders = new();

    LeanHandle StdReader() => s_stdReaders.GetValue(Stream, static s => new LeanHandle(s, null, false, ownsStream: false));

    /// <summary>Read up to `n` bytes; blocks until `n` bytes are available or EOF (like `fread`).</summary>
    public int Read(byte[] dst, int n)
    {
        if (m_std != StdKind.None) return StdReader().Read(dst, n);
        lock (m_lock)
        {
            var s = Checked();
            if (!s.CanRead) throw new LeanErrnoException(LeanErrno.EBADF);
            int got = 0;
            if (!s.CanSeek)
            {
                if (!ReferenceEquals(m_rbufOwner, s)) { m_rpos = m_rlen = 0; m_rbufOwner = s; }
                if (m_rpos < m_rlen)
                {
                    int k = Math.Min(n, m_rlen - m_rpos);
                    Buffer.BlockCopy(m_rbuf, m_rpos, dst, 0, k);
                    m_rpos += k;
                    got = k;
                }
            }
            while (got < n)
            {
                int k = s.Read(dst, got, n - got);
                if (k <= 0) break;
                got += k;
            }
            return got;
        }
    }

    int ReadByteBuffered(Stream s)
    {
        if (s.CanSeek) return s.ReadByte();
        if (!ReferenceEquals(m_rbufOwner, s)) { m_rpos = m_rlen = 0; m_rbufOwner = s; }
        if (m_rpos >= m_rlen)
        {
            m_rbuf ??= new byte[8192];
            int k = s.Read(m_rbuf, 0, m_rbuf.Length);
            if (k <= 0) return -1;
            m_rpos = 0; m_rlen = k;
        }
        return m_rbuf[m_rpos++];
    }

    /// <summary>Read a line including the terminating `\n` (empty at EOF).</summary>
    public byte[] GetLine()
    {
        if (m_std != StdKind.None) return StdReader().GetLine();
        lock (m_lock)
        {
            var s = Checked();
            if (!s.CanRead) throw new LeanErrnoException(LeanErrno.EBADF);
            var line = new MemoryStream();
            int c;
            while ((c = ReadByteBuffered(s)) >= 0)
            {
                line.WriteByte((byte)c);
                if (c == '\n') break;
            }
            return line.ToArray();
        }
    }

    public void Write(ReadOnlySpan<byte> data)
    {
        if (m_std == StdKind.Stdout || m_std == StdKind.Stderr)
        {
            lock (LeanStdStreams.s_writeLock)
            {
                var s = Stream;
                s.Write(data);
                s.Flush();
            }
            return;
        }
        lock (m_lock)
        {
            var s = Checked();
            if (!s.CanWrite) throw new LeanErrnoException(LeanErrno.EBADF);
            if (m_append && s.CanSeek) s.Seek(0, SeekOrigin.End);
            s.Write(data);
        }
    }

    public void Flush()
    {
        lock (m_lock)
        {
            var s = Checked();
            if (s.CanWrite) s.Flush();
        }
    }

    public void Rewind()
    {
        lock (m_lock)
        {
            var s = Checked();
            if (!s.CanSeek) throw new LeanErrnoException(LeanErrno.ESPIPE);
            s.Seek(0, SeekOrigin.Begin);
            m_rpos = m_rlen = 0;
        }
    }

    public void Truncate()
    {
        lock (m_lock)
        {
            var s = Checked();
            if (!s.CanSeek || !s.CanWrite) throw new LeanErrnoException(LeanErrno.EINVAL);
            s.SetLength(s.Position);
        }
    }

    public bool IsTty()
    {
        try
        {
            switch (m_std)
            {
                case StdKind.Stdin: return LeanStdStreams.IsConsoleStream(Stream) && !Console.IsInputRedirected;
                case StdKind.Stdout: return LeanStdStreams.IsConsoleStream(Stream) && !Console.IsOutputRedirected;
                case StdKind.Stderr: return LeanStdStreams.IsConsoleStream(Stream) && !Console.IsErrorRedirected;
                default: return false;
            }
        }
        catch (Exception) { return false; }
    }

    /// <summary>Close the handle (the finalizer of `IO.FS.Handle`). Errors are ignored.</summary>
    public void Close()
    {
        FileLocks.Release(this);
        lock (m_lock)
        {
            if (m_closed || m_std != StdKind.None) return;
            m_closed = true;
            if (m_ownsStream)
            {
                try { m_stream.Dispose(); } catch (Exception) { }
            }
        }
    }
}

/// <summary>
/// Emulation of `flock` for `Handle.lock`/`tryLock`/`unlock`: advisory reader/writer locks keyed by
/// the file's full path. Locks are owned by handles (as `flock` locks are owned by open file
/// descriptions) and are released when the handle is closed. Only effective within this process.
/// </summary>
static class FileLocks
{
    sealed class State
    {
        public int Shared;
        public LeanHandle Exclusive;
    }

    static readonly object s_lock = new();
    static readonly Dictionary<string, State> s_table = new();

    static State Get(string key)
    {
        if (!s_table.TryGetValue(key, out var st)) { st = new State(); s_table[key] = st; }
        return st;
    }

    static void ReleaseCore(LeanHandle h)
    {
        if (h.m_lockMode == 0) return;
        if (s_table.TryGetValue(h.LockKey, out var st))
        {
            if (h.m_lockMode == 1) st.Shared--;
            else if (ReferenceEquals(st.Exclusive, h)) st.Exclusive = null;
            if (st.Shared == 0 && st.Exclusive == null) s_table.Remove(h.LockKey);
        }
        h.m_lockMode = 0;
        Monitor.PulseAll(s_lock);
    }

    static bool TryAcquireCore(LeanHandle h, bool exclusive)
    {
        var st = Get(h.LockKey);
        if (exclusive)
        {
            int othersShared = st.Shared - (h.m_lockMode == 1 ? 1 : 0);
            if ((st.Exclusive == null || ReferenceEquals(st.Exclusive, h)) && othersShared == 0)
            {
                if (h.m_lockMode == 1) st.Shared--;
                st.Exclusive = h;
                h.m_lockMode = 2;
                return true;
            }
            return false;
        }
        else
        {
            if (st.Exclusive == null || ReferenceEquals(st.Exclusive, h))
            {
                if (h.m_lockMode == 2) st.Exclusive = null;
                if (h.m_lockMode != 1) st.Shared++;
                h.m_lockMode = 1;
                Monitor.PulseAll(s_lock);
                return true;
            }
            return false;
        }
    }

    public static void Lock(LeanHandle h, bool exclusive)
    {
        lock (s_lock)
        {
            if (TryAcquireCore(h, exclusive)) return;
            // `flock` lock conversion is not atomic: the old lock is released first.
            ReleaseCore(h);
            while (!TryAcquireCore(h, exclusive)) Monitor.Wait(s_lock);
        }
    }

    public static bool TryLock(LeanHandle h, bool exclusive)
    {
        lock (s_lock) return TryAcquireCore(h, exclusive);
    }

    public static void Release(LeanHandle h)
    {
        lock (s_lock) ReleaseCore(h);
    }
}
