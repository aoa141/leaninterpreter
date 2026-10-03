// Child processes (`IO.Process.spawn` and friends) on top of System.Diagnostics.Process, plus a
// hook that lets hosts intercept spawning (e.g. to run `lean` in-process).

using System.Diagnostics;
using System.Text;

namespace LeanInterpreter.Runtime;

/// <summary>`IO.Process.Stdio`.</summary>
public enum LeanStdioMode : byte { Piped = 0, Inherit = 1, Null = 2 }

/// <summary>A decoded `IO.Process.SpawnArgs`.</summary>
public sealed class SpawnRequest
{
    public string Cmd { get; init; } = "";
    public IReadOnlyList<string> Args { get; init; } = Array.Empty<string>();
    /// <summary>Working directory of the child; null to inherit the current directory.</summary>
    public string Cwd { get; init; }
    /// <summary>Environment modifications in order; a null value removes the variable.</summary>
    public IReadOnlyList<KeyValuePair<string, string>> Env { get; init; } = Array.Empty<KeyValuePair<string, string>>();
    public bool InheritEnv { get; init; } = true;
    public bool SetSid { get; init; }
    public LeanStdioMode Stdin { get; init; } = LeanStdioMode.Inherit;
    public LeanStdioMode Stdout { get; init; } = LeanStdioMode.Inherit;
    public LeanStdioMode Stderr { get; init; } = LeanStdioMode.Inherit;

    /// <summary>File name of the command without directory and extension (e.g. `lean` for `/x/bin/lean.exe`).</summary>
    public string CommandName => Path.GetFileNameWithoutExtension(Cmd);

    /// <summary>
    /// The working directory the child would run in (absolute). As everything else here, it is
    /// relative to the spawning logical process (the working directory and environment of an
    /// in-process child are not those of the OS process).
    /// </summary>
    public string EffectiveCwd
    {
        get
        {
            var proc = LeanContext.Proc;
            return Cwd == null ? proc.Cwd : Path.GetFullPath(proc.Resolve(Cwd));
        }
    }

    /// <summary>The environment the child would see.</summary>
    public Dictionary<string, string> BuildEnvironment()
    {
        var env = InheritEnv
            ? LeanContext.Proc.EnvironmentSnapshot()
            : new Dictionary<string, string>(OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal);
        foreach (var kv in Env)
        {
            if (kv.Value == null) env.Remove(kv.Key);
            else env[kv.Key] = kv.Value;
        }
        return env;
    }

    public override string ToString() => Cmd + (Args.Count > 0 ? " " + string.Join(" ", Args) : "");
}

/// <summary>A running child process as seen by `IO.Process.Child`.</summary>
public abstract class LeanChildProcess
{
    /// <summary>Stream the parent writes to the child's stdin (only when stdin is piped).</summary>
    public abstract Stream StdinPipe { get; }
    /// <summary>Stream the parent reads the child's stdout from (only when stdout is piped).</summary>
    public abstract Stream StdoutPipe { get; }
    /// <summary>Stream the parent reads the child's stderr from (only when stderr is piped).</summary>
    public abstract Stream StderrPipe { get; }
    /// <summary>The OS process id, or null if the child is not an OS process.</summary>
    public virtual int? OsPid => null;
    /// <summary>Block until the child exits and return its exit code.</summary>
    public abstract int WaitForExit();
    /// <summary>The exit code if the child has exited.</summary>
    public abstract bool TryGetExitCode(out int code);
    /// <summary>Terminate the child (`SIGKILL`).</summary>
    public abstract void Kill();
}

/// <summary>Spawning of child processes.</summary>
public static class LeanProcess
{
    /// <summary>
    /// Called for every `IO.Process.spawn`. Return a child (e.g. an <see cref="InProcessChild"/>) to
    /// handle the request, or null to spawn an OS process as usual.
    /// </summary>
    public static Func<SpawnRequest, LeanChildProcess> ProcessSpawnHook;

    static int s_nextFakePid = 0x40000000;

    public static LeanChildProcess Spawn(SpawnRequest req)
    {
        var hook = ProcessSpawnHook;
        if (hook != null)
        {
            var c = hook(req);
            if (c != null) return c;
        }
        return OsChildProcess.Start(req);
    }

    internal static int AllocFakePid() => Interlocked.Increment(ref s_nextFakePid);

    // Children by (possibly fake) pid; `IO.Process.Child` objects only store the pid, as in C.
    static readonly Dictionary<int, LeanChildProcess> s_children = new();

    internal static int Register(LeanChildProcess c)
    {
        int pid = c.OsPid ?? AllocFakePid();
        lock (s_children) s_children[pid] = c;
        return pid;
    }

    internal static LeanChildProcess Find(int pid)
    {
        lock (s_children) return s_children.TryGetValue(pid, out var c) ? c : null;
    }
}

/// <summary>A child that is an OS process.</summary>
public sealed class OsChildProcess : LeanChildProcess
{
    readonly Process m_proc;
    readonly bool m_setsid;
    readonly List<Task> m_pumps = new();
    Stream m_stdin, m_stdout, m_stderr;
    int m_exitCode;
    bool m_exited;

    OsChildProcess(Process p, bool setsid) { m_proc = p; m_setsid = setsid; }

    public override Stream StdinPipe => m_stdin;
    public override Stream StdoutPipe => m_stdout;
    public override Stream StderrPipe => m_stderr;
    public override int? OsPid => m_proc.Id;

    static bool IsExecutable(string path)
    {
        try
        {
            if (!File.Exists(path)) return false;
            if (OperatingSystem.IsWindows()) return true;
            var m = File.GetUnixFileMode(path);
            return (m & (UnixFileMode.UserExecute | UnixFileMode.GroupExecute | UnixFileMode.OtherExecute)) != 0;
        }
        catch (Exception) { return false; }
    }

    /// <summary>Resolve the command like `execvp` in the child (after `chdir` and environment changes).</summary>
    static string ResolveCommand(string cmd, string cwd, Dictionary<string, string> env)
    {
        if (OperatingSystem.IsWindows()) return cmd;
        string baseDir = cwd ?? Directory.GetCurrentDirectory();
        if (cmd.Contains('/'))
            return Path.IsPathRooted(cmd) ? cmd : Path.GetFullPath(Path.Combine(baseDir, cmd));
        if (!env.TryGetValue("PATH", out var pathVar) || pathVar == null) pathVar = "/usr/bin:/bin";
        foreach (var dir in pathVar.Split(':'))
        {
            string d = dir.Length == 0 ? "." : dir;
            string cand = Path.Combine(Path.IsPathRooted(d) ? d : Path.Combine(baseDir, d), cmd);
            if (IsExecutable(cand)) return cand;
        }
        // Not found: fail like `execvp` would (instead of letting .NET search other directories).
        throw new LeanErrnoException(LeanErrno.ENOENT);
    }

    static Task Pump(Stream from, Func<Stream> to, bool closeTo)
    {
        return Task.Run(() =>
        {
            var buf = new byte[16384];
            try
            {
                int n;
                while ((n = from.Read(buf, 0, buf.Length)) > 0)
                {
                    var t = to();
                    if (t == null) continue;
                    lock (LeanStdStreams.s_writeLock) { t.Write(buf, 0, n); t.Flush(); }
                }
            }
            catch (Exception) { }
            finally
            {
                if (closeTo) { try { to()?.Dispose(); } catch (Exception) { } }
            }
        });
    }

    public static OsChildProcess Start(SpawnRequest req)
    {
        var env = req.BuildEnvironment();
        var psi = new ProcessStartInfo
        {
            FileName = ResolveCommand(req.Cmd, req.EffectiveCwd, env),
            UseShellExecute = false,
        };
        foreach (var a in req.Args) psi.ArgumentList.Add(a);
        if (req.Cwd != null || LeanContext.Proc.HasLogicalCwd) psi.WorkingDirectory = req.EffectiveCwd;
        psi.Environment.Clear();
        foreach (var kv in env) psi.Environment[kv.Key] = kv.Value;

        // Inherited streams are only passed through at the OS level if they are the real console
        // streams; if the host redirected them, the child's output is pumped into them instead.
        var parentIn = LeanStdStreams.Stdin;
        var parentOut = LeanStdStreams.Stdout;
        var parentErr = LeanStdStreams.Stderr;
        bool pumpIn = req.Stdin == LeanStdioMode.Inherit && !LeanStdStreams.IsConsoleStream(parentIn);
        bool pumpOut = req.Stdout == LeanStdioMode.Inherit && !LeanStdStreams.IsConsoleStream(parentOut);
        bool pumpErr = req.Stderr == LeanStdioMode.Inherit && !LeanStdStreams.IsConsoleStream(parentErr);
        psi.RedirectStandardInput = req.Stdin != LeanStdioMode.Inherit || pumpIn;
        psi.RedirectStandardOutput = req.Stdout != LeanStdioMode.Inherit || pumpOut;
        psi.RedirectStandardError = req.Stderr != LeanStdioMode.Inherit || pumpErr;
        if (psi.RedirectStandardInput) psi.StandardInputEncoding = new UTF8Encoding(false);

        var p = Process.Start(psi);
        if (p == null) throw new LeanErrnoException(LeanErrno.ENOENT);
        var c = new OsChildProcess(p, req.SetSid);
        switch (req.Stdin)
        {
            case LeanStdioMode.Piped: c.m_stdin = p.StandardInput.BaseStream; break;
            case LeanStdioMode.Null: p.StandardInput.BaseStream.Dispose(); break;
            default:
                if (pumpIn)
                {
                    var childIn = p.StandardInput.BaseStream;
                    // Not awaited on exit: the parent's stdin may never reach EOF.
                    Pump(parentIn, () => childIn, true);
                }
                break;
        }
        switch (req.Stdout)
        {
            case LeanStdioMode.Piped: c.m_stdout = p.StandardOutput.BaseStream; break;
            case LeanStdioMode.Null: c.m_pumps.Add(Pump(p.StandardOutput.BaseStream, () => null, false)); break;
            default: if (pumpOut) c.m_pumps.Add(Pump(p.StandardOutput.BaseStream, () => parentOut, false)); break;
        }
        switch (req.Stderr)
        {
            case LeanStdioMode.Piped: c.m_stderr = p.StandardError.BaseStream; break;
            case LeanStdioMode.Null: c.m_pumps.Add(Pump(p.StandardError.BaseStream, () => null, false)); break;
            default: if (pumpErr) c.m_pumps.Add(Pump(p.StandardError.BaseStream, () => parentErr, false)); break;
        }
        return c;
    }

    void Finish()
    {
        lock (this)
        {
            if (m_exited) return;
            try { Task.WaitAll(m_pumps.ToArray()); } catch (Exception) { }
            m_exitCode = m_proc.ExitCode;
            m_exited = true;
        }
    }

    public override int WaitForExit()
    {
        if (!m_exited)
        {
            m_proc.WaitForExit();
            Finish();
        }
        return m_exitCode;
    }

    public override bool TryGetExitCode(out int code)
    {
        if (!m_exited && m_proc.HasExited) Finish();
        code = m_exitCode;
        return m_exited;
    }

    public override void Kill()
    {
        // As with `kill(2)`, killing an exited child that has not been waited for succeeds.
        if (m_exited) throw new LeanErrnoException(LeanErrno.ESRCH);
        try { if (!m_proc.HasExited) m_proc.Kill(m_setsid); }
        catch (InvalidOperationException) { }
    }
}

/// <summary>Context of an <see cref="InProcessChild"/>'s main function.</summary>
public sealed class InProcessContext
{
    public SpawnRequest Request { get; init; }
    /// <summary>The child's standard streams (pipes, the parent's streams, or null streams).</summary>
    public Stream Stdin { get; init; }
    public Stream Stdout { get; init; }
    public Stream Stderr { get; init; }
    /// <summary>The child's working directory (absolute). The process-wide current directory is not changed.</summary>
    public string Cwd { get; init; }
    /// <summary>The child's environment (the process environment is not changed).</summary>
    public Dictionary<string, string> Environment { get; init; }
    /// <summary>Set when the parent called `Child.kill`; long-running children may poll it.</summary>
    public CancellationToken KillRequested { get; init; }
}

/// <summary>
/// A "child process" that runs a managed function on a dedicated thread. Its standard streams are
/// in-memory pipes (or the parent's streams / null streams, according to the request), and while
/// it runs, `LeanStdStreams` (and hence Lean's `IO.getStdout` etc.) are redirected to them for the
/// child's logical call context. The exit code is the function's result; `LeanExitException`
/// (`IO.Process.exit`) is turned into its exit code, other exceptions into exit code 1.
/// </summary>
public sealed class InProcessChild : LeanChildProcess
{
    readonly LeanPipe m_in, m_out, m_err;
    readonly Thread m_thread;
    readonly CancellationTokenSource m_kill = new();
    readonly ManualResetEventSlim m_done = new(false);
    readonly LeanLogicalProcess m_proc;
    int m_exitCode;
    volatile bool m_exited;

    public InProcessChild(SpawnRequest req, Func<InProcessContext, int> main, int maxStackSize = 64 * 1024 * 1024)
    {
        Stream cin, cout, cerr;
        switch (req.Stdin)
        {
            case LeanStdioMode.Piped: m_in = new LeanPipe(); cin = m_in.Reader; break;
            case LeanStdioMode.Null: cin = new MemoryStream(Array.Empty<byte>(), false); break;
            default: cin = LeanStdStreams.Stdin; break;
        }
        switch (req.Stdout)
        {
            case LeanStdioMode.Piped: m_out = new LeanPipe(); cout = m_out.Writer; break;
            case LeanStdioMode.Null: cout = Stream.Null; break;
            default: cout = LeanStdStreams.Stdout; break;
        }
        switch (req.Stderr)
        {
            case LeanStdioMode.Piped: m_err = new LeanPipe(); cerr = m_err.Writer; break;
            case LeanStdioMode.Null: cerr = Stream.Null; break;
            default: cerr = LeanStdStreams.Stderr; break;
        }
        var ctx = new InProcessContext
        {
            Request = req,
            Stdin = cin,
            Stdout = cout,
            Stderr = cerr,
            Cwd = req.EffectiveCwd,
            Environment = req.BuildEnvironment(),
            KillRequested = m_kill.Token,
        };
        // The child's logical process: its own working directory, environment and executable path
        // (`IO.currentDir`, relative paths, `IO.getEnv`, `IO.appPath`, ... of the child and of the
        // tasks and threads it starts refer to these, not to the state of the OS process).
        m_proc = new LeanLogicalProcess(ctx.Cwd, ctx.Environment);
        try
        {
            if (req.Cmd.Contains('/') || req.Cmd.Contains(Path.DirectorySeparatorChar))
                m_proc.AppPath = Path.GetFullPath(req.Cmd, ctx.Cwd);
        }
        catch (Exception) { }
        m_thread = new Thread(() => { LeanRt.lean_declare_thread_stack(maxStackSize); Run(ctx, main); }, maxStackSize) { IsBackground = true, Name = "lean child: " + req.CommandName };
        m_thread.Start();
    }

    void Run(InProcessContext ctx, Func<InProcessContext, int> main)
    {
        int code;
        using (LeanStdStreams.Redirect(ctx.Stdin, ctx.Stdout, ctx.Stderr))
        {
            LeanContext.SetProcess(m_proc);
            try { code = main(ctx); }
            catch (LeanExitException e) { code = e.ExitCode; }
            catch (Exception e)
            {
                try
                {
                    var b = Encoding.UTF8.GetBytes("uncaught exception in in-process child: " + e + "\n");
                    ctx.Stderr.Write(b, 0, b.Length);
                }
                catch (Exception) { }
                code = 1;
            }
            try { ctx.Stdout.Flush(); } catch (Exception) { }
            try { ctx.Stderr.Flush(); } catch (Exception) { }
        }
        // Natively the child's remaining threads die with the process: let its tasks see a
        // cancellation request (`IO.checkCanceled`).
        m_proc.MarkExited();
        m_out?.Writer.Dispose();
        m_err?.Writer.Dispose();
        m_in?.Reader.Dispose();
        if (!m_exited) m_exitCode = code;
        m_exited = true;
        m_done.Set();
    }

    public override Stream StdinPipe => m_in?.Writer;
    public override Stream StdoutPipe => m_out?.Reader;
    public override Stream StderrPipe => m_err?.Reader;

    public override int WaitForExit()
    {
        m_done.Wait();
        return m_exitCode;
    }

    public override bool TryGetExitCode(out int code)
    {
        code = m_exitCode;
        return m_exited;
    }

    /// <summary>
    /// Threads cannot be killed: the child is reported as killed by `SIGKILL` (exit code 137), its
    /// pipes are closed and <see cref="InProcessContext.KillRequested"/> is signaled.
    /// </summary>
    public override void Kill()
    {
        if (m_exited) return;
        m_exitCode = 128 + 9;
        m_exited = true;
        m_proc.MarkExited();
        m_kill.Cancel();
        m_out?.Writer.Dispose();
        m_err?.Writer.Dispose();
        m_in?.Reader.Dispose();
        m_done.Set();
    }
}

/// <summary>An in-memory unidirectional pipe with an unbounded buffer.</summary>
public sealed class LeanPipe
{
    readonly object m_lock = new();
    readonly Queue<byte[]> m_chunks = new();
    int m_headOffset;
    bool m_writerClosed, m_readerClosed;

    public Stream Reader { get; }
    public Stream Writer { get; }

    public LeanPipe()
    {
        Reader = new End(this, false);
        Writer = new End(this, true);
    }

    int Read(Span<byte> dst)
    {
        lock (m_lock)
        {
            while (m_chunks.Count == 0 && !m_writerClosed && !m_readerClosed) Monitor.Wait(m_lock);
            if (m_readerClosed) throw new ObjectDisposedException("pipe");
            int got = 0;
            while (got < dst.Length && m_chunks.Count > 0)
            {
                var head = m_chunks.Peek();
                int k = Math.Min(dst.Length - got, head.Length - m_headOffset);
                head.AsSpan(m_headOffset, k).CopyTo(dst.Slice(got));
                got += k;
                m_headOffset += k;
                if (m_headOffset == head.Length) { m_chunks.Dequeue(); m_headOffset = 0; }
            }
            return got;
        }
    }

    void Write(ReadOnlySpan<byte> src)
    {
        if (src.Length == 0) return;
        lock (m_lock)
        {
            if (m_writerClosed) throw new ObjectDisposedException("pipe");
            if (m_readerClosed) throw new LeanErrnoException(LeanErrno.EPIPE);
            m_chunks.Enqueue(src.ToArray());
            Monitor.PulseAll(m_lock);
        }
    }

    void Close(bool writer)
    {
        lock (m_lock)
        {
            if (writer) m_writerClosed = true;
            else { m_readerClosed = true; m_chunks.Clear(); }
            Monitor.PulseAll(m_lock);
        }
    }

    sealed class End : Stream
    {
        readonly LeanPipe m_pipe;
        readonly bool m_writer;
        public End(LeanPipe p, bool writer) { m_pipe = p; m_writer = writer; }
        public override bool CanRead => !m_writer;
        public override bool CanWrite => m_writer;
        public override bool CanSeek => false;
        public override long Length => throw new NotSupportedException();
        public override long Position { get => throw new NotSupportedException(); set => throw new NotSupportedException(); }
        public override void Flush() { }
        public override int Read(byte[] buffer, int offset, int count) => Read(buffer.AsSpan(offset, count));
        public override int Read(Span<byte> buffer)
        {
            if (m_writer) throw new NotSupportedException();
            return m_pipe.Read(buffer);
        }
        public override void Write(byte[] buffer, int offset, int count) => Write(buffer.AsSpan(offset, count));
        public override void Write(ReadOnlySpan<byte> buffer)
        {
            if (!m_writer) throw new NotSupportedException();
            m_pipe.Write(buffer);
        }
        public override long Seek(long offset, SeekOrigin origin) => throw new NotSupportedException();
        public override void SetLength(long value) => throw new NotSupportedException();
        protected override void Dispose(bool disposing) { m_pipe.Close(m_writer); base.Dispose(disposing); }
    }
}
