// Process-level standard streams used by the runtime. The Lean-level `IO.getStdout` etc. are
// implemented on top of these (see Runtime/IO*.cs). Hosts can redirect them (e.g. to capture
// the output of an in-process `lean` invocation).

using System.Text;

namespace LeanInterpreter.Runtime;

public static class LeanIO
{
    static readonly object s_lock = new();
    static Stream s_stdout = Console.OpenStandardOutput();
    static Stream s_stderr = Console.OpenStandardError();
    static Stream s_stdin = Console.OpenStandardInput();

    public static Stream Stdout { get => s_stdout; set { lock (s_lock) s_stdout = value; } }
    public static Stream Stderr { get => s_stderr; set { lock (s_lock) s_stderr = value; } }
    public static Stream Stdin { get => s_stdin; set { lock (s_lock) s_stdin = value; } }

    public static void StdoutWrite(string s) => Write(s_stdout, s);
    public static void StderrWrite(string s) => Write(s_stderr, s);

    static void Write(Stream st, string s)
    {
        var b = Encoding.UTF8.GetBytes(s);
        lock (s_lock) { st.Write(b, 0, b.Length); st.Flush(); }
    }
}
