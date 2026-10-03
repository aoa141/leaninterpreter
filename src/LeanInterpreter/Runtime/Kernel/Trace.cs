// Port of kernel/trace.{h,cpp}: minimal tracing support for C++-ported components (used by the
// IR interpreter). The options are installed for the current thread with `ScopeTraceEnv`.

using System.Text;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

public static class KernelTrace
{
    [ThreadStatic] static Obj t_opts;

    /// <summary>`is_trace_class_enabled(n)`.</summary>
    public static bool IsTraceClassEnabled(Name n)
    {
        Obj opts = t_opts;
        if (opts == null) return false;
        return KX.IsTraceClassEnabled(RC.Own(opts), RC.Own(n.Raw)) != 0;
    }

    /// <summary>`scope_trace_env`: install the options (borrowed) for the current thread.</summary>
    public readonly struct ScopeTraceEnv : IDisposable
    {
        readonly Obj m_old;
        public ScopeTraceEnv(Obj opts) { m_old = t_opts; t_opts = opts; }
        public void Dispose() { t_opts = m_old; }
    }

    /// <summary>`lean_trace(cls, msg)`: print `[cls] msg` to stderr through `IO.eprint`.</summary>
    public static void Trace(Name cls, string msg)
    {
        if (!IsTraceClassEnabled(cls)) return;
        var sb = new StringBuilder();
        sb.Append('[');
        Name.Display(sb, cls.Raw);
        sb.Append("] ");
        sb.Append(msg);
        Obj r = KX.IOEPrint(lean_mk_string(sb.ToString()));
        if (!lean_io_result_is_ok(r))
            LeanIO.StderrWrite("uncaught exception while tracing\n");
        lean_dec(r);
    }
}
