// Port of runtime/process.cpp. `IO.Process.Child` objects have the same layout as in C
// (`stdin`, `stdout`, `stderr` object fields, then the pid (`UInt32`) and the `setsid` flag in
// the scalar area); the managed child is found through its pid (see `LeanProcess`).

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    const uint IoChildPidOffset = 3 * 8;
    const uint IoChildSetsidOffset = 3 * 8 + 4;

    /* IO.Process.getPID : BaseIO UInt32 */
    public static uint lean_io_process_get_pid() => (uint)System.Environment.ProcessId;

    static LeanChildProcess IoChildOf(Obj child) =>
        LeanProcess.Find((int)lean_ctor_get_uint32(child, IoChildPidOffset));

    /* Child.wait {cfg : @& StdioConfig} : @& Child cfg → IO UInt32 */
    public static Obj lean_io_process_child_wait(Obj cfg, Obj child)
    {
        var c = IoChildOf(child);
        if (c == null) return LeanIOErrors.DecodeResult(LeanErrno.ECHILD, null);
        try { return lean_io_result_mk_ok(lean_box((uint)c.WaitForExit())); }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
    }

    /* Child.tryWait {cfg : @& StdioConfig} : @& Child cfg → IO (Option UInt32) */
    public static Obj lean_io_process_child_try_wait(Obj cfg, Obj child)
    {
        var c = IoChildOf(child);
        if (c == null) return LeanIOErrors.DecodeResult(LeanErrno.ECHILD, null);
        try
        {
            if (c.TryGetExitCode(out int code))
                return lean_io_result_mk_ok(lean_mk_option_some(lean_box((uint)code)));
            return lean_io_result_mk_ok(lean_mk_option_none());
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
    }

    /* Child.kill {cfg : @& StdioConfig} : @& Child cfg → IO Unit */
    public static Obj lean_io_process_child_kill(Obj cfg, Obj child)
    {
        var c = IoChildOf(child);
        if (c == null) return LeanIOErrors.DecodeResult(LeanErrno.ESRCH, null);
        try { c.Kill(); return IoOkUnit(); }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
    }

    /* Child.pid {cfg : @& StdioConfig} : Child cfg → UInt32 */
    public static uint lean_io_process_child_pid(Obj cfg, Obj child)
    {
        uint pid = lean_ctor_get_uint32(child, IoChildPidOffset);
        lean_dec(child);
        return pid;
    }

    /* Child.takeStdin {cfg : @& StdioConfig} : Child cfg → IO (cfg.stdin.toHandleType × Child {cfg with stdin := .null}) */
    public static Obj lean_io_process_child_take_stdin(Obj cfg, Obj child)
    {
        var child2 = lean_alloc_ctor(0, 3, 5);
        lean_ctor_set(child2, 0, lean_box(0));
        var o1 = lean_ctor_get(child, 1); lean_inc(o1); lean_ctor_set(child2, 1, o1);
        var o2 = lean_ctor_get(child, 2); lean_inc(o2); lean_ctor_set(child2, 2, o2);
        lean_ctor_set_uint32(child2, IoChildPidOffset, lean_ctor_get_uint32(child, IoChildPidOffset));
        lean_ctor_set_uint8(child2, IoChildSetsidOffset, lean_ctor_get_uint8(child, IoChildSetsidOffset));
        var stdin = lean_ctor_get(child, 0);
        lean_inc(stdin);
        lean_dec(child);
        return lean_io_result_mk_ok(lean_mk_pair(stdin, child2));
    }

    /// <summary>Decode an `IO.Process.SpawnArgs` value (borrowed).</summary>
    public static SpawnRequest IoDecodeSpawnArgs(Obj args)
    {
        var stdioCfg = lean_ctor_get(args, 0);
        var argv = new List<string>();
        var arr = lean_ctor_get(args, 2);
        for (ulong i = 0; i < lean_array_size(arr); i++) argv.Add(lean_string_to_net(lean_array_get_core(arr, i)));
        var cwdOpt = lean_ctor_get(args, 3);
        string cwd = lean_is_scalar(cwdOpt) ? null : lean_string_to_net(lean_ctor_get(cwdOpt, 0));
        var env = new List<KeyValuePair<string, string>>();
        var envArr = lean_ctor_get(args, 4);
        for (ulong i = 0; i < lean_array_size(envArr); i++)
        {
            var pair = lean_array_get_core(envArr, i);
            var key = lean_string_to_net(lean_ctor_get(pair, 0));
            var vOpt = lean_ctor_get(pair, 1);
            env.Add(new(key, lean_is_scalar(vOpt) ? null : lean_string_to_net(lean_ctor_get(vOpt, 0))));
        }
        return new SpawnRequest
        {
            Stdin = (LeanStdioMode)lean_ctor_get_uint8(stdioCfg, 0),
            Stdout = (LeanStdioMode)lean_ctor_get_uint8(stdioCfg, 1),
            Stderr = (LeanStdioMode)lean_ctor_get_uint8(stdioCfg, 2),
            Cmd = lean_string_to_net(lean_ctor_get(args, 1)),
            Args = argv,
            Cwd = cwd,
            Env = env,
            InheritEnv = lean_ctor_get_uint8(args, 5 * 8) != 0,
            SetSid = lean_ctor_get_uint8(args, 5 * 8 + 1) != 0,
        };
    }

    /* IO.Process.spawn (args : SpawnArgs) : IO (Child args.toStdioConfig) */
    public static Obj lean_io_process_spawn(Obj args)
    {
        SpawnRequest req;
        try { req = IoDecodeSpawnArgs(args); }
        finally { lean_dec(args); }
        LeanChildProcess c;
        try
        {
            c = LeanProcess.Spawn(req);
        }
        catch (Exception e)
        {
            return LeanIOErrors.FromExceptionResult(e, null);
        }
        int pid = LeanProcess.Register(c);
        Obj parentStdin = lean_box(0), parentStdout = lean_box(0), parentStderr = lean_box(0);
        if (req.Stdin == LeanStdioMode.Piped && c.StdinPipe != null) parentStdin = LeanHandle.Wrap(new LeanHandle(c.StdinPipe));
        if (req.Stdout == LeanStdioMode.Piped && c.StdoutPipe != null) parentStdout = LeanHandle.Wrap(new LeanHandle(c.StdoutPipe));
        if (req.Stderr == LeanStdioMode.Piped && c.StderrPipe != null) parentStderr = LeanHandle.Wrap(new LeanHandle(c.StderrPipe));
        var r = lean_alloc_ctor(0, 3, 5);
        lean_ctor_set(r, 0, parentStdin);
        lean_ctor_set(r, 1, parentStdout);
        lean_ctor_set(r, 2, parentStderr);
        lean_ctor_set_uint32(r, IoChildPidOffset, (uint)pid);
        lean_ctor_set_uint8(r, IoChildSetsidOffset, req.SetSid ? (byte)1 : (byte)0);
        return lean_io_result_mk_ok(r);
    }
}
