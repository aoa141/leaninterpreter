// Port of `lean_main` (src/util/shell.cpp): command-line driver of the `lean` executable.
// Option processing and the actual work are implemented in Lean (`Lean.Shell`); this file only
// parses the command line like `getopt_long` and calls the exported Lean functions.

using LeanInterpreter.Runtime;

namespace LeanInterpreter;

public static unsafe class LeanShell
{
    enum ArgKind { None, Required, Optional }

    // `g_long_options` in shell.cpp
    static readonly (string name, ArgKind kind, char val)[] s_longOptions =
    {
        ("version", ArgKind.None, 'v'),
        ("help", ArgKind.None, 'h'),
        ("githash", ArgKind.None, 'g'),
        ("short-version", ArgKind.None, 'V'),
        ("run", ArgKind.None, 'r'),
        ("o", ArgKind.Optional, 'o'),
        ("i", ArgKind.Optional, 'i'),
        ("stdin", ArgKind.None, 'I'),
        ("root", ArgKind.Required, 'R'),
        ("memory", ArgKind.Required, 'M'),
        ("trust", ArgKind.Required, 't'),
        ("profile", ArgKind.None, 'P'),
        ("stats", ArgKind.None, 'a'),
        ("quiet", ArgKind.None, 'q'),
        ("deps", ArgKind.None, 'd'),
        ("src-deps", ArgKind.None, 'O'),
        ("deps-json", ArgKind.None, 'N'),
        ("timeout", ArgKind.Optional, 'T'),
        ("c", ArgKind.Optional, 'c'),
        ("bc", ArgKind.Optional, 'b'),
        ("features", ArgKind.None, 'f'),
        ("exitOnPanic", ArgKind.None, 'e'),
        ("threads", ArgKind.Required, 'j'),
        ("tstack", ArgKind.Required, 's'),
        ("server", ArgKind.None, 'S'),
        ("worker", ArgKind.None, 'W'),
        ("plugin", ArgKind.Required, 'p'),
        ("load-dynlib", ArgKind.Required, 'l'),
        ("setup", ArgKind.Required, 'u'),
        ("error", ArgKind.Required, 'E'),
        ("json", ArgKind.None, 'J'),
        ("print-prefix", ArgKind.None, 'x'),
        ("print-libdir", ArgKind.None, 'L'),
        ("incr-save", ArgKind.Required, 'Y'),
        ("incr-load", ArgKind.Required, 'Z'),
        ("incr-header-save", ArgKind.Required, 'H'),
    };

    // `g_opt_str` in shell.cpp
    const string OptStr = "PdD:o:i:b:c:C:qgvVht:012j:012rR:M:012T:012ap:eE:Y:Z:H:s:012";

    static ArgKind ShortKind(char c)
    {
        int i = OptStr.IndexOf(c);
        if (i < 0 || c == ':') return (ArgKind)(-1);
        return i + 1 < OptStr.Length && OptStr[i + 1] == ':' ? ArgKind.Required : ArgKind.None;
    }

    /// <summary>
    /// Runs the `lean` command line on the current thread (which must have a large stack) and
    /// returns its exit code. The runtime must have been initialized (<see cref="LeanHost.Initialize"/>).
    /// </summary>
    public static int RunOnCurrentThread(string[] argv)
    {
        var initStart = System.Diagnostics.Stopwatch.StartNew();
        LeanHost.Initialize();
        double initTime = initStart.Elapsed.TotalSeconds;
        using (LeanHost.EnterProgram())
            return Run(argv, initTime);
    }

    static int Run(string[] argv, double initTime)
    {
        LeanPaths.AppPath = LeanSysroot.LeanExe;
        try
        {
            Consume(((delegate*<Obj>)LeanExports.Get("lean_init_search_path"))());
        }
        catch (LeanPanicException ex)
        {
            LeanStdStreams.WriteProcessStderr("error: " + ex.Message + "\n");
            return 1;
        }
        Consume(((delegate*<Obj>)LeanExports.Get("lean_enable_initializer_execution"))());

        Obj shellOpts = ((delegate*<Obj, Obj>)LeanExports.Get("lean_shell_options_mk"))(LeanRt.lean_box(0));
        var process = ((delegate*<Obj, uint, Obj, Obj>)LeanExports.Get("lean_shell_options_process"));
        var getRun = ((delegate*<Obj, byte>)LeanExports.Get("lean_shell_options_get_run"));

        // getopt_long with GNU-style permutation of non-option arguments
        var positional = new List<string>();
        int i = 0;
        while (i < argv.Length)
        {
            string a = argv[i];
            if (a == "--") { i++; positional.AddRange(argv[i..]); i = argv.Length; break; }
            if (a.Length < 2 || a[0] != '-') { positional.Add(a); i++; continue; }
            i++;
            var opts = new List<(char c, string arg)>();
            if (a[1] == '-')
            {
                string body = a.Substring(2);
                string name = body, value = null;
                int eq = body.IndexOf('=');
                if (eq >= 0) { name = body.Substring(0, eq); value = body.Substring(eq + 1); }
                var lo = s_longOptions.FirstOrDefault(o => o.name == name);
                if (lo.name == null)
                {
                    // `getopt_long` accepts unambiguous prefixes of option names
                    var matches = s_longOptions.Where(o => o.name.StartsWith(name, StringComparison.Ordinal)).ToArray();
                    if (matches.Length == 1 || (matches.Length > 1 && matches.All(m => m.val == matches[0].val && m.kind == matches[0].kind)))
                        lo = matches[0];
                    else if (matches.Length > 1)
                    {
                        LeanStdStreams.WriteProcessStderr($"lean: option '--{name}' is ambiguous; possibilities:" + string.Concat(matches.Select(m => " '--" + m.name + "'")) + "\n");
                        return Process('?', null, process, ref shellOpts, out int rcA) ? rcA : 1;
                    }
                }
                if (lo.name == null)
                {
                    LeanStdStreams.WriteProcessStderr($"lean: unrecognized option '{a}'" + "\n");
                    return Process('?', null, process, ref shellOpts, out int rc0) ? rc0 : 1;
                }
                switch (lo.kind)
                {
                    case ArgKind.None:
                        if (value != null)
                        {
                            LeanStdStreams.WriteProcessStderr($"lean: option doesn't take an argument -- {name}" + "\n");
                            value = null;
                            opts.Add(('?', null));
                            break;
                        }
                        opts.Add((lo.val, null));
                        break;
                    case ArgKind.Required:
                        if (value == null)
                        {
                            if (i >= argv.Length)
                            {
                                LeanStdStreams.WriteProcessStderr($"lean: option requires an argument -- {name}" + "\n");
                                opts.Add(('?', null));
                                break;
                            }
                            value = argv[i++];
                        }
                        opts.Add((lo.val, value));
                        break;
                    case ArgKind.Optional:
                        opts.Add((lo.val, value));
                        break;
                }
            }
            else
            {
                // one or more short options
                for (int k = 1; k < a.Length; k++)
                {
                    char c = a[k];
                    var kind = ShortKind(c);
                    if ((int)kind < 0) { opts.Add(('?', null)); break; }
                    if (kind == ArgKind.Required)
                    {
                        string value;
                        if (k + 1 < a.Length) value = a.Substring(k + 1);
                        else if (i < argv.Length) value = argv[i++];
                        else
                        {
                            LeanStdStreams.WriteProcessStderr($"lean: option requires an argument -- {c}" + "\n");
                            opts.Add(('?', null));
                            break;
                        }
                        opts.Add((c, value));
                        break;
                    }
                    opts.Add((c, null));
                }
            }
            bool stop = false;
            foreach (var (c, arg) in opts)
            {
                if (Process(c, arg, process, ref shellOpts, out int rc))
                    return rc;
                if (getRun(shellOpts) != 0) { stop = true; break; }
            }
            if (stop)
            {
                // `--run` ends option processing. glibc's `getopt_long` has not yet moved the
                // non-options it skipped behind the options at this point, so the program and its
                // arguments are what follows `--run`: `lean A.lean --run B.lean x` runs `B.lean x`.
                positional.Clear();
                positional.AddRange(argv[i..]);
                i = argv.Length;
                break;
            }
        }

        LeanRt.lean_io_mark_end_initialization();
        if (((delegate*<Obj, byte>)LeanExports.Get("lean_shell_options_get_profiler"))(shellOpts) != 0)
            LeanProfiling.ReportTime("initialization", initTime);
        uint numThreads = ((delegate*<Obj, uint>)LeanExports.Get("lean_shell_options_get_num_threads"))(shellOpts);
        LeanRt.lean_init_task_manager_using(numThreads);

        Obj args = LeanRt.lean_box(0);
        for (int k = positional.Count - 1; k >= 0; k--)
            args = LeanRt.lean_mk_list_cons(LeanRt.lean_mk_string(positional[k]), args);
        try
        {
            Obj r = ((delegate*<Obj, Obj, Obj>)LeanExports.Get("lean_shell_main"))(args, shellOpts);
            // `scoped_task_manager` in `lean_main`: when the main function returns (as opposed
            // to `exit`), the remaining tasks and dedicated threads are waited for.
            LeanRt.lean_finalize_task_manager();
            if (LeanRt.lean_io_result_is_ok(r))
            {
                uint code = LeanRt.lean_unbox_uint32(LeanRt.lean_io_result_get_value(r));
                return (int)code;
            }
            LeanRt.lean_io_result_show_error(r);
            return 1;
        }
        catch (LeanExitException e)
        {
            Debug(e);
            return e.ExitCode;
        }
        catch (LeanPanicException e)
        {
            Debug(e);
            return 1; // `lean_internal_panic`: the message has been printed
        }
    }

    static bool Process(char c, string optarg, delegate*<Obj, uint, Obj, Obj> process, ref Obj shellOpts, out int rc)
    {
        Obj optArg = optarg != null ? LeanRt.lean_mk_option_some(LeanRt.lean_mk_string(optarg)) : LeanRt.lean_box(0);
        Obj r;
        try
        {
            r = process(shellOpts, c, optArg);
        }
        catch (LeanExitException e)
        {
            rc = e.ExitCode;
            return true;
        }
        if (LeanRt.lean_io_result_is_ok(r))
        {
            shellOpts = LeanRt.lean_io_result_get_value(r);
            LeanRt.lean_inc(shellOpts);
            LeanRt.lean_dec_ref(r);
            rc = 0;
            return false;
        }
        rc = (int)LeanRt.lean_unbox(LeanRt.lean_io_result_get_error(r));
        LeanRt.lean_dec_ref(r);
        return true;
    }

    /// <summary>Runs the `lean` command line on a large-stack thread and returns its exit code.</summary>
    public static int Main(string[] argv)
    {
        try
        {
            return LeanHost.RunWithLargeStack(() => RunOnCurrentThread(argv));
        }
        catch (LeanExitException e)
        {
            return e.ExitCode;
        }
    }

    static readonly bool s_debug = Environment.GetEnvironmentVariable("LEAN_INTERP_DEBUG") == "1";

    /// <summary>LEAN_INTERP_DEBUG=1: report how a program ended abnormally.</summary>
    internal static void Debug(Exception e)
    {
        if (s_debug && !(e is LeanExitException { ExitCode: 0 })) LeanStdStreams.WriteProcessStderr($"[lean-interpreter] {e}" + Environment.NewLine);
    }

    static void Consume(Obj r)
    {
        if (LeanRt.lean_io_result_is_error(r))
        {
            LeanRt.lean_io_result_show_error(r);
            throw new LeanPanicException("initialization failed");
        }
        LeanRt.lean_dec_ref(r);
    }

}
