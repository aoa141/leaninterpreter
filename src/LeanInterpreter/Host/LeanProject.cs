// High-level API: run Lean on the files of a project directory, in-process, with the Lean
// libraries interpreted (no native Lean installation, no code generation).

using System.Text;
using System.Text.Json;
using LeanInterpreter.Runtime;

namespace LeanInterpreter;

/// <summary>Outcome of a `lean` invocation.</summary>
public sealed record LeanResult(int ExitCode, string Stdout, string Stderr)
{
    public bool Success => ExitCode == 0;
    /// <summary>Standard output followed by standard error.</summary>
    public string Output => Stderr.Length == 0 ? Stdout : Stdout + Stderr;
    public override string ToString() => $"exit code {ExitCode}\n{Output}";
}

/// <summary>
/// A Lean project directory: `.lean` files whose module names are their paths relative to
/// <see cref="SourceDirectory"/> (`Demo/Basic.lean` is `Demo.Basic`). Modules of the project
/// imported by a file are compiled to <see cref="OutputDirectory"/> before the file is run (and
/// recompiled when their sources change). All commands run inside the current process; the
/// working directory and environment of the host process are not modified.
/// </summary>
/// <example>
/// <code>
/// LeanSysroot.Root = "/path/to/lean-sysroot";      // lib/lean/*.olean, *.ir
/// var project = new LeanProject("/src/MyProject");
/// LeanResult r = project.RunFile("Scratch.lean");  // lean Scratch.lean
/// Console.WriteLine(r.ExitCode + ": " + r.Output);
/// </code>
/// </example>
public sealed class LeanProject
{
    /// <summary>Absolute path of the project directory (the working directory of all commands).</summary>
    public string Directory { get; }

    /// <summary>Root of the module hierarchy (default: <see cref="Directory"/>).</summary>
    public string SourceDirectory { get; set; }

    /// <summary>Where compiled modules (`.olean`, `.ilean`) are written (default: `.lean-interpreter` in the project directory).</summary>
    public string OutputDirectory { get; set; }

    /// <summary>Extra environment variables for commands (e.g. `LEAN_PATH` for more library directories).</summary>
    public Dictionary<string, string> Environment { get; } = new();

    public LeanProject(string directory)
    {
        Directory = Path.GetFullPath(directory);
        if (!System.IO.Directory.Exists(Directory))
            throw new DirectoryNotFoundException(Directory);
        SourceDirectory = Directory;
        OutputDirectory = Path.Combine(Directory, ".lean-interpreter");
    }

    /// <summary>`lean [args] file`: elaborates a file of the project (after compiling the project modules it imports).</summary>
    public LeanResult RunFile(string file, params string[] leanArgs)
    {
        var build = BuildImportsOf(file);
        if (build != null && !build.Success) return build;
        return Lean(leanArgs.Append(file).ToArray());
    }

    /// <summary>Same as <see cref="RunFile"/>.</summary>
    public LeanResult CheckFile(string file, params string[] leanArgs) => RunFile(file, leanArgs);

    /// <summary>`lean --run file [programArgs]`: runs the `main` function of a file with the interpreter.</summary>
    public LeanResult RunMain(string file, params string[] programArgs)
    {
        var build = BuildImportsOf(file);
        if (build != null && !build.Success) return build;
        return Lean(new[] { "--run", file }.Concat(programArgs).ToArray());
    }

    /// <summary>
    /// Compiles the given files (default: all `.lean` files under <see cref="SourceDirectory"/>)
    /// and the project modules they import, in dependency order; up-to-date modules are skipped.
    /// Stops at the first module that fails and returns its result.
    /// </summary>
    public LeanResult Build(params string[] files)
    {
        if (files.Length == 0)
            files = System.IO.Directory.EnumerateFiles(SourceDirectory, "*.lean", SearchOption.AllDirectories)
                .Where(f => !Path.GetRelativePath(SourceDirectory, f).Split(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar)
                    .Any(p => p.StartsWith('.')))
                .ToArray();
        var roots = new List<string>();
        foreach (var f in files)
        {
            var m = ModuleOfFile(Path.GetFullPath(f, Directory));
            if (m == null) return new LeanResult(1, "", $"error: '{f}' is not a file under the source directory '{SourceDirectory}'\n");
            roots.Add(m);
        }
        return BuildModules(roots);
    }

    /// <summary>Runs `lean` with arbitrary arguments in the project directory (compiled project modules on the search path).</summary>
    public LeanResult Lean(params string[] args) => Run(args, null);

    /// <summary>Runs `lean` with arbitrary arguments, feeding <paramref name="stdin"/> to its standard input (e.g. with `--stdin`).</summary>
    public LeanResult LeanWithInput(string stdin, params string[] args) => Run(args, stdin);

    // ------------------------------------------------------------------
    // Building project modules

    static readonly Dictionary<string, object> s_buildLocks = new(StringComparer.OrdinalIgnoreCase);

    string FileOfModule(string module) => Path.Combine(SourceDirectory, Path.Combine(module.Split('.'))) + ".lean";
    string OleanOfModule(string module) => Path.Combine(OutputDirectory, Path.Combine(module.Split('.'))) + ".olean";

    string ModuleOfFile(string fullPath)
    {
        var rel = Path.GetRelativePath(SourceDirectory, fullPath);
        if (rel.StartsWith("..") || Path.IsPathRooted(rel) || !rel.EndsWith(".lean", StringComparison.Ordinal)) return null;
        return string.Join('.', rel[..^".lean".Length].Split(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar));
    }

    /// <summary>Compiles the project modules imported by `file` (null if there are none).</summary>
    LeanResult BuildImportsOf(string file)
    {
        var full = Path.GetFullPath(file, Directory);
        if (!File.Exists(full)) return null; // let `lean` report it
        var imports = ReadImports(new[] { full }, out var error);
        if (error != null) return error;
        var local = imports[full].Where(m => File.Exists(FileOfModule(m))).ToList();
        return local.Count == 0 ? null : BuildModules(local);
    }

    LeanResult BuildModules(List<string> roots)
    {
        object gate;
        lock (s_buildLocks)
        {
            if (!s_buildLocks.TryGetValue(OutputDirectory, out gate)) s_buildLocks[OutputDirectory] = gate = new object();
        }
        lock (gate)
        {
            // dependency graph of the project modules reachable from `roots`
            var deps = new Dictionary<string, List<string>>(StringComparer.Ordinal);
            var todo = new Queue<string>(roots);
            while (todo.Count > 0)
            {
                var batch = new List<string>();
                while (todo.Count > 0)
                {
                    var m = todo.Dequeue();
                    if (!deps.ContainsKey(m) && !batch.Contains(m)) batch.Add(m);
                }
                if (batch.Count == 0) break;
                var files = batch.Select(FileOfModule).ToArray();
                var imports = ReadImports(files, out var error);
                if (error != null) return error;
                for (int i = 0; i < batch.Count; i++)
                {
                    var local = imports[files[i]].Where(m => File.Exists(FileOfModule(m))).Distinct().ToList();
                    deps[batch[i]] = local;
                    foreach (var d in local) if (!deps.ContainsKey(d)) todo.Enqueue(d);
                }
            }
            // compile in dependency order
            var order = new List<string>();
            var state = new Dictionary<string, int>(StringComparer.Ordinal);
            string cycle = null;
            void Visit(string m)
            {
                if (cycle != null) return;
                state.TryGetValue(m, out int s);
                if (s == 2) return;
                if (s == 1) { cycle = m; return; }
                state[m] = 1;
                foreach (var d in deps[m]) Visit(d);
                state[m] = 2;
                order.Add(m);
            }
            foreach (var r in roots) Visit(r);
            if (cycle != null) return new LeanResult(1, "", $"error: import cycle involving module '{cycle}'\n");
            var stdout = new StringBuilder();
            var stderr = new StringBuilder();
            foreach (var m in order)
            {
                var src = FileOfModule(m);
                var olean = OleanOfModule(m);
                var built = File.Exists(olean) ? File.GetLastWriteTimeUtc(olean) : DateTime.MinValue;
                if (built >= File.GetLastWriteTimeUtc(src) && deps[m].All(d => File.GetLastWriteTimeUtc(OleanOfModule(d)) <= built))
                    continue;
                System.IO.Directory.CreateDirectory(Path.GetDirectoryName(olean));
                var r = Run(new[] { "--root=" + SourceDirectory, "-o", olean, "-i", Path.ChangeExtension(olean, ".ilean"), src }, null);
                stdout.Append(r.Stdout);
                stderr.Append(r.Stderr);
                if (!r.Success)
                {
                    try { File.Delete(olean); } catch (IOException) { }
                    return new LeanResult(r.ExitCode, stdout.ToString(), stderr.ToString());
                }
            }
            return new LeanResult(0, stdout.ToString(), stderr.ToString());
        }
    }

    /// <summary>The modules imported by each file (`lean --deps-json`).</summary>
    Dictionary<string, List<string>> ReadImports(string[] files, out LeanResult error)
    {
        error = null;
        var r = Run(new[] { "--deps-json" }.Concat(files).ToArray(), null);
        var result = new Dictionary<string, List<string>>(StringComparer.OrdinalIgnoreCase);
        if (!r.Success) { error = r; return result; }
        using var doc = JsonDocument.Parse(r.Stdout);
        var items = doc.RootElement.GetProperty("imports");
        int i = 0;
        foreach (var item in items.EnumerateArray())
        {
            var errors = item.GetProperty("errors");
            if (errors.GetArrayLength() > 0)
            {
                error = new LeanResult(1, "", string.Join("\n", errors.EnumerateArray().Select(e => e.GetString())) + "\n");
                return result;
            }
            var mods = new List<string>();
            foreach (var imp in item.GetProperty("result").GetProperty("imports").EnumerateArray())
                mods.Add(imp.GetProperty("module").GetString());
            result[files[i++]] = mods;
        }
        return result;
    }

    // ------------------------------------------------------------------
    // Running `lean`

    /// <summary>
    /// Runs `lean` in the project directory. <paramref name="onOutputLine"/>, if given, receives
    /// every line of standard output and standard error as it is produced (from two reader threads).
    /// </summary>
    internal LeanResult Run(string[] args, string stdin, Action<string> onOutputLine = null)
    {
        LeanHost.RunWithLargeStack(() => { LeanHost.Initialize(); return 0; });
        var env = new Dictionary<string, string>(Environment);
        // compiled project modules come first on the search path
        var leanPath = OutputDirectory;
        if (env.TryGetValue("LEAN_PATH", out var extra) && !string.IsNullOrEmpty(extra))
            leanPath += Path.PathSeparator + extra;
        env["LEAN_PATH"] = leanPath;
        var req = new SpawnRequest
        {
            Cmd = LeanSysroot.LeanExe,
            Args = args,
            Cwd = Directory,
            Env = env.ToList(),
            Stdin = stdin == null ? LeanStdioMode.Null : LeanStdioMode.Piped,
            Stdout = LeanStdioMode.Piped,
            Stderr = LeanStdioMode.Piped,
        };
        var child = LeanProcess.Spawn(req);
        string so = "", se = "";
        var t1 = new Thread(() => so = ReadAll(child.StdoutPipe, onOutputLine));
        var t2 = new Thread(() => se = ReadAll(child.StderrPipe, onOutputLine));
        t1.Start(); t2.Start();
        if (stdin != null)
        {
            using var w = child.StdinPipe;
            var bytes = Encoding.UTF8.GetBytes(stdin);
            w.Write(bytes, 0, bytes.Length);
        }
        int code = child.WaitForExit();
        t1.Join(); t2.Join();
        return new LeanResult(code, so, se);
    }

    static string ReadAll(Stream s, Action<string> onLine)
    {
        if (s == null) return "";
        if (onLine == null)
        {
            using var ms = new MemoryStream();
            s.CopyTo(ms);
            return Encoding.UTF8.GetString(ms.ToArray());
        }
        var sb = new StringBuilder();
        using var r = new StreamReader(s, new UTF8Encoding(false));
        string line;
        while ((line = r.ReadLine()) != null)
        {
            sb.Append(line).Append('\n');
            lock (onLine) onLine(line);
        }
        return sb.ToString();
    }
}
