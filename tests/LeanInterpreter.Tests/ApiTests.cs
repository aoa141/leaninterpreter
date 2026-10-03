// End-to-end tests of the public API: every test runs Lean in-process through `LeanProject`,
// with the Lean libraries interpreted.

using LeanInterpreter;
using Xunit;

namespace LeanInterpreter.Tests;

/// <summary>Locates the sysroot and creates scratch project directories.</summary>
public sealed class LeanFixture : IDisposable
{
    public string Root { get; }
    public string SkipReason { get; }

    public LeanFixture()
    {
        string sysroot = Environment.GetEnvironmentVariable("LEAN_SYSROOT");
        if (string.IsNullOrEmpty(sysroot) || !File.Exists(Path.Combine(sysroot, "lib", "lean", "Init.olean")))
            SkipReason = "no Lean sysroot: set LEAN_SYSROOT to a directory with lib/lean/Init.olean";
        else
            LeanSysroot.Root = sysroot;
        Root = Path.Combine(Path.GetTempPath(), "leaninterpreter-tests-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(Root);
    }

    public LeanProject NewProject(params (string path, string text)[] files)
    {
        var dir = Path.Combine(Root, Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(dir);
        foreach (var (path, text) in files)
        {
            var full = Path.Combine(dir, path);
            Directory.CreateDirectory(Path.GetDirectoryName(full));
            File.WriteAllText(full, text);
        }
        return new LeanProject(dir);
    }

    public void Dispose()
    {
        try { Directory.Delete(Root, true); } catch { }
    }
}

public class ApiTests : IClassFixture<LeanFixture>
{
    readonly LeanFixture m_fx;
    public ApiTests(LeanFixture fx) => m_fx = fx;

    [SkippableFact]
    public void Version()
    {
        Skip.If(m_fx.SkipReason != null, m_fx.SkipReason);
        var r = m_fx.NewProject().Lean("--version");
        Assert.Equal(0, r.ExitCode);
        Assert.StartsWith("Lean (version 4.", r.Stdout);
    }

    [SkippableFact]
    public void ElaboratesDefinitionsTheoremsAndEval()
    {
        Skip.If(m_fx.SkipReason != null, m_fx.SkipReason);
        var p = m_fx.NewProject(("T.lean", """
            def fib : Nat → Nat | 0 => 0 | 1 => 1 | n+2 => fib n + fib (n+1)
            theorem fib10 : fib 10 = 55 := by decide
            theorem add_comm' (a b : Nat) : a + b = b + a := by omega
            #eval fib 20
            #check fib10
            """));
        var r = p.RunFile("T.lean");
        Assert.Equal(0, r.ExitCode);
        Assert.Equal("6765\nfib10 : fib 10 = 55\n", r.Stdout);
    }

    [SkippableFact]
    public void ReportsErrorsWithExitCode1()
    {
        Skip.If(m_fx.SkipReason != null, m_fx.SkipReason);
        var p = m_fx.NewProject(("Bad.lean", "theorem wrong : 1 = 2 := rfl\n"));
        var r = p.RunFile("Bad.lean");
        Assert.Equal(1, r.ExitCode);
        Assert.Contains("Bad.lean:1:25: error", r.Output);
    }

    [SkippableFact]
    public void RunsMainWithTheInterpreter()
    {
        Skip.If(m_fx.SkipReason != null, m_fx.SkipReason);
        var p = m_fx.NewProject(("Main.lean", """
            def main (args : List String) : IO UInt32 := do
              IO.println s!"hello {args}"
              return 7
            """));
        var r = p.RunMain("Main.lean", "a", "b");
        Assert.Equal("hello [a, b]\n", r.Stdout);
        Assert.Equal(7, r.ExitCode);
    }

    [SkippableFact]
    public void ReadsStandardInput()
    {
        Skip.If(m_fx.SkipReason != null, m_fx.SkipReason);
        var r = m_fx.NewProject().LeanWithInput("#eval 1 + 1\n", "--stdin");
        Assert.Equal("2\n", r.Stdout);
    }

    [SkippableFact]
    public void MetaprogrammingWithImportLean()
    {
        Skip.If(m_fx.SkipReason != null, m_fx.SkipReason);
        var p = m_fx.NewProject(("M.lean", """
            import Lean
            open Lean Elab Command Meta
            elab "#hello" : command => logInfo "hello from a user elaborator"
            #hello
            #eval show MetaM Unit from do
              let e ← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 3]
              IO.println s!"{← ppExpr (← whnf e)}"
            """));
        var r = p.RunFile("M.lean");
        Assert.True(r.Success, r.Output);
        Assert.Equal("hello from a user elaborator\n5\n", r.Stdout);
    }

    [SkippableFact]
    public void CompilesImportedProjectModules()
    {
        Skip.If(m_fx.SkipReason != null, m_fx.SkipReason);
        var p = m_fx.NewProject(
            ("Demo.lean", "import Demo.Basic\nimport Demo.Thm\n"),
            ("Demo/Basic.lean", "def double (n : Nat) : Nat := n + n\n"),
            ("Demo/Thm.lean", "import Demo.Basic\ntheorem double_eq (n : Nat) : double n = 2 * n := by unfold double; omega\n"),
            ("Scratch.lean", "import Demo\n#check double_eq\n#eval double 21\n"));
        var r = p.RunFile("Scratch.lean");
        Assert.True(r.Success, r.Output);
        Assert.Equal("double_eq (n : Nat) : double n = 2 * n\n42\n", r.Stdout);
        var thm = Path.Combine(p.OutputDirectory, "Demo", "Thm.olean");
        Assert.True(File.Exists(thm));

        // nothing to do the second time
        var t = File.GetLastWriteTimeUtc(thm);
        var again = p.Build();
        Assert.True(again.Success, again.Output);
        Assert.Equal(t, File.GetLastWriteTimeUtc(thm));

        // a changed dependency is recompiled, and so is what imports it
        File.WriteAllText(Path.Combine(p.Directory, "Demo", "Basic.lean"), "def double (n : Nat) : Nat := 2 * n\n");
        File.SetLastWriteTimeUtc(Path.Combine(p.Directory, "Demo", "Basic.lean"), DateTime.UtcNow.AddSeconds(5));
        var changed = p.RunFile("Scratch.lean");
        Assert.True(changed.Success, changed.Output);
        Assert.True(File.GetLastWriteTimeUtc(thm) > t);
    }

    [SkippableFact]
    public void BuildFailsOnAnError()
    {
        Skip.If(m_fx.SkipReason != null, m_fx.SkipReason);
        var p = m_fx.NewProject(
            ("Bad.lean", "example : False := trivial\n"),
            ("Use.lean", "import Bad\n"));
        var r = p.RunFile("Use.lean");
        Assert.False(r.Success);
        Assert.Contains("Bad.lean:1:19: error", r.Output);
    }

    [SkippableFact]
    public void ProgramsDoNotShareWorkingDirectoryEnvironmentOrGlobalState()
    {
        Skip.If(m_fx.SkipReason != null, m_fx.SkipReason);
        // each file registers the same option: with shared global state the second one would fail
        const string text = """
            import Lean
            register_option leaninterp.test.opt : Nat := { defValue := 1, descr := "test" }
            #eval do IO.println (← IO.currentDir).fileName.get!.length
            #eval show IO Unit from do IO.println ((← IO.getEnv "LEANINTERP_TEST_VAR").getD "unset")
            """;
        var p1 = m_fx.NewProject(("A.lean", text));
        var p2 = m_fx.NewProject(("A.lean", text));
        p1.Environment["LEANINTERP_TEST_VAR"] = "one";
        LeanResult r1 = null, r2 = null;
        var t1 = new Thread(() => r1 = p1.RunFile("A.lean"));
        var t2 = new Thread(() => r2 = p2.RunFile("A.lean"));
        t1.Start(); t2.Start(); t1.Join(); t2.Join();
        Assert.True(r1.Success && r2.Success, r1.Output + "\n--\n" + r2.Output);
        Assert.Equal("32\none\n", r1.Stdout + r1.Stderr);
        Assert.Equal("32\nunset\n", r2.Stdout + r2.Stderr);
        Assert.Equal(Environment.CurrentDirectory, Directory.GetCurrentDirectory());
    }
}
