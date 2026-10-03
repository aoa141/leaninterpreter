# LeanInterpreter

Run [Lean 4](https://github.com/leanprover/lean4) from C# with nothing but one managed assembly:
`LeanInterpreter.dll` (≈600 KB, .NET 10, no dependencies, no native code, no code generation).

It is a stripped-down sibling of LeanSharp. LeanSharp translates Lean's standard library
(`Init`, `Std`, `Lean`) to 12.8M lines of C# and compiles them into a 170 MB assembly.
LeanInterpreter keeps only LeanSharp's hand-ported runtime (object model, kernel, `.olean`
reader/writer, tasks, IO) and adds an IR interpreter that runs **Lean's own elaborator** from the
IR stored in the sysroot's `.ir` files, the way `lean` interprets user code for `#eval`.

## Usage

```csharp
using LeanInterpreter;

LeanSysroot.Root = @"C:\lean-sysroot";          // contains lib/lean/*.olean, *.ir
var project = new LeanProject(@"C:\src\MyProject");

LeanResult r = project.RunFile("Scratch.lean");  // lean Scratch.lean
Console.WriteLine(r.ExitCode);                   // 0 = no errors
Console.WriteLine(r.Output);                     // messages, #eval/#check output

LeanResult m = project.RunMain("Main.lean", "a", "b");   // lean --run Main.lean a b
```

`LeanProject`:

| Member | Does |
|---|---|
| `RunFile(file, leanArgs...)` / `CheckFile` | Elaborates a file (`lean file`) |
| `RunMain(file, args...)` | Runs `main` with the interpreter (`lean --run file args`) |
| `Build(files...)` | Compiles project modules to `.olean` (default: all `.lean` files) |
| `Lean(args...)`, `LeanWithInput(stdin, args...)` | Any `lean` command line |
| `Environment` | Extra environment variables (e.g. `LEAN_PATH`) |
| `SourceDirectory`, `OutputDirectory` | Module root (default: the project directory), output for compiled modules (default: `.lean-interpreter/`) |

Imports between the files of a project just work. Before a file is run, the project modules it
imports (`import Demo.Basic` → `Demo/Basic.lean`) are compiled in dependency order into
`OutputDirectory`, and recompiled when their sources change. Lake is not involved: `lakefile`s
are ignored.

Each run is isolated from the others. It gets a fresh *logical process* (working directory,
environment variables, and the global state of the Lean libraries), so runs can execute
concurrently on different threads. The host process's working directory and environment are
never modified. The first run in a process loads and initializes the libraries (≈1.7 s); later
runs reuse them.

## The sysroot

The assembly contains no Lean library code. It reads the library from a sysroot. Only
`lib/lean/` is used, and only the `.olean`, `.olean.server`, `.olean.private`, `.ir` and `.ir.sig`
files of `Init`, `Std` and `Lean` (≈2 GB, 12k files). The version must be **Lean 4.36.0-pre,
commit `77f336f7ae`**, the version the runtime was ported from. Possible sources:

* the sysroot built by LeanSharp (`LeanSharp.Cli build-stdlib <lean4/src> <dir>`);
* the `lib/lean` directory of a native Lean build of that commit.

To make a trimmed copy for another machine or repository:

```csharp
LeanSysroot.CopyLibrary(@"C:\repos\leansharp\artifacts\selfhost", @"C:\work\lean-sysroot");
```

If `LeanSysroot.Root` is not set, `LEAN_SYSROOT` is used, then `lean-sysroot` next to the
assembly.

## How it works

| | |
|---|---|
| `src/LeanInterpreter/Runtime` | Copied from LeanSharp's hand-ported runtime: object model, `lean.h` functions, bignums, strings, IO, tasks, the kernel (type checker), `.olean` compaction. CaDiCaL, libuv and LLVM bindings were left out. |
| `Interp/Library.cs` | Loads the module data of `Init`/`Std`/`Lean`: IR declarations (`Lean.IR.declMapExt` entries of the `.ir` files), `@[export]` names, and `[builtin_init]`/`[init]` declarations. Then it does what `lean_initialize()` does natively: it runs every module's initializers in import order and declaration order. Closed terms and other constants are evaluated on first use. |
| `Interp/Fn.cs`, `Interp/Machine.cs` | The interpreter. An IR declaration is translated, on first call, into a graph of nodes (variables become frame slots, join points become direct references, callees are resolved once). This graph is executed on a segmented value stack. Closures of interpreted functions are ordinary runtime closures pointing to stubs. |
| `Interp/ExternTable.g.cs` | `@[extern]` declarations → runtime functions (generated from the IR's extern symbols and the runtime's signatures). Externs implemented in Lean (`@[extern "lean_whnf"]` + `@[export lean_whnf]`) are forwarded to their IR. |
| `Interp/ExportStubs.g.cs` | The `@[export]` functions the runtime and kernel call (`lean_expr_mk_app`, `lean_shell_main`, …), each running its declaration in the interpreter. |
| `Interp/Session.cs` | Code from a program's environment (`#eval`, macros, `initialize`, `--run`), looked up with `Lean.IR.findEnvDecl`. |
| `Host/` | `LeanHost` (startup), `LeanShell` (the `lean` command line), `LeanProject` (the API above). |
| `tools/GenTables` | Regenerates the two `.g.cs` tables from a sysroot (only needed for another Lean version). |

To use it in another solution, copy `src/LeanInterpreter/` and add a project reference. The
project file carries all of its build settings.

Lean's frontend calls `runModInitCore` for the library modules, and these are reported as already
initialized. From Lean's point of view the interpreted library therefore looks exactly like the
native, linked one.

## Status

* Elaboration, tactics (`decide`, `omega`, `simp`, `grind`, …), `#eval`, `#check`, user
  macros/elaborators/`initialize`, `import Lean` metaprogramming, `lean --run`, `--stdin`,
  `-o`/`-i` (writing `.olean`/`.ilean`), multi-file projects.
* Lean's `tests/elab` pile passes almost completely; see "Lean test suite" below.
* Not included (to stay small): `bv_decide`'s SAT solver (CaDiCaL), the libuv-based `Std.Async`
  (timers, TCP/UDP, DNS), LLVM, native dynamic libraries/plugins, Lake. Calling one of these
  reports an error such as "no implementation of the external declaration …". CaDiCaL and libuv
  can be copied back from LeanSharp (`src/LeanSharp.Runtime/{Cadical,Uv}`). After that,
  regenerate the tables, and for CaDiCaL add a spawn hook for `cadical`.
* The language server (`lean --server`) is interpreted like everything else but untested.
* `Lean.manualRoot` (from `LEAN_MANUAL_ROOT`) is computed once per process.

### Performance

Measured on a 24-core Windows machine with server GC:

| | first run in a process | later runs |
|---|---|---|
| library startup (once per process) | 1.7 s | – |
| small file (`decide`, `omega`, `#eval`, `#check`) | 1.7 s | ≈1 s |
| `import Lean` + one command | 5 s | ≈4 s |

For reference, LeanSharp's notes give 1.2 s for a one-line file and 3.7 s for `import Lean` with
native `lean`. The first run that imports a library module pays a one-time cost: decoding that module's data
from the `.olean` files into managed objects, and compiling the IR of the functions it uses.
Later runs in the same process share all of this. The managed heap holds about 0.5 GB after a
small file and 0.7 GB after `import Lean`. The library files are memory-mapped.

**Use server GC in the host process.** The interpreter allocates heavily and the heap holds
millions of library objects. With workstation GC the same work takes about 1.5× as long. In the
host's `.csproj`:

```xml
<ServerGarbageCollection>true</ServerGarbageCollection>
<ConcurrentGarbageCollection>true</ConcurrentGarbageCollection>
```

### Lean test suite

Lean's `tests/elab` pile has 3,295 tests. Every one passes with exact expected output, except
those that need the components left out: 41 use `bv_decide`/CaDiCaL, 39 use libuv
(`Std.Async`: timers, sockets, DNS), and 1 depends on `LEAN_MANUAL_ROOT` per program.

### Diagnostics

Environment variables: `LEAN_INTERP_TRACE_STARTUP=1` (startup timing), `LEAN_INTERP_DEBUG=1`
(exceptions that end a program), `LEAN_INTERP_PROFILE=1` (calls and executed IR nodes per
function, printed at exit).

## Tests

```sh
LEAN_SYSROOT=/path/to/sysroot dotnet test tests/LeanInterpreter.Tests -c Release
```

## Third-party code

The runtime derives from LeanSharp's port of the Lean 4 runtime and kernel (Apache-2.0,
https://github.com/leanprover/lean4).
