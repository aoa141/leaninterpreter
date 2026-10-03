// Interpreted functions and their compiled form.
//
// An IR declaration (`Lean.IR.Decl`) is translated, on its first call, into a graph of `Node`s:
// variables become slots of a frame (parameters first), join points become direct references to
// their bodies, callees are resolved to `Fn` objects once, and literals are decoded. `Machine`
// executes this graph. Nothing is generated at run time; the interpreter only walks objects.

using System.Runtime.CompilerServices;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Interp;

/// <summary>Where the callees of a function are looked up: the library (Init/Std/Lean, loaded from
/// the sysroot) or a session (the environment of a program being elaborated).</summary>
internal abstract class Scope
{
    public abstract Fn Resolve(Obj name);
}

/// <summary>Target of a call of an `@[extern]` declaration.</summary>
internal sealed class ExternTarget
{
    /// <summary>`delegate*&lt;Value[] frame, int base, int[] slots, Value&gt;` taking the non-erased,
    /// non-`void` arguments from the given slots of the caller's frame.</summary>
    public nint Fn;
    /// <summary>Indices of the IR parameters passed to <see cref="Fn"/>.</summary>
    public int[] Live;
    /// <summary>The extern is implemented in Lean (`@[export sym]` elsewhere): call this function instead.</summary>
    public Fn Forward;
    /// <summary>For <see cref="Forward"/>: for each parameter of the target, the IR parameter of the extern passed to it (-1: `void`).</summary>
    public int[] ForwardMap;
    public string Symbol;
}

internal sealed unsafe class Fn
{
    public readonly Obj Name;
    public readonly Obj Decl;
    public readonly Scope Scope;
    public readonly int Arity;
    public readonly IrType[] ParamTypes;
    public readonly bool[] ParamBorrow;
    public readonly IrType RetType;
    public readonly bool IsExtern;
    public readonly bool HasScalarParams, HasBorrowedParams;
    /// <summary>Persistent object standing for this function in closures.</summary>
    public readonly Obj Handle;

    /// <summary>Compiled body (null until the first call).</summary>
    public Node Body;
    public int FrameSize;
    public ExternTarget Extern;

    /// <summary>Constants (nullary functions): 0 = not evaluated, 1 = being initialized by its `[init]` function, 2 = done.</summary>
    public int ConstState;
    public Value ConstVal;
    /// <summary>Library constants with an `[init]`/`[builtin_init]` function.</summary>
    public Obj InitFn;

    /// <summary>Profiling counters (LEAN_INTERP_PROFILE=1).</summary>
    public long Calls, Nodes;

    string m_str;
    public string Str => m_str ??= IrName.ToString(Name);
    public override string ToString() => Str;

    static readonly ExternalClass s_handleClass = new(null, null);

    public Fn(Obj name, Obj decl, Scope scope)
    {
        Name = name;
        Decl = decl;
        Scope = scope;
        Obj ps = Ir.DeclParams(decl);
        Arity = Ir.Size(ps);
        ParamTypes = new IrType[Arity];
        ParamBorrow = new bool[Arity];
        for (int i = 0; i < Arity; i++)
        {
            Obj p = Ir.At(ps, i);
            ParamTypes[i] = Ir.ParamType(p);
            ParamBorrow[i] = Ir.ParamBorrow(p);
            if (Ir.IsScalar(ParamTypes[i])) HasScalarParams = true;
            else if (ParamBorrow[i]) HasBorrowedParams = true;
        }
        RetType = Ir.DeclType(decl);
        IsExtern = Ir.DeclTag(decl) == Ir.DeclExtern;
        Handle = new ExternalObj { m_rc = 0, m_tag = (byte)LeanExternal, m_class = s_handleClass, m_data = this };
        if (Profiler.Enabled) Profiler.Register(this);
    }

    public static Fn OfHandle(Obj h) => (Fn)Unsafe.As<ExternalObj>(h).m_data;

    /// <summary>Compiles the body if necessary (thread-safe; callees are resolved, not compiled).</summary>
    public Node EnsureCompiled()
    {
        var b = Volatile.Read(ref Body);
        if (b != null) return b;
        lock (this)
        {
            if (Body != null) return Body;
            if (IsExtern) throw new InterpreterException($"(interpreter) '{Str}' is an external declaration");
            long t0 = Profiler.Enabled ? System.Diagnostics.Stopwatch.GetTimestamp() : 0;
            var c = new Compiler(this);
            b = c.CompileBody(Ir.DeclBody(Decl));
            if (Profiler.Enabled) { Interlocked.Add(ref Profiler.CompileTicks, System.Diagnostics.Stopwatch.GetTimestamp() - t0); Interlocked.Increment(ref Profiler.Compiled); }
            FrameSize = Math.Max(Math.Max(c.FrameSize, Arity), 1);
            Volatile.Write(ref Body, b);
            return b;
        }
    }

    public bool BodyIsUnreachable => !IsExtern && Ir.BodyTag(Ir.DeclBody(Decl)) == FnBodyKind.Unreachable;
}

// ----------------------------------------------------------------------
// Nodes

internal enum Op : byte
{
    Ctor, Reset, Reuse, Proj, UProj, SProj, Call, CallExt, TailCall, Const, PAp, Ap, Box, Unbox, LitObj, LitNum,
    IsShared, Set, SetTag, USet, SSet, Inc, Dec, Del, Case, Ret, Jmp, Unreachable
}

internal class Node
{
    public Op Op;
    public Node Next;
    /// <summary>Destination slot of the value computed by the node (if any).</summary>
    public int Dst;
}

internal sealed class NCtor : Node { public uint Tag, NumObjs, ScalarSz; public int[] Args; }
internal sealed class NReset : Node { public int X; public uint N; }
internal sealed class NReuse : Node { public int X; public uint Tag, NumObjs, ScalarSz; public bool UpdtHeader; public int[] Args; }
internal sealed class NProj : Node { public int X; public uint I; }
internal sealed class NSProj : Node { public int X; public uint Offset; public IrType Ty; }
internal sealed class NCall : Node { public Fn Target; public int[] Args; }
internal sealed class NCallExt : Node { public nint Ext; public int[] Args; public string Symbol; public Fn Decl; public long Hits; }
internal sealed class NTail : Node { public int[] Args; public bool NeedsTemp; }
internal sealed class NConst : Node { public Fn Target; }
internal sealed class NPAp : Node { public Fn Target; public int[] Args; }
internal sealed class NAp : Node { public int F; public int[] Args; }
internal sealed class NBox : Node { public int X; public IrType Ty; }
internal sealed class NLit : Node { public Value V; }
internal sealed class NUnary : Node { public int X; public IrType Ty; }
internal sealed class NSet : Node { public int X; public uint I; public int Y; public IrType Ty; }
internal sealed class NIncDec : Node { public int X; public uint N; }
internal sealed class NCase : Node { public int X; public bool Scalar; public Node[] Table; public Node Default; }
internal sealed class NRet : Node { public int X; }
internal sealed class NJmp : Node { public JoinPoint Jp; public int[] Args; public bool NeedsTemp; }
internal sealed class NUnreachable : Node { public string Fn; }

internal sealed class JoinPoint
{
    public int[] Params;
    public Node Body;
}

// ----------------------------------------------------------------------
// IR -> nodes

internal sealed class Compiler
{
    readonly Fn m_fn;
    readonly Dictionary<int, int> m_slots = new();
    int m_next;

    sealed class JpEnv
    {
        public int Idx; public JoinPoint Jp; public JpEnv Next;
    }

    public Compiler(Fn fn)
    {
        m_fn = fn;
        Obj ps = Ir.DeclParams(fn.Decl);
        for (int i = 0; i < fn.Arity; i++) Slot(Ir.ParamVar(Ir.At(ps, i)));
    }

    public int FrameSize => m_next;

    int Slot(Obj var)
    {
        int idx = Ir.Idx(var);
        if (!m_slots.TryGetValue(idx, out int s))
        {
            s = m_next++;
            m_slots[idx] = s;
        }
        return s;
    }

    int Arg(Obj a) => Ir.ArgIsErased(a) ? -1 : Slot(Ir.ArgVar(a));

    int[] Args(Obj arr)
    {
        int n = Ir.Size(arr);
        var r = new int[n];
        for (int i = 0; i < n; i++) r[i] = Arg(Ir.At(arr, i));
        return r;
    }

    public Node CompileBody(Obj b) => Body(b, null);

    Node Body(Obj b, JpEnv jps)
    {
        Node head = null, tail = null;
        void Link(Node n)
        {
            if (tail == null) head = n; else tail.Next = n;
            tail = n;
        }
        while (true)
        {
            switch (Ir.BodyTag(b))
            {
                case FnBodyKind.VDecl:
                {
                    Obj x = Ir.F(b, 0), ty = Ir.F(b, 1), e = Ir.F(b, 2), cont = Ir.F(b, 3);
                    if (Ir.ExprTag(e) == ExprKind.FAp && Ir.BodyTag(cont) == FnBodyKind.Ret && Ir.Size(Ir.F(e, 1)) > 0)
                    {
                        Obj r = Ir.F(cont, 0);
                        if (!Ir.ArgIsErased(r) && Ir.Idx(Ir.ArgVar(r)) == Ir.Idx(x) && IrName.Eq(Ir.F(e, 0), m_fn.Name))
                        {
                            var args = Args(Ir.F(e, 1));
                            Link(new NTail { Op = Op.TailCall, Args = args, NeedsTemp = NeedsTemp(args, Identity(args.Length)) });
                            return head;
                        }
                    }
                    Link(Expr(Slot(x), Ir.ToType(ty), e));
                    b = cont;
                    break;
                }
                case FnBodyKind.JDecl:
                {
                    Obj xs = Ir.F(b, 1);
                    int n = Ir.Size(xs);
                    var jp = new JoinPoint { Params = new int[n] };
                    for (int i = 0; i < n; i++) jp.Params[i] = Slot(Ir.ParamVar(Ir.At(xs, i)));
                    jp.Body = Body(Ir.F(b, 2), jps);
                    jps = new JpEnv { Idx = Ir.Idx(Ir.F(b, 0)), Jp = jp, Next = jps };
                    b = Ir.F(b, 3);
                    break;
                }
                case FnBodyKind.Set:
                    Link(new NSet { Op = Op.Set, X = Slot(Ir.F(b, 0)), I = (uint)Ir.Idx(Ir.F(b, 1)), Y = Arg(Ir.F(b, 2)) });
                    b = Ir.F(b, 3);
                    break;
                case FnBodyKind.SetTag:
                    Link(new NSet { Op = Op.SetTag, X = Slot(Ir.F(b, 0)), I = (uint)Ir.Idx(Ir.F(b, 1)) });
                    b = Ir.F(b, 2);
                    break;
                case FnBodyKind.USet:
                    Link(new NSet { Op = Op.USet, X = Slot(Ir.F(b, 0)), I = (uint)Ir.Idx(Ir.F(b, 1)), Y = Slot(Ir.F(b, 2)) });
                    b = Ir.F(b, 3);
                    break;
                case FnBodyKind.SSet:
                    Link(new NSet
                    {
                        Op = Op.SSet, X = Slot(Ir.F(b, 0)), I = (uint)(Ir.Idx(Ir.F(b, 1)) * 8 + Ir.Idx(Ir.F(b, 2))),
                        Y = Slot(Ir.F(b, 3)), Ty = Ir.ToType(Ir.F(b, 4)),
                    });
                    b = Ir.F(b, 5);
                    break;
                case FnBodyKind.Inc:
                case FnBodyKind.Dec:
                    Link(new NIncDec
                    {
                        Op = Ir.BodyTag(b) == FnBodyKind.Inc ? Op.Inc : Op.Dec,
                        X = Slot(Ir.F(b, 0)), N = (uint)Ir.Idx(Ir.F(b, 1)),
                    });
                    b = Ir.F(b, 2);
                    break;
                case FnBodyKind.Del:
                    Link(new NIncDec { Op = Op.Del, X = Slot(Ir.F(b, 0)) });
                    b = Ir.F(b, 1);
                    break;
                case FnBodyKind.Case:
                {
                    var c = new NCase { Op = Op.Case, X = Slot(Ir.F(b, 1)), Scalar = Ir.IsScalar(Ir.ToType(Ir.F(b, 2))) };
                    Obj alts = Ir.F(b, 3);
                    int n = Ir.Size(alts);
                    var cases = new List<(int tag, Node body)>();
                    for (int i = 0; i < n; i++)
                    {
                        Obj a = Ir.At(alts, i);
                        if (lean_obj_tag(a) == 0)
                            cases.Add((Ir.CtorTag(Ir.F(a, 0)), Body(Ir.F(a, 1), jps)));
                        else
                        {
                            c.Default = Body(Ir.F(a, 0), jps);
                            break;
                        }
                    }
                    int max = cases.Count == 0 ? -1 : cases.Max(t => t.tag);
                    c.Table = new Node[max + 1];
                    for (int i = cases.Count - 1; i >= 0; i--) c.Table[cases[i].tag] = cases[i].body;
                    for (int i = 0; i <= max; i++) c.Table[i] ??= c.Default;
                    Link(c);
                    return head;
                }
                case FnBodyKind.Ret:
                    Link(new NRet { Op = Op.Ret, X = Arg(Ir.F(b, 0)) });
                    return head;
                case FnBodyKind.Jmp:
                {
                    int idx = Ir.Idx(Ir.F(b, 0));
                    var env = jps;
                    while (env != null && env.Idx != idx) env = env.Next;
                    if (env == null) throw new InterpreterException($"(interpreter) unknown join point in '{m_fn.Str}'");
                    var args = Args(Ir.F(b, 1));
                    Link(new NJmp { Op = Op.Jmp, Jp = env.Jp, Args = args, NeedsTemp = NeedsTemp(args, env.Jp.Params) });
                    return head;
                }
                case FnBodyKind.Unreachable:
                    Link(new NUnreachable { Op = Op.Unreachable, Fn = m_fn.Str });
                    return head;
                default:
                    throw new InterpreterException($"(interpreter) unexpected instruction kind {(int)Ir.BodyTag(b)}");
            }
        }
    }

    static int[] Identity(int n)
    {
        var r = new int[n];
        for (int i = 0; i < n; i++) r[i] = i;
        return r;
    }

    /// <summary>Does the parallel assignment `dsts := args` need a temporary copy, i.e. does some
    /// argument read a destination that an earlier assignment overwrites?</summary>
    static bool NeedsTemp(int[] args, int[] dsts)
    {
        for (int i = 0; i < args.Length; i++)
            for (int j = 0; j < i; j++)
                if (args[i] == dsts[j] && args[j] != dsts[j]) return true;
        return false;
    }

    Node Expr(int dst, IrType ty, Obj e)
    {
        switch (Ir.ExprTag(e))
        {
            case ExprKind.Ctor:
            {
                Obj info = Ir.F(e, 0);
                int tag = Ir.CtorTag(info), size = Ir.CtorSize(info), usize = Ir.CtorUSize(info), ssize = Ir.CtorSSize(info);
                if (size == 0 && usize == 0 && ssize == 0)
                    return new NLit { Op = Op.LitNum, Dst = dst, V = Value.Of(lean_box((ulong)tag)) };
                return new NCtor
                {
                    Op = Op.Ctor, Dst = dst, Tag = (uint)tag, NumObjs = (uint)size, ScalarSz = (uint)(usize * 8 + ssize),
                    Args = Args(Ir.F(e, 1)),
                };
            }
            case ExprKind.Reset:
                return new NReset { Op = Op.Reset, Dst = dst, N = (uint)Ir.Idx(Ir.F(e, 0)), X = Slot(Ir.F(e, 1)) };
            case ExprKind.Reuse:
            {
                Obj info = Ir.F(e, 1);
                return new NReuse
                {
                    Op = Op.Reuse, Dst = dst, X = Slot(Ir.F(e, 0)), Tag = (uint)Ir.CtorTag(info), NumObjs = (uint)Ir.CtorSize(info),
                    ScalarSz = (uint)(Ir.CtorUSize(info) * 8 + Ir.CtorSSize(info)),
                    UpdtHeader = lean_ctor_get_uint8_s(e, 0) != 0, Args = Args(Ir.F(e, 2)),
                };
            }
            case ExprKind.Proj:
                return new NProj { Op = Op.Proj, Dst = dst, I = (uint)Ir.Idx(Ir.F(e, 0)), X = Slot(Ir.F(e, 1)) };
            case ExprKind.UProj:
                return new NProj { Op = Op.UProj, Dst = dst, I = (uint)Ir.Idx(Ir.F(e, 0)), X = Slot(Ir.F(e, 1)) };
            case ExprKind.SProj:
                return new NSProj
                {
                    Op = Op.SProj, Dst = dst, Offset = (uint)(Ir.Idx(Ir.F(e, 0)) * 8 + Ir.Idx(Ir.F(e, 1))), X = Slot(Ir.F(e, 2)), Ty = ty,
                };
            case ExprKind.FAp:
            {
                Fn g = m_fn.Scope.Resolve(Ir.F(e, 0));
                var args = Args(Ir.F(e, 1));
                if (args.Length == 0 && g.Arity == 0) return new NConst { Op = Op.Const, Dst = dst, Target = g };
                return Call(dst, g, args);
            }
            case ExprKind.PAp:
                return new NPAp { Op = Op.PAp, Dst = dst, Target = m_fn.Scope.Resolve(Ir.F(e, 0)), Args = Args(Ir.F(e, 1)) };
            case ExprKind.Ap:
                return new NAp { Op = Op.Ap, Dst = dst, F = Slot(Ir.F(e, 0)), Args = Args(Ir.F(e, 1)) };
            case ExprKind.Box:
                return new NBox { Op = Op.Box, Dst = dst, Ty = Ir.ToType(Ir.F(e, 0)), X = Slot(Ir.F(e, 1)) };
            case ExprKind.Unbox:
                return new NUnary { Op = Op.Unbox, Dst = dst, X = Slot(Ir.F(e, 0)), Ty = ty };
            case ExprKind.Lit:
            {
                Obj lit = Ir.F(e, 0);
                Obj v = Ir.F(lit, 0);
                if (lean_obj_tag(lit) == 0 && Ir.IsScalar(ty))
                {
                    Value n = ty switch
                    {
                        IrType.Float => Value.FromFloat(lean_is_scalar(v) ? lean_unbox(v) : (double)lean_nat_to_big(v)),
                        IrType.Float32 => Value.FromFloat32(lean_is_scalar(v) ? lean_unbox(v) : (float)lean_nat_to_big(v)),
                        _ => Value.Num(lean_is_scalar(v) ? lean_unbox(v) : (ulong)(lean_nat_to_big(v) & ulong.MaxValue)),
                    };
                    return new NLit { Op = Op.LitNum, Dst = dst, V = n };
                }
                return new NLit { Op = Op.LitObj, Dst = dst, V = Value.Of(v) };
            }
            case ExprKind.IsShared:
                return new NUnary { Op = Op.IsShared, Dst = dst, X = Slot(Ir.F(e, 0)) };
        }
        throw new InterpreterException($"(interpreter) unexpected expression kind {(int)Ir.ExprTag(e)}");
    }

    Node Call(int dst, Fn g, int[] args)
    {
        if (!g.IsExtern) return new NCall { Op = Op.Call, Dst = dst, Target = g, Args = args };
        var ext = Externs.Resolve(g);
        if (ext.Forward != null)
        {
            var map = ext.ForwardMap;
            var fargs = new int[map.Length];
            for (int i = 0; i < map.Length; i++) fargs[i] = map[i] < 0 ? -1 : args[map[i]];
            return new NCall { Op = Op.Call, Dst = dst, Target = ext.Forward, Args = fargs };
        }
        var live = new int[ext.Live.Length];
        for (int i = 0; i < live.Length; i++) live[i] = args[ext.Live[i]];
        var node = new NCallExt { Op = Op.CallExt, Dst = dst, Ext = ext.Fn, Args = live, Symbol = ext.Symbol, Decl = g };
        if (Profiler.Enabled) Profiler.Register(node);
        return node;
    }
}

/// <summary>Call and node counts per function, printed at exit (LEAN_INTERP_PROFILE=1).</summary>
internal static class Profiler
{
    public static readonly bool Enabled = Environment.GetEnvironmentVariable("LEAN_INTERP_PROFILE") == "1";
    static readonly System.Collections.Concurrent.ConcurrentBag<Fn> s_fns = new();
    static readonly System.Collections.Concurrent.ConcurrentBag<NCallExt> s_ext = new();

    public static void Register(NCallExt n) => s_ext.Add(n);
    public static readonly long[] OpCounts = new long[64];
    public static long CompileTicks, Compiled;

    public static void Register(Fn f)
    {
        if (s_fns.IsEmpty) AppDomain.CurrentDomain.ProcessExit += (_, _) => Report();
        s_fns.Add(f);
    }

    static void Report()
    {
        var fns = s_fns.Where(f => f.Nodes > 0 || f.Calls > 0).OrderByDescending(f => f.Nodes).Take(60).ToList();
        long total = s_fns.Sum(f => f.Nodes);
        var w = Console.Error;
        w.WriteLine($"[profile] {total:N0} nodes executed; {Compiled:N0} functions compiled in {CompileTicks * 1000 / System.Diagnostics.Stopwatch.Frequency:N0} ms");
        for (int i = 0; i < OpCounts.Length; i++)
            if (OpCounts[i] > 0) w.WriteLine($"[profile]   {(Op)i,-12} {OpCounts[i],15:N0}");
        foreach (var g in s_ext.GroupBy(n => n.Symbol).Select(g => (g.Key, g.Sum(n => n.Hits))).OrderByDescending(x => x.Item2).Take(30))
            w.WriteLine($"[profile]   extern {g.Key,-40} {g.Item2,15:N0}");
        foreach (var f in fns)
            w.WriteLine($"[profile] {f.Nodes,14:N0} nodes {f.Calls,12:N0} calls  {f.Str}");
    }
}
