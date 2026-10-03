// Execution of compiled IR (see Fn.cs).
//
// Every thread that runs Lean code has a `Machine`: a stack of value slots, split into segments
// so that frames never move. A call allocates the callee's frame on top of the stack, copies the
// arguments into its first slots and runs the callee's nodes (recursively on the .NET stack,
// which is checked by `lean_stack_probe`). Closures of interpreted functions point to the `Stub`
// methods below, with the function's handle as first fixed argument, so the runtime can apply
// them like any other closure.

using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

// frames of the interpreter loop are large; their locals need not be zeroed
[module: SkipLocalsInit]

namespace LeanInterpreter.Interp;

internal sealed unsafe class Machine
{
    [ThreadStatic] static Machine t_current;

    public static Machine Current
    {
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        get => t_current ?? (t_current = new Machine());
    }

    const int SegmentSize = 1 << 15;
    Value[] m_seg = new Value[SegmentSize];
    int m_sp;
    // segments below the current one, with their stack pointers
    readonly Stack<(Value[] Seg, int Sp)> m_below = new();
    Value[] m_spare;

    static readonly Obj s_box0 = lean_box(0);

    // ------------------------------------------------------------------
    // Stack

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    Value[] Alloc(int n, out int bp)
    {
        int sp = m_sp;
        var seg = m_seg;
        if (sp + n <= seg.Length)
        {
            bp = sp;
            m_sp = sp + n;
            return seg;
        }
        return AllocSlow(n, out bp);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    Value[] AllocSlow(int n, out int bp)
    {
        m_below.Push((m_seg, m_sp));
        var seg = m_spare != null && m_spare.Length >= n ? m_spare : new Value[Math.Max(SegmentSize, n)];
        m_spare = null;
        m_seg = seg;
        m_sp = n;
        bp = 0;
        return seg;
    }

    /// <summary>Releases the topmost frame (allocated at `bp` of `seg`).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    void Free(Value[] seg, int bp)
    {
        Array.Clear(seg, bp, m_sp - bp);
        m_sp = bp;
        if (bp == 0 && m_below.Count > 0) FreeSegment();
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    void FreeSegment()
    {
        m_spare = m_seg;
        (m_seg, m_sp) = m_below.Pop();
    }

    /// <summary>Saved stack state, for restoring it when an exception unwinds interpreted frames.</summary>
    public (int Depth, Value[] Seg, int Sp) Mark() => (m_below.Count, m_seg, m_sp);

    public void Restore((int Depth, Value[] Seg, int Sp) mark)
    {
        while (m_below.Count > mark.Depth) m_below.Pop();
        m_seg = mark.Seg;
        if (m_sp > mark.Sp) Array.Clear(m_seg, mark.Sp, m_sp - mark.Sp);
        m_sp = mark.Sp;
    }

    // ------------------------------------------------------------------
    // Execution

    /// <summary>Slot `i` of the frame starting at `f` (frames are accessed without bounds checks:
    /// the compiler sized them).</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static ref Value At(ref Value f, int i) => ref Unsafe.Add(ref f, i);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static ref Value Frame(Value[] s, int bp) => ref Unsafe.Add(ref MemoryMarshal.GetArrayDataReference(s), bp);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Value Arg(ref Value f, int a) => a < 0 ? new Value { O = s_box0 } : Unsafe.Add(ref f, a);

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static Obj ArgO(ref Value f, int a) => a < 0 ? s_box0 : Unsafe.Add(ref f, a).O;

    /// <summary>Calls `g` with arguments taken from slots of the frame at `bp` of `s`.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    Value Invoke(Fn g, int[] args, ref Value f)
    {
        Node body = Volatile.Read(ref g.Body) ?? g.EnsureCompiled();
        Value[] s2 = Alloc(g.FrameSize, out int bp2);
        ref Value f2 = ref Frame(s2, bp2);
        for (int i = 0; i < args.Length; i++) At(ref f2, i) = Arg(ref f, args[i]);
        Value r = Run(g, body, s2, bp2);
        Free(s2, bp2);
        return r;
    }

    Value Run(Fn fn, Node n, Value[] s, int bp)
    {
        lean_stack_probe();
        if (Profiler.Enabled) fn.Calls++;
        ref Value f = ref Frame(s, bp);
        while (true)
        {
            if (Profiler.Enabled) { fn.Nodes++; Profiler.OpCounts[(int)n.Op]++; }
            switch (n.Op)
            {
                case Op.Ctor:
                {
                    var c = Unsafe.As<NCtor>(n);
                    Obj o = lean_alloc_ctor(c.Tag, c.NumObjs, c.ScalarSz);
                    var args = c.Args;
                    for (int i = 0; i < args.Length; i++) lean_ctor_set(o, (uint)i, ArgO(ref f, args[i]));
                    At(ref f, c.Dst) = Value.Of(o);
                    break;
                }
                case Op.Reset:
                {
                    var c = Unsafe.As<NReset>(n);
                    Obj o = At(ref f, c.X).O;
                    if (lean_is_exclusive(o))
                    {
                        for (uint i = 0; i < c.N; i++) lean_ctor_release(o, i);
                        At(ref f, c.Dst) = Value.Of(o);
                    }
                    else
                    {
                        lean_dec_ref(o);
                        At(ref f, c.Dst) = Value.Of(s_box0);
                    }
                    break;
                }
                case Op.Reuse:
                {
                    var c = Unsafe.As<NReuse>(n);
                    Obj o = At(ref f, c.X).O;
                    o = lean_is_scalar(o) ? lean_alloc_ctor(c.Tag, c.NumObjs, c.ScalarSz) : lean_ctor_reuse(o, c.Tag, c.NumObjs, c.ScalarSz, c.UpdtHeader);
                    var args = c.Args;
                    for (int i = 0; i < args.Length; i++) lean_ctor_set(o, (uint)i, ArgO(ref f, args[i]));
                    At(ref f, c.Dst) = Value.Of(o);
                    break;
                }
                case Op.Proj:
                {
                    var c = Unsafe.As<NProj>(n);
                    At(ref f, c.Dst) = Value.Of(lean_ctor_get(At(ref f, c.X).O, c.I));
                    break;
                }
                case Op.UProj:
                {
                    var c = Unsafe.As<NProj>(n);
                    At(ref f, c.Dst) = Value.Num(lean_ctor_get_usize(At(ref f, c.X).O, c.I));
                    break;
                }
                case Op.SProj:
                {
                    var c = Unsafe.As<NSProj>(n);
                    Obj o = At(ref f, c.X).O;
                    At(ref f, c.Dst) = c.Ty switch
                    {
                        IrType.Float => Value.FromFloat(lean_ctor_get_float(o, c.Offset)),
                        IrType.Float32 => Value.FromFloat32(lean_ctor_get_float32(o, c.Offset)),
                        IrType.UInt8 => Value.Num(lean_ctor_get_uint8(o, c.Offset)),
                        IrType.UInt16 => Value.Num(lean_ctor_get_uint16(o, c.Offset)),
                        IrType.UInt32 => Value.Num(lean_ctor_get_uint32(o, c.Offset)),
                        IrType.UInt64 or IrType.USize => Value.Num(lean_ctor_get_uint64(o, c.Offset)),
                        _ => throw new InterpreterException("(interpreter) invalid sproj"),
                    };
                    break;
                }
                case Op.Call:
                {
                    var c = Unsafe.As<NCall>(n);
                    At(ref f, c.Dst) = Invoke(c.Target, c.Args, ref f);
                    break;
                }
                case Op.CallExt:
                {
                    var c = Unsafe.As<NCallExt>(n);
                    At(ref f, c.Dst) = CallExtern(c, s, bp);
                    break;
                }
                case Op.TailCall:
                {
                    var c = Unsafe.As<NTail>(n);
                    Assign(c.Args, null, c.NeedsTemp, ref f);
                    n = fn.Body;
                    continue;
                }
                case Op.Const:
                {
                    var c = Unsafe.As<NConst>(n);
                    Fn g = c.Target;
                    At(ref f, c.Dst) = Volatile.Read(ref g.ConstState) == 2 ? g.ConstVal : Constants.Load(g);
                    break;
                }
                case Op.PAp:
                {
                    var c = Unsafe.As<NPAp>(n);
                    At(ref f, c.Dst) = Value.Of(MkClosure(c.Target, c.Args, ref f));
                    break;
                }
                case Op.Ap:
                {
                    var c = Unsafe.As<NAp>(n);
                    At(ref f, c.Dst) = Value.Of(Apply(At(ref f, c.F).O, c.Args, ref f));
                    break;
                }
                case Op.Box:
                {
                    var c = Unsafe.As<NBox>(n);
                    At(ref f, c.Dst) = Value.Of(Boxing.Box(At(ref f, c.X), c.Ty));
                    break;
                }
                case Op.Unbox:
                {
                    var c = Unsafe.As<NUnary>(n);
                    At(ref f, c.Dst) = Boxing.Unbox(At(ref f, c.X).O, c.Ty);
                    break;
                }
                case Op.LitObj:
                {
                    var c = Unsafe.As<NLit>(n);
                    lean_inc(c.V.O);
                    At(ref f, c.Dst) = c.V;
                    break;
                }
                case Op.LitNum:
                    At(ref f, n.Dst) = Unsafe.As<NLit>(n).V;
                    break;
                case Op.IsShared:
                {
                    var c = Unsafe.As<NUnary>(n);
                    At(ref f, c.Dst) = Value.Num(lean_is_exclusive(At(ref f, c.X).O) ? 0UL : 1UL);
                    break;
                }
                case Op.Set:
                {
                    var c = Unsafe.As<NSet>(n);
                    lean_ctor_set(At(ref f, c.X).O, c.I, ArgO(ref f, c.Y));
                    break;
                }
                case Op.SetTag:
                {
                    var c = Unsafe.As<NSet>(n);
                    lean_ctor_set_tag(At(ref f, c.X).O, c.I);
                    break;
                }
                case Op.USet:
                {
                    var c = Unsafe.As<NSet>(n);
                    lean_ctor_set_usize(At(ref f, c.X).O, c.I, At(ref f, c.Y).N);
                    break;
                }
                case Op.SSet:
                {
                    var c = Unsafe.As<NSet>(n);
                    Obj o = At(ref f, c.X).O;
                    Value v = At(ref f, c.Y);
                    switch (c.Ty)
                    {
                        case IrType.Float: lean_ctor_set_float(o, c.I, v.Float); break;
                        case IrType.Float32: lean_ctor_set_float32(o, c.I, v.Float32); break;
                        case IrType.UInt8: lean_ctor_set_uint8(o, c.I, (byte)v.N); break;
                        case IrType.UInt16: lean_ctor_set_uint16(o, c.I, (ushort)v.N); break;
                        case IrType.UInt32: lean_ctor_set_uint32(o, c.I, (uint)v.N); break;
                        case IrType.UInt64:
                        case IrType.USize: lean_ctor_set_uint64(o, c.I, v.N); break;
                        default: throw new InterpreterException("(interpreter) invalid sset");
                    }
                    break;
                }
                case Op.Inc:
                {
                    var c = Unsafe.As<NIncDec>(n);
                    Obj o = At(ref f, c.X).O;
                    if (o != null)
                    {
                        if (c.N == 1) lean_inc(o); else lean_inc_n(o, c.N);
                    }
                    break;
                }
                case Op.Dec:
                {
                    var c = Unsafe.As<NIncDec>(n);
                    Obj o = At(ref f, c.X).O;
                    if (o != null)
                        for (uint i = 0; i < c.N; i++) lean_dec(o);
                    break;
                }
                case Op.Del:
                    break;
                case Op.Case:
                {
                    var c = Unsafe.As<NCase>(n);
                    ref Value v = ref At(ref f, c.X);
                    uint tag = c.Scalar ? (uint)v.N : lean_obj_tag(v.O);
                    var table = c.Table;
                    n = tag < (uint)table.Length ? table[tag] : c.Default;
                    if (n == null) throw new InterpreterException($"(interpreter) incomplete case in '{fn.Str}'");
                    continue;
                }
                case Op.Ret:
                    return Arg(ref f, Unsafe.As<NRet>(n).X);
                case Op.Jmp:
                {
                    var c = Unsafe.As<NJmp>(n);
                    Assign(c.Args, c.Jp.Params, c.NeedsTemp, ref f);
                    n = c.Jp.Body;
                    continue;
                }
                case Op.Unreachable:
                    throw new InterpreterException($"(interpreter) unreachable code has been reached in '{Unsafe.As<NUnreachable>(n).Fn}'");
                default:
                    throw new InterpreterException($"(interpreter) unknown node {n.Op}");
            }
            n = n.Next;
        }
    }

    /// <summary>Parallel assignment of arguments to parameter slots (`dsts == null`: slots 0..n-1).</summary>
    void Assign(int[] args, int[] dsts, bool needsTemp, ref Value f)
    {
        int n = args.Length;
        if (!needsTemp)
        {
            for (int i = 0; i < n; i++)
            {
                int d = dsts == null ? i : dsts[i];
                if (args[i] != d) At(ref f, d) = Arg(ref f, args[i]);
            }
            return;
        }
        Value[] t = Alloc(n, out int tb);
        for (int i = 0; i < n; i++) t[tb + i] = Arg(ref f, args[i]);
        for (int i = 0; i < n; i++) At(ref f, dsts == null ? i : dsts[i]) = t[tb + i];
        Free(t, tb);
    }

    static Value CallExtern(NCallExt c, Value[] s, int bp)
    {
        if (c.Ext == 0) throw Externs.Missing(c.Decl, c.Symbol);
        if (Profiler.Enabled) c.Hits++;
        return ((delegate*<Value[], int, int[], Value>)c.Ext)(s, bp, c.Args);
    }

    static Obj MkClosure(Fn g, int[] args, ref Value f)
    {
        int arity = g.Arity + 1;
        Obj cls = lean_alloc_closure(Stubs.For(arity), (uint)arity, (uint)(args.Length + 1));
        lean_closure_set(cls, 0, g.Handle);
        for (int i = 0; i < args.Length; i++) lean_closure_set(cls, (uint)(i + 1), ArgO(ref f, args[i]));
        return cls;
    }

    static Obj Apply(Obj fn, int[] args, ref Value f)
    {
        switch (args.Length)
        {
            case 1: return lean_apply_1(fn, ArgO(ref f, args[0]));
            case 2: return lean_apply_2(fn, ArgO(ref f, args[0]), ArgO(ref f, args[1]));
            case 3: return lean_apply_3(fn, ArgO(ref f, args[0]), ArgO(ref f, args[1]), ArgO(ref f, args[2]));
            case 4: return lean_apply_4(fn, ArgO(ref f, args[0]), ArgO(ref f, args[1]), ArgO(ref f, args[2]), ArgO(ref f, args[3]));
            default:
            {
                var xs = new Obj[args.Length];
                for (int i = 0; i < xs.Length; i++) xs[i] = ArgO(ref f, args[i]);
                return lean_apply_n(fn, (uint)xs.Length, xs);
            }
        }
    }

    // ------------------------------------------------------------------
    // Entry points

    /// <summary>Runs `g` with the given (unboxed according to the IR types) arguments; the
    /// argument count must equal the arity. Used for constants and by the export stubs.</summary>
    public Value Call(Fn g, ReadOnlySpan<Value> args)
    {
        if (g.IsExtern) return CallExternDirect(g, args);
        var mark = Mark();
        try
        {
            Node body = g.EnsureCompiled();
            Value[] s = Alloc(g.FrameSize, out int bp);
            for (int i = 0; i < args.Length; i++) s[bp + i] = args[i];
            Value r = Run(g, body, s, bp);
            Free(s, bp);
            return r;
        }
        catch
        {
            Restore(mark);
            throw;
        }
    }

    Value CallExternDirect(Fn g, ReadOnlySpan<Value> args)
    {
        var ext = Externs.Resolve(g);
        if (ext.Forward != null)
        {
            var fargs = new Value[ext.ForwardMap.Length];
            for (int i = 0; i < fargs.Length; i++) fargs[i] = ext.ForwardMap[i] < 0 ? Value.Of(s_box0) : args[ext.ForwardMap[i]];
            return Call(ext.Forward, fargs);
        }
        if (ext.Fn == 0) throw Externs.Missing(g, ext.Symbol);
        var mark = Mark();
        try
        {
            Value[] s = Alloc(Math.Max(args.Length, 1), out int bp);
            for (int i = 0; i < args.Length; i++) s[bp + i] = args[i];
            Value r = ((delegate*<Value[], int, int[], Value>)ext.Fn)(s, bp, ext.Live);
            Free(s, bp);
            return r;
        }
        catch
        {
            Restore(mark);
            throw;
        }
    }

    /// <summary>Calls `g` with owned boxed arguments (the closure calling convention) and returns
    /// an owned boxed result. Borrowed object parameters are released after the call, as the
    /// `_boxed` wrappers of compiled code do.</summary>
    public Obj CallBoxed(Fn g, ReadOnlySpan<Obj> args)
    {
        var vals = new Value[args.Length];
        for (int i = 0; i < args.Length; i++)
        {
            IrType t = g.ParamTypes[i];
            if (Ir.IsScalar(t))
            {
                vals[i] = Boxing.Unbox(args[i], t);
                lean_dec(args[i]);
            }
            else vals[i] = Value.Of(args[i]);
        }
        Value r = Call(g, vals);
        if (g.HasBorrowedParams)
            for (int i = 0; i < args.Length; i++)
                if (g.ParamBorrow[i] && !Ir.IsScalar(g.ParamTypes[i])) lean_dec(args[i]);
        return Ir.IsScalar(g.RetType) ? Boxing.Box(r, g.RetType) : r.O ?? s_box0;
    }

    // Fast path of closure calls: frame set up directly by the stubs.

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static bool Simple(Fn g) => !g.IsExtern && !g.HasScalarParams && !g.HasBorrowedParams && !Ir.IsScalar(g.RetType);

    public Value[] Enter(Fn g, out int bp, out (int, Value[], int) mark)
    {
        mark = Mark();
        g.EnsureCompiled();
        return Alloc(g.FrameSize, out bp);
    }

    public Obj Leave(Fn g, Value[] s, int bp, (int, Value[], int) mark)
    {
        try
        {
            Value r = Run(g, g.Body, s, bp);
            Free(s, bp);
            return r.O ?? s_box0;
        }
        catch
        {
            Restore(mark);
            throw;
        }
    }
}

/// <summary>Constants (nullary functions): evaluated once, on first use, and made persistent.</summary>
internal static class Constants
{
    public static Value Load(Fn g)
    {
        if (Volatile.Read(ref g.ConstState) == 2) return g.ConstVal;
        if (g.Scope is Session session) return session.LoadConstant(g);
        return Library.LoadConstant(g);
    }

    /// <summary>Evaluates the body of the constant `g` and publishes its value.</summary>
    public static Value Evaluate(Fn g)
    {
        Value v = Machine.Current.Call(g, ReadOnlySpan<Value>.Empty);
        return Publish(g, v);
    }

    public static Value Publish(Fn g, Value v)
    {
        lock (g)
        {
            if (g.ConstState == 2) return g.ConstVal;
            if (!Ir.IsScalar(g.RetType) && v.O != null) lean_mark_persistent(v.O);
            g.ConstVal = v;
            Volatile.Write(ref g.ConstState, 2);
            return v;
        }
    }
}
