// The λRC IR (`Lean.IR.Decl` and friends, Lean/Compiler/IR/Basic.lean) as it is stored in the
// `.ir` files of the sysroot, and the values the interpreter computes with.

using System.Runtime.CompilerServices;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Interp;

/// <summary>`Lean.IR.IRType` (constructor indices; all but `struct`/`union` are boxed scalars).</summary>
internal enum IrType : byte
{
    Float, UInt8, UInt16, UInt32, UInt64, USize, Erased, Object, TObject, Float32, Struct, Union, Tagged, Void
}

/// <summary>`Lean.IR.Expr` constructor indices.</summary>
internal enum ExprKind : byte { Ctor, Reset, Reuse, Proj, UProj, SProj, FAp, PAp, Ap, Box, Unbox, Lit, IsShared }

/// <summary>`Lean.IR.FnBody` constructor indices.</summary>
internal enum FnBodyKind : byte { VDecl, JDecl, Set, SetTag, USet, SSet, Inc, Dec, Del, Case, Ret, Jmp, Unreachable }

/// <summary>An interpreter value: an unboxed scalar (floats as their bit pattern) or an object.</summary>
internal struct Value
{
    public ulong N;
    public Obj O;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Value Num(ulong n) => new Value { N = n };
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Value Of(Obj o) => new Value { O = o };
    public static Value FromFloat(double f) => new Value { N = BitConverter.DoubleToUInt64Bits(f) };
    public static Value FromFloat32(float f) => new Value { N = BitConverter.SingleToUInt32Bits(f) };
    public double Float => BitConverter.UInt64BitsToDouble(N);
    public float Float32 => BitConverter.UInt32BitsToSingle((uint)N);
}

/// <summary>Accessors of the IR objects. `VarId`/`JoinPointId` are represented by their `Nat` index.</summary>
internal static class Ir
{
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Obj F(Obj o, int i) => lean_ctor_get(o, (uint)i);
    public static int Idx(Obj nat) => (int)lean_unbox(nat);
    public static int Size(Obj arr) => (int)Unsafe.As<ArrayObj>(arr).m_size;
    public static Obj At(Obj arr, int i) => Unsafe.As<ArrayObj>(arr).m_data[i];

    public static IrType ToType(Obj o)
    {
        if (!lean_is_scalar(o)) throw new InterpreterException("(interpreter) struct/union IR types are not supported");
        return (IrType)lean_unbox(o);
    }

    public static bool IsScalar(IrType t) =>
        t is IrType.Float or IrType.Float32 or IrType.UInt8 or IrType.UInt16 or IrType.UInt32 or IrType.UInt64 or IrType.USize;

    // Arg: var (id) | erased (box 1)
    public static bool ArgIsErased(Obj a) => lean_is_scalar(a);
    public static Obj ArgVar(Obj a) => F(a, 0);

    // CtorInfo: name, cidx, size, usize, ssize
    public static int CtorTag(Obj c) => Idx(F(c, 1));
    public static int CtorSize(Obj c) => Idx(F(c, 2));
    public static int CtorUSize(Obj c) => Idx(F(c, 3));
    public static int CtorSSize(Obj c) => Idx(F(c, 4));

    public static ExprKind ExprTag(Obj e) => (ExprKind)lean_obj_tag(e);
    public static FnBodyKind BodyTag(Obj b) => (FnBodyKind)lean_obj_tag(b);

    // Param: x, ty (objects), borrow (scalar)
    public static Obj ParamVar(Obj p) => F(p, 0);
    public static IrType ParamType(Obj p) => ToType(F(p, 1));
    public static bool ParamBorrow(Obj p) => lean_ctor_get_uint8_s(p, 0) != 0;

    // Decl: fdecl (f, xs, type, body, info) | extern (f, xs, type, ext)
    public const uint DeclFun = 0, DeclExtern = 1;
    public static uint DeclTag(Obj d) => lean_obj_tag(d);
    public static Obj DeclName(Obj d) => F(d, 0);
    public static Obj DeclParams(Obj d) => F(d, 1);
    public static IrType DeclType(Obj d) => ToType(F(d, 2));
    public static Obj DeclBody(Obj d) => F(d, 3);

    /// <summary>The C symbol of a `@[extern]` declaration for the C backend (or `all`), or null
    /// (`adhoc`/`opaque` entries, or none). `ExternAttrData` is a trivial structure, i.e. its
    /// `entries : List ExternEntry`.</summary>
    public static string ExternSymbol(Obj d, out bool adhoc)
    {
        adhoc = false;
        Obj l = F(d, 3);
        while (!lean_is_scalar(l))
        {
            Obj e = F(l, 0);
            l = F(l, 1);
            if (lean_is_scalar(e)) continue; // opaque
            string backend = IrName.ToString(F(e, 0));
            if (backend != "c" && backend != "all") continue;
            switch (lean_obj_tag(e))
            {
                case 0: adhoc = true; return null;                         // adhoc
                case 1: return null;                                       // inline (not used by Init/Std/Lean)
                case 2: return lean_string_to_net(F(e, 1));                // standard
            }
        }
        return null;
    }
}

/// <summary>Boxing of scalars as in lean.h.</summary>
internal static class Boxing
{
    public static Obj Box(Value v, IrType t)
    {
        switch (t)
        {
            case IrType.Float: return lean_box_float(v.Float);
            case IrType.Float32: return lean_box_float32(v.Float32);
            case IrType.UInt8:
            case IrType.UInt16:
            case IrType.UInt32: return lean_box(v.N);
            case IrType.UInt64:
            case IrType.USize: return lean_box_uint64(v.N);
            default:
                // a slot that was never assigned (e.g. an erased world token) holds no object
                return v.O ?? lean_box(0);
        }
    }

    public static Value Unbox(Obj o, IrType t)
    {
        switch (t)
        {
            case IrType.Float: return Value.FromFloat(lean_unbox_float(o));
            case IrType.Float32: return Value.FromFloat32(lean_unbox_float32(o));
            case IrType.UInt8:
            case IrType.UInt16: return Value.Num(lean_unbox(o));
            case IrType.UInt32: return Value.Num((uint)lean_unbox(o));
            case IrType.UInt64:
            case IrType.USize: return Value.Num(lean_unbox_uint64(o));
            default: throw new InterpreterException("(interpreter) cannot unbox a value of non-scalar type");
        }
    }
}
