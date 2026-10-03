// Global names and expressions used by the kernel (the `initialize_*` functions of the C++
// kernel). They are created through the Lean exports on first use (after the generated code has
// registered its exports) and marked persistent, as in C++.

using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

internal static class KConsts
{
    static Name P(Name n) { lean_mark_persistent(n.Raw); return n; }
    static Expr P(Expr e) { lean_mark_persistent(e.Raw); return e; }
    static Level P(Level l) { lean_mark_persistent(l.Raw); return l; }
    static Expr Const(params string[] parts) => P(Expr.MkConst(Name.Mk(parts)));

    // name generator prefixes
    public static readonly Name TmpPrefix = P(Name.Str("_uniq"));
    public static readonly Name KernelFresh = P(Name.Str("_kernel_fresh"));
    public static readonly Name IndFresh = P(Name.Str("_ind_fresh"));
    public static readonly Name NestedFresh = P(Name.Str("_nested_fresh"));
    public static readonly Name Nested = P(Name.Str("_nested"));
    public static readonly Name ConstructionsFresh = P(Name.Str("_cnstr_fresh"));

    // expr.cpp
    public static readonly Name DefaultName = P(Name.Str("a"));
    public static readonly Expr Prop = P(Expr.MkSort(Level.Zero));
    // level.cpp
    public static readonly Level LevelOne = P(Level.MkSucc(Level.Zero));

    // type_checker.cpp
    public static readonly Name BoolTrue = P(Name.Mk("Bool", "true"));
    public static readonly Name EagerReduce = P(Name.Str("eagerReduce"));
    public static readonly Expr DontCare = Const("dontcare");
    public static readonly Expr NatZero = Const("Nat", "zero");
    public static readonly Expr NatSucc = Const("Nat", "succ");
    public static readonly Expr NatAdd = Const("Nat", "add");
    public static readonly Expr NatSub = Const("Nat", "sub");
    public static readonly Expr NatMul = Const("Nat", "mul");
    public static readonly Expr NatPow = Const("Nat", "pow");
    public static readonly Expr NatGcd = Const("Nat", "gcd");
    public static readonly Expr NatDiv = Const("Nat", "div");
    public static readonly Expr NatMod = Const("Nat", "mod");
    public static readonly Expr NatBeq = Const("Nat", "beq");
    public static readonly Expr NatBle = Const("Nat", "ble");
    public static readonly Expr NatLand = Const("Nat", "land");
    public static readonly Expr NatLor = Const("Nat", "lor");
    public static readonly Expr NatXor = Const("Nat", "xor");
    public static readonly Expr NatShiftLeft = Const("Nat", "shiftLeft");
    public static readonly Expr NatShiftRight = Const("Nat", "shiftRight");
    public static readonly Expr StringMk = Const("String", "ofList");

    // library/util.cpp, library/constants.cpp
    public static readonly Expr BoolTrueExpr = Const("Bool", "true");
    public static readonly Expr BoolFalseExpr = Const("Bool", "false");
    public static readonly Name PUnit = P(Name.Str("PUnit"));
    public static readonly Name PUnitUnit = P(Name.Mk("PUnit", "unit"));

    // inductive.cpp
    public static readonly Name RecName = P(Name.Str("rec"));
    public static readonly Name MotiveName = P(Name.Str("motive"));
    public static readonly Name TName = P(Name.Str("t"));
    static readonly Expr CharType = P(Expr.MkConst(Name.Str("Char")));
    public static readonly Expr ListConsChar = P(Expr.MkApp(Expr.MkConst(Name.Mk("List", "cons"), Level.Zero), CharType));
    public static readonly Expr ListNilChar = P(Expr.MkApp(Expr.MkConst(Name.Mk("List", "nil"), Level.Zero), CharType));
    public static readonly Expr CharOfNat = Const("Char", "ofNat");

    // quot.cpp
    public static readonly Name Quot = P(Name.Str("Quot"));
    public static readonly Name QuotLift = P(Name.Mk("Quot", "lift"));
    public static readonly Name QuotInd = P(Name.Mk("Quot", "ind"));
    public static readonly Name QuotMk = P(Name.Mk("Quot", "mk"));
    public static readonly Name Eq = P(Name.Str("Eq"));

    // print.cpp
    public static readonly Name M = P(Name.Str("M"));
    public static readonly Name X = P(Name.Str("x"));

    // suffixes.h
    public static readonly Name CasesOn = P(Name.Str("casesOn"));
}
