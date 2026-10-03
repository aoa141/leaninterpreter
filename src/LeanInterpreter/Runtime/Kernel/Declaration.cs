// Port of kernel/declaration.{h,cpp}: views over `Lean.Declaration`, `Lean.ConstantInfo` and the
// `*Val` structures. Object fields are read directly; scalar fields (Bool / enum) are stored as
// UInt8 in the scalar area in declaration order (objects first, then scalars).

using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

public enum ReducibilityHintsKind : byte { Opaque, Abbreviation, Regular }
public enum DefinitionSafety : byte { Unsafe, Safe, Partial }
public enum QuotKind : byte { Type, Mk, Lift, Ind }
public enum DeclarationKind : byte { Axiom, Definition, Theorem, Opaque, Quot, MutualDefinition, Inductive }
public enum ConstantInfoKind : byte { Axiom, Definition, Theorem, Opaque, Quot, Inductive, Constructor, Recursor }

internal static class ReducibilityHints
{
    public static Obj MkOpaque() => lean_box(0);
    public static Obj MkAbbreviation() => lean_box(1);
    public static ReducibilityHintsKind Kind(Obj h) => (ReducibilityHintsKind)lean_obj_tag(h);
    public static bool IsRegular(Obj h) => Kind(h) == ReducibilityHintsKind.Regular;
    public static bool IsAbbrev(Obj h) => Kind(h) == ReducibilityHintsKind.Abbreviation;
    /// <summary>`lean_reducibility_hints_get_height`.</summary>
    public static uint GetHeight(Obj h) => IsRegular(h) ? lean_ctor_get_uint32_s(h, 0) : 0;

    /// <summary>`compare(h1, h2)`: &lt; 0 unfold f1, == 0 unfold both, &gt; 0 unfold f2.</summary>
    public static int Compare(Obj h1, Obj h2)
    {
        var k1 = Kind(h1); var k2 = Kind(h2);
        if (k1 == k2)
        {
            if (k1 == ReducibilityHintsKind.Regular)
            {
                uint a = GetHeight(h1), b = GetHeight(h2);
                if (a == b) return 0;
                return a > b ? -1 : 1;
            }
            return 0;
        }
        if (k1 == ReducibilityHintsKind.Opaque) return 1;
        if (k2 == ReducibilityHintsKind.Opaque) return -1;
        if (k1 == ReducibilityHintsKind.Abbreviation) return -1;
        if (k2 == ReducibilityHintsKind.Abbreviation) return 1;
        throw lean_internal_panic_unreachable();
    }
}

/// <summary>`structure ConstantVal where name levelParams type`.</summary>
public readonly struct ConstantVal
{
    public readonly Obj Raw;
    public ConstantVal(Obj raw) { Raw = raw; }
    public Name Name => new Name(lean_ctor_get(Raw, 0));
    public Obj LParams => lean_ctor_get(Raw, 1);
    public Expr Type => new Expr(lean_ctor_get(Raw, 2));
}

/// <summary>`DefinitionVal` (objs: cval, value, hints, all; scalars: safety).</summary>
public readonly struct DefinitionVal
{
    public readonly Obj Raw;
    public DefinitionVal(Obj raw) { Raw = raw; }
    public ConstantVal CVal => new ConstantVal(lean_ctor_get(Raw, 0));
    public Name Name => CVal.Name;
    public Obj LParams => CVal.LParams;
    public Expr Type => CVal.Type;
    public Expr Value => new Expr(lean_ctor_get(Raw, 1));
    public Obj Hints => lean_ctor_get(Raw, 2);
    public DefinitionSafety Safety => (DefinitionSafety)lean_ctor_get_uint8_s(Raw, 0);
    public bool IsUnsafe => Safety == DefinitionSafety.Unsafe;

    public static DefinitionVal Mk(Name n, Obj lparams, Expr type, Expr val, Obj hints, DefinitionSafety safety, Obj all) =>
        new DefinitionVal(KX.MkDefinitionVal(RC.Own(n.Raw), RC.Own(lparams), RC.Own(type.Raw), RC.Own(val.Raw), RC.Own(hints), (byte)safety, RC.Own(all)));
}

/// <summary>`InductiveVal` (objs: cval, numParams, numIndices, all, ctors, numNested; scalars: isRec, isUnsafe, isReflexive).</summary>
public readonly struct InductiveVal
{
    public readonly Obj Raw;
    public InductiveVal(Obj raw) { Raw = raw; }
    public ConstantVal CVal => new ConstantVal(lean_ctor_get(Raw, 0));
    public uint NParams => (uint)lean_unbox(lean_ctor_get(Raw, 1));
    public uint NIndices => (uint)lean_unbox(lean_ctor_get(Raw, 2));
    public Obj All => lean_ctor_get(Raw, 3);
    public Obj Cnstrs => lean_ctor_get(Raw, 4);
    public uint NCnstrs => (uint)KList.Length(Cnstrs);
    public uint NNested => (uint)lean_unbox(lean_ctor_get(Raw, 5));
    public bool IsRec => lean_ctor_get_uint8_s(Raw, 0) != 0;
    public bool IsUnsafe => lean_ctor_get_uint8_s(Raw, 1) != 0;
    public bool IsReflexive => lean_ctor_get_uint8_s(Raw, 2) != 0;

    public static InductiveVal Mk(Name n, Obj lparams, Expr type, uint nparams, uint nindices, Obj all, Obj cnstrs, uint nnested, bool isRec, bool isUnsafe, bool isReflexive) =>
        new InductiveVal(KX.MkInductiveVal(RC.Own(n.Raw), RC.Own(lparams), RC.Own(type.Raw), lean_box(nparams), lean_box(nindices),
            RC.Own(all), RC.Own(cnstrs), lean_box(nnested), isRec ? (byte)1 : (byte)0, isUnsafe ? (byte)1 : (byte)0, isReflexive ? (byte)1 : (byte)0));
}

/// <summary>`ConstructorVal` (objs: cval, induct, cidx, numParams, numFields; scalars: isUnsafe).</summary>
public readonly struct ConstructorVal
{
    public readonly Obj Raw;
    public ConstructorVal(Obj raw) { Raw = raw; }
    public ConstantVal CVal => new ConstantVal(lean_ctor_get(Raw, 0));
    public Name Induct => new Name(lean_ctor_get(Raw, 1));
    public uint CIdx => (uint)lean_unbox(lean_ctor_get(Raw, 2));
    public uint NParams => (uint)lean_unbox(lean_ctor_get(Raw, 3));
    public uint NFields => (uint)lean_unbox(lean_ctor_get(Raw, 4));
    public bool IsUnsafe => lean_ctor_get_uint8_s(Raw, 0) != 0;

    public static ConstructorVal Mk(Name n, Obj lparams, Expr type, Name induct, uint cidx, uint nparams, uint nfields, bool isUnsafe) =>
        new ConstructorVal(KX.MkConstructorVal(RC.Own(n.Raw), RC.Own(lparams), RC.Own(type.Raw), RC.Own(induct.Raw),
            lean_box(cidx), lean_box(nparams), lean_box(nfields), isUnsafe ? (byte)1 : (byte)0));
}

/// <summary>`RecursorRule` (ctor, nfields, rhs).</summary>
public readonly struct RecursorRule
{
    public readonly Obj Raw;
    public RecursorRule(Obj raw) { Raw = raw; }
    public Name Cnstr => new Name(lean_ctor_get(Raw, 0));
    public uint NFields => (uint)lean_unbox(lean_ctor_get(Raw, 1));
    public Expr Rhs => new Expr(lean_ctor_get(Raw, 2));

    public static RecursorRule Mk(Name cnstr, uint nfields, Expr rhs) =>
        new RecursorRule(RC.MkCnstr(0, RC.Own(cnstr.Raw), lean_box(nfields), RC.Own(rhs.Raw)));
}

/// <summary>`RecursorVal` (objs: cval, all, numParams, numIndices, numMotives, numMinors, rules; scalars: k, isUnsafe).</summary>
public readonly struct RecursorVal
{
    public readonly Obj Raw;
    public RecursorVal(Obj raw) { Raw = raw; }
    public ConstantVal CVal => new ConstantVal(lean_ctor_get(Raw, 0));
    public Name Name => CVal.Name;
    public Obj All => lean_ctor_get(Raw, 1);
    public uint NParams => (uint)lean_unbox(lean_ctor_get(Raw, 2));
    public uint NIndices => (uint)lean_unbox(lean_ctor_get(Raw, 3));
    public uint NMotives => (uint)lean_unbox(lean_ctor_get(Raw, 4));
    public uint NMinors => (uint)lean_unbox(lean_ctor_get(Raw, 5));
    public uint MajorIdx => NParams + NMotives + NMinors + NIndices;
    public Obj Rules => lean_ctor_get(Raw, 6);
    public bool IsK => lean_ctor_get_uint8_s(Raw, 0) != 0;
    public bool IsUnsafe => lean_ctor_get_uint8_s(Raw, 1) != 0;

    public Name GetMajorInduct()
    {
        uint n = MajorIdx;
        Expr t = CVal.Type;
        for (uint i = 0; i < n; i++) t = t.BindingBody;
        t = t.BindingDomain;
        t = Expr.GetAppFn(t);
        return t.ConstName;
    }

    public static RecursorVal Mk(Name n, Obj lparams, Expr type, Obj all, uint nparams, uint nindices, uint nmotives, uint nminors, Obj rules, bool k, bool isUnsafe) =>
        new RecursorVal(KX.MkRecursorVal(RC.Own(n.Raw), RC.Own(lparams), RC.Own(type.Raw), RC.Own(all),
            lean_box(nparams), lean_box(nindices), lean_box(nmotives), lean_box(nminors), RC.Own(rules), k ? (byte)1 : (byte)0, isUnsafe ? (byte)1 : (byte)0));
}

internal static class QuotVal
{
    public static Obj Mk(Name n, Obj lparams, Expr type, QuotKind k) =>
        KX.MkQuotVal(RC.Own(n.Raw), RC.Own(lparams), RC.Own(type.Raw), (byte)k);
}

/// <summary>`Lean.ConstantInfo`.</summary>
public readonly struct ConstantInfo
{
    public readonly Obj Raw;
    public ConstantInfo(Obj raw) { Raw = raw; }

    public bool IsNull => Raw == null;
    public ConstantInfoKind Kind => (ConstantInfoKind)Raw.m_tag;
    public Obj Val => lean_ctor_get(Raw, 0);
    public ConstantVal CVal => new ConstantVal(lean_ctor_get(Val, 0));
    public Name Name => CVal.Name;
    public Obj LParams => CVal.LParams;
    public uint NumLParams => (uint)KList.Length(LParams);
    public Expr Type => CVal.Type;

    public bool IsDefinition => Kind == ConstantInfoKind.Definition;
    public bool IsAxiom => Kind == ConstantInfoKind.Axiom;
    public bool IsTheorem => Kind == ConstantInfoKind.Theorem;
    public bool IsOpaque => Kind == ConstantInfoKind.Opaque;
    public bool IsInductive => Kind == ConstantInfoKind.Inductive;
    public bool IsConstructor => Kind == ConstantInfoKind.Constructor;
    public bool IsRecursor => Kind == ConstantInfoKind.Recursor;
    public bool IsQuot => Kind == ConstantInfoKind.Quot;

    public bool HasValue(bool allowOpaque = false) => IsTheorem || IsDefinition || (allowOpaque && IsOpaque);
    /// <summary>The value of a definition/theorem/opaque (field 1 of the `*Val`).</summary>
    public Expr GetValue() => new Expr(lean_ctor_get(Val, 1));

    public Obj Hints => IsDefinition ? lean_ctor_get(Val, 2) : ReducibilityHints.MkOpaque();

    public DefinitionVal ToDefinitionVal() => new DefinitionVal(Val);
    public InductiveVal ToInductiveVal() => new InductiveVal(Val);
    public ConstructorVal ToConstructorVal() => new ConstructorVal(Val);
    public RecursorVal ToRecursorVal() => new RecursorVal(Val);
    public QuotKind QuotKind => (QuotKind)lean_ctor_get_uint8_s(Val, 0);

    public bool IsUnsafe
    {
        get
        {
            switch (Kind)
            {
                case ConstantInfoKind.Axiom: return lean_ctor_get_uint8_s(Val, 0) != 0;
                case ConstantInfoKind.Definition: return ToDefinitionVal().Safety == DefinitionSafety.Unsafe;
                case ConstantInfoKind.Theorem: return false;
                case ConstantInfoKind.Opaque: return lean_ctor_get_uint8_s(Val, 0) != 0;
                case ConstantInfoKind.Quot: return false;
                case ConstantInfoKind.Inductive: return ToInductiveVal().IsUnsafe;
                case ConstantInfoKind.Constructor: return ToConstructorVal().IsUnsafe;
                case ConstantInfoKind.Recursor: return ToRecursorVal().IsUnsafe;
            }
            throw lean_internal_panic_unreachable();
        }
    }

    /// <summary>`constant_info(declaration const &)`: axioms, definitions, theorems and opaques share the layout (owned result).</summary>
    public static ConstantInfo OfDeclaration(Declaration d) => new ConstantInfo(RC.Own(d.Raw));
    public static ConstantInfo Of(ConstantInfoKind k, Obj val) => new ConstantInfo(RC.MkCnstr((uint)k, RC.Own(val)));
}

/// <summary>`Lean.Declaration`.</summary>
public readonly struct Declaration
{
    public readonly Obj Raw;
    public Declaration(Obj raw) { Raw = raw; }

    public DeclarationKind Kind => (DeclarationKind)lean_obj_tag(Raw);
    public Obj Val => lean_ctor_get(Raw, 0);
    public DefinitionVal ToDefinitionVal() => new DefinitionVal(Val);
    public ConstantVal ToConstantVal() => new ConstantVal(lean_ctor_get(Val, 0));
    /// <summary>`to_definition_vals` for mutual definitions (List DefinitionVal).</summary>
    public Obj DefinitionVals => lean_ctor_get(Raw, 0);
    public Expr Value => new Expr(lean_ctor_get(Val, 1));

    // inductDecl (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
    public Obj IndLParams => lean_ctor_get(Raw, 0);
    public Obj IndNParams => lean_ctor_get(Raw, 1);
    public Obj IndTypes => lean_ctor_get(Raw, 2);
    public bool IndIsUnsafe => lean_ctor_get_uint8_s(Raw, 0) != 0;

    public bool IsUnsafe
    {
        get
        {
            switch (Kind)
            {
                case DeclarationKind.Definition: return ToDefinitionVal().Safety == DefinitionSafety.Unsafe;
                case DeclarationKind.Axiom: return lean_ctor_get_uint8_s(Val, 0) != 0;
                case DeclarationKind.Theorem: return false;
                case DeclarationKind.Opaque: return lean_ctor_get_uint8_s(Val, 0) != 0;
                case DeclarationKind.Inductive: return IndIsUnsafe;
                case DeclarationKind.Quot: return false;
                case DeclarationKind.MutualDefinition: return true;
            }
            throw lean_internal_panic_unreachable();
        }
    }

    public static Declaration MkDefinition(Name n, Obj lparams, Expr t, Expr v, Obj hints, DefinitionSafety safety = DefinitionSafety.Safe)
    {
        Obj all = KList.Cons(RC.Own(n.Raw), lean_box(0));
        var dv = DefinitionVal.Mk(n, lparams, t, v, hints, safety, all);
        return new Declaration(RC.MkCnstr((uint)DeclarationKind.Definition, dv.Raw));
    }

    public static Declaration MkInductiveDecl(Obj lparams, Obj nparams, Obj types, bool isUnsafe) =>
        new Declaration(KX.MkInductiveDecl(RC.Own(lparams), RC.Own(nparams), RC.Own(types), isUnsafe ? (byte)1 : (byte)0));

    /// <summary>`use_unsafe(env, e)`.</summary>
    public static bool UseUnsafe(Environment env, Expr e)
    {
        bool found = false;
        ForEachFn.ForEach(e, x =>
        {
            if (found) return false;
            if (x.IsConst)
            {
                var info = env.Find(x.ConstName);
                if (!info.IsNull && info.IsUnsafe)
                {
                    found = true;
                    return false;
                }
            }
            return true;
        });
        return found;
    }

    public static Declaration MkDefinitionInferringUnsafe(Environment env, Name n, Obj lparams, Expr t, Expr v, Obj hints)
    {
        bool isUnsafe = UseUnsafe(env, t) || UseUnsafe(env, v);
        return MkDefinition(n, lparams, t, v, hints, isUnsafe ? DefinitionSafety.Unsafe : DefinitionSafety.Safe);
    }
}

/// <summary>`InductiveType` (name, type, ctors : List Constructor) and `Constructor` (name, type).</summary>
internal static class InductiveType
{
    public static Name GetName(Obj t) => new Name(lean_ctor_get(t, 0));
    public static Expr GetType(Obj t) => new Expr(lean_ctor_get(t, 1));
    public static Obj GetCnstrs(Obj t) => lean_ctor_get(t, 2);
    public static Obj Mk(Name id, Expr type, Obj cnstrs) => RC.MkCnstr(0, RC.Own(id.Raw), RC.Own(type.Raw), RC.Own(cnstrs));

    public static Name CnstrName(Obj c) => new Name(lean_ctor_get(c, 0));
    public static Expr CnstrType(Obj c) => new Expr(lean_ctor_get(c, 1));
    public static Obj MkCnstr(Name n, Expr type) => RC.MkCnstr(0, RC.Own(n.Raw), RC.Own(type.Raw));
}
