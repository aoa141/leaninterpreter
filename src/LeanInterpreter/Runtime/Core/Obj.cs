// LeanInterpreter object model.
//
// This is the managed counterpart of `lean_object` (see `src/include/lean/lean.h` in the Lean 4
// repository). Every Lean value that is represented as `lean_object*` in C is an `Obj` here.
//
// Differences with the C runtime:
//  * Tagged pointers (`lean_box(n)`) are represented by instances of `Box` (tag `LeanBoxTag`).
//    Small values are cached. Boxes are persistent (`m_rc == 0`), so RC operations on them are
//    no-ops even without an `lean_is_scalar` check.
//  * Memory is reclaimed by the .NET GC. We still maintain reference counts because Lean relies
//    on them for destructive updates (`lean_is_exclusive`). When an object's RC drops to zero we
//    release its children (so that their RCs stay accurate), but never "free" anything.
//  * Pointer addresses (`ptrAddrUnsafe`) are emulated by a lazily assigned unique id.
//  * Constructor objects store their first 8 object fields inline (`Ctor1`..`Ctor8`), further
//    object fields in `CtorN.rest`, and scalar fields in `s0` (first 8 bytes) and `sx` (rest).
//    Scalar offsets used by the generated code are *relative to the start of the scalar area*.

using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

public class Obj
{
    /// <summary>Reference count: &gt; 0 single threaded, &lt; 0 multi threaded, 0 persistent.</summary>
    public int m_rc;
    public byte m_tag;
    /// <summary>Number of object fields (ctor) or element size (scalar array); linear mark bit for arrays/strings.</summary>
    public byte m_other;
    /// <summary>Constructor objects: size in bytes of the scalar area.</summary>
    public ushort m_cs_sz;
    /// <summary>Unique pseudo-address (0 until requested).</summary>
    public long m_id;

    public Obj() { m_rc = 1; }
}

/// <summary>Boxed scalar (the managed equivalent of a tagged pointer).</summary>
public sealed class Box : Obj
{
    public readonly ulong m_value;
    public Box(ulong v) { m_rc = 0; m_tag = LeanRt.LeanBoxTag; m_value = v; }
}

/// <summary>Constructor object without object fields.</summary>
public class Ctor : Obj
{
    /// <summary>First 8 bytes of the scalar area (little endian).</summary>
    public ulong s0;
    /// <summary>Remaining bytes of the scalar area (null if the scalar area is at most 8 bytes).</summary>
    public byte[] sx;
}

public class Ctor1 : Ctor { public Obj f0; }
public class Ctor2 : Ctor1 { public Obj f1; }
public class Ctor3 : Ctor2 { public Obj f2; }
public class Ctor4 : Ctor3 { public Obj f3; }
public class Ctor5 : Ctor4 { public Obj f4; }
public class Ctor6 : Ctor5 { public Obj f5; }
public class Ctor7 : Ctor6 { public Obj f6; }
public class Ctor8 : Ctor7 { public Obj f7; }
public sealed class CtorN : Ctor8 { public Obj[] rest; }

public sealed unsafe class Closure : Obj
{
    /// <summary>Function pointer (`delegate*&lt;Obj, ..., Obj&gt;` or `delegate*&lt;Obj[], Obj&gt;` if arity &gt; 16).</summary>
    public void* m_fun;
    public ushort m_arity;
    public ushort m_num_fixed;
    public Obj[] m_objs;
}

public sealed class ArrayObj : Obj
{
    public Obj[] m_data;   // capacity == m_data.Length
    public long m_size;
}

/// <summary>Scalar array; `m_other` (without the linear bit) holds the element size.</summary>
public sealed class SArrayObj : Obj
{
    public byte[] m_data;  // capacity (in elements) == m_data.Length / elemSize
    public long m_size;    // number of elements
    public long m_capacity;
}

/// <summary>UTF-8 string. `m_size` includes the terminating NUL byte, as in C.</summary>
public sealed class StrObj : Obj
{
    public byte[] m_data;  // capacity == m_data.Length
    public long m_size;
    public long m_length;  // number of code points
}

public sealed class MpzObj : Obj
{
    public System.Numerics.BigInteger m_value;
}

public sealed class ThunkObj : Obj
{
    public volatile Obj m_value;
    public volatile Obj m_closure;
}

public sealed class RefObj : Obj
{
    public volatile Obj m_value;
    /// <summary>Non-zero for a ref created while the compiled Lean modules were initializing:
    /// index of its value in the global state of each logical process (see `LeanGlobalRefs`).</summary>
    public int m_slot;
}

public sealed class ExternalObj : Obj
{
    public ExternalClass m_class;
    public object m_data;
}

/// <summary>Managed counterpart of `lean_external_class`.</summary>
public sealed class ExternalClass
{
    public readonly Action<object> Finalize;
    public readonly Action<object, Obj> Foreach;
    public ExternalClass(Action<object> finalize, Action<object, Obj> foreach_)
    {
        Finalize = finalize; Foreach = foreach_;
    }
}

/// <summary>`Task α`. `m_imp` is owned by the task manager (Runtime/Tasks).</summary>
public sealed class TaskObj : Obj
{
    public volatile Obj m_value;
    public volatile object m_imp;
}

/// <summary>`IO.Promise α`.</summary>
public sealed class PromiseObj : Obj
{
    public TaskObj m_result;
}
