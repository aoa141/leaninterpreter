// Port of the Name primitives of runtime/object.cpp and `lean_name_hash` from lean.h.
//
// `Name.anonymous` is `lean_box(0)`, `Name.str p s` is ctor tag 1 with fields (p, s) and
// `Name.num p n` is ctor tag 2 with fields (p, n); both cache a `uint64` hash in the scalar area.

using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    // `lean_name_hash_ptr` (lean.h). Kept private: `lean_name_hash{,_ptr}` live in lean.h's Name section,
    // which other areas may port.
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    static ulong name_hash_ptr_s(Obj n) => lean_ctor_get_uint64_s(n, 0);

    public static byte lean_name_eq(Obj n1, Obj n2)
    {
        if (StrRtUtil.PtrEq(n1, n2)) return 1;
        if (lean_is_scalar(n1) != lean_is_scalar(n2)) return 0;
        // Both are non-scalar here (otherwise they would be equal: `Name.anonymous` is `box(0)`).
        if (lean_is_scalar(n1) || name_hash_ptr_s(n1) != name_hash_ptr_s(n2)) return 0;
        while (true)
        {
            if (lean_ptr_tag(n1) != lean_ptr_tag(n2)) return 0;
            if (lean_ptr_tag(n1) == 1)
            {
                if (!lean_string_eq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1))) return 0;
            }
            else
            {
                if (!StrRtUtil.NatEq(lean_ctor_get(n1, 1), lean_ctor_get(n2, 1))) return 0;
            }
            n1 = lean_ctor_get(n1, 0);
            n2 = lean_ctor_get(n2, 0);
            if (StrRtUtil.PtrEq(n1, n2)) return 1;
            if (lean_is_scalar(n1) != lean_is_scalar(n2)) return 0;
            if (lean_is_scalar(n1)) return 0; // unreachable: two anonymous names are pointer-equal
        }
    }
}
