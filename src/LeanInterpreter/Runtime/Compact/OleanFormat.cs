// On-disk format of compacted regions (`.olean`, `.olean.server`, `.olean.private`, `.ir`,
// `.ir.sig` files and incremental snapshots). Port of `olean_header` (library/module.cpp) and of
// the object layouts written by `object_compactor` (runtime/compact.cpp).
//
// File layout (all integers little endian, 64-bit):
//
//   offset  0: "olean"                    5 bytes
//   offset  5: version                    1 byte   (2 = plain, 3 = with closure tables)
//   offset  6: flags                      1 byte   (bit 0: big numbers use the GMP layout)
//   offset  7: Lean version string       33 bytes  (NUL padded, e.g. "4.36.0-pre")
//   offset 40: githash                   40 bytes  (NUL padded)
//   offset 80: base_addr                  8 bytes  (logical address of the start of the file)
//   v2: offset 88: compacted data (up to the end of the file)
//   v3: offset 88: data_size, offset 96: compacted data (data_size bytes), then
//       uint32 num_closure_offsets, num_closure_offsets x uint64 (data-relative `m_fun` offsets),
//       uint32 num_libs, num_libs x (uint64 base_addr, uint32 id_len, id bytes)
//
// The compacted data starts with the root pointer (8 bytes) followed by the objects, each 8-byte
// aligned, children always before parents. A pointer is either a tagged scalar (`(n << 1) | 1`) or
// the logical address of an object: `base_addr + file offset` for objects in the same file, or an
// address inside another region (an earlier part of a chained save, or a dependency region).
//
// Object header (8 bytes): int32 m_rc (= 0), uint16 m_cs_sz, uint8 m_other, uint8 m_tag.
// For "small" objects (ctors, thunks, tasks, refs, promises, mpz, closures) m_cs_sz is the object's
// byte size; for arrays, scalar arrays and strings it is 1.
//
//   ctor     header, m_other pointers, scalar area (total size m_cs_sz, a multiple of 8)
//   array    header, size, capacity (= size), size pointers
//   sarray   header (m_other = elem size), size, capacity (= size), elem*size bytes
//   string   header, size (incl. NUL), capacity (= size), length (code points), size bytes
//   mpz/GMP  header, int32 _mp_alloc (= #limbs), int32 _mp_size (+-#limbs), _mp_d (address), limbs
//   mpz/Lean header, bool m_sign (+7 pad), uint64 m_size (#digits), m_digits (address), uint32 digits
//   thunk    header, m_value, m_closure (= 0)
//   task     header, m_value, m_imp (= 0)
//   promise  header, m_result
//   ref      header, m_value
//   closure  header, m_fun, uint16 arity, uint16 num_fixed, 4 bytes pad, num_fixed pointers

using System.Runtime.CompilerServices;
using System.Text;

namespace LeanInterpreter.Runtime.Compact;

/// <summary>Error in a compacted region file (reported by the externs as an `IO.Error`).</summary>
public sealed class OleanFormatException : Exception
{
    public OleanFormatException(string msg) : base(msg) { }
}

/// <summary>The fixed 88-byte header of a compacted region file.</summary>
public struct OleanHeader
{
    public const int Size = 5 + 1 + 1 + 33 + 40 + 8;
    public byte Version;
    public byte Flags;
    public string LeanVersion;
    public string GitHash;
    public ulong BaseAddr;

    public bool Gmp => (Flags & 1) != 0;

    public static bool TryParse(ReadOnlySpan<byte> b, out OleanHeader h)
    {
        h = default;
        if (b.Length < Size) return false;
        if (b[0] != 'o' || b[1] != 'l' || b[2] != 'e' || b[3] != 'a' || b[4] != 'n') return false;
        h.Version = b[5];
        h.Flags = b[6];
        h.LeanVersion = CStr(b.Slice(7, 33));
        h.GitHash = CStr(b.Slice(40, 40));
        h.BaseAddr = Unsafe.ReadUnaligned<ulong>(ref Unsafe.AsRef(in b[80]));
        return true;
    }

    static string CStr(ReadOnlySpan<byte> s)
    {
        int n = s.IndexOf((byte)0);
        if (n < 0) n = s.Length;
        return Encoding.ASCII.GetString(s.Slice(0, n));
    }

    public void WriteTo(Span<byte> b)
    {
        b.Slice(0, Size).Clear();
        "olean"u8.CopyTo(b);
        b[5] = Version;
        b[6] = Flags;
        // strncpy semantics: copy at most N bytes, pad with NULs.
        var v = Encoding.ASCII.GetBytes(LeanVersion ?? "");
        v.AsSpan(0, Math.Min(v.Length, 33)).CopyTo(b.Slice(7));
        var g = Encoding.ASCII.GetBytes(GitHash ?? "");
        g.AsSpan(0, Math.Min(g.Length, 40)).CopyTo(b.Slice(40));
        Unsafe.WriteUnaligned(ref b[80], BaseAddr);
    }
}

internal static class OleanLayout
{
    public const int CtorHeader = 8;
    public const int ArrayHeader = 24;      // sizeof(lean_array_object)
    public const int SArrayHeader = 24;     // sizeof(lean_sarray_object)
    public const int StringHeader = 32;     // sizeof(lean_string_object)
    public const int ThunkSize = 24;        // sizeof(lean_thunk_object)
    public const int TaskSize = 24;         // sizeof(lean_task_object) (header, m_value, m_imp)
    public const int PromiseSize = 16;      // sizeof(lean_promise_object)
    public const int RefSize = 16;          // sizeof(lean_ref_object)
    public const int ClosureHeader = 24;    // sizeof(lean_closure_object)
    public const int MpzGmpHeader = 24;     // sizeof(mpz_object) with GMP
    public const int MpzLeanHeader = 32;    // sizeof(mpz_object) without GMP

    /// <summary>Alignment of the logical start of each part of a chained save (`ALIGN` in module.cpp).</summary>
    public const ulong PartAlign = 1UL << 16;

    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static long Align8(long n) => (n + 7) & ~7L;

    /// <summary>
    /// Byte size of the compacted image of `o` (as `lean_object_byte_size` of the compacted object).
    /// For constructors the scalar area size is rounded up to a multiple of 8, as native Lean's
    /// heap objects are.
    /// </summary>
    public static long CompactedSize(Obj o, bool gmp)
    {
        int tag = o.m_tag;
        if (tag <= LeanRt.LeanMaxCtorTag)
            return CtorHeader + 8L * o.m_other + Align8(o.m_cs_sz);
        switch (tag)
        {
            case LeanRt.LeanArray: return ArrayHeader + 8 * Unsafe.As<ArrayObj>(o).m_size;
            case LeanRt.LeanScalarArray:
                return Align8(SArrayHeader + (long)LeanRt.lean_sarray_elem_size(o) * Unsafe.As<SArrayObj>(o).m_size);
            case LeanRt.LeanString: return Align8(StringHeader + Unsafe.As<StrObj>(o).m_size);
            case LeanRt.LeanMPZ:
            {
                var v = System.Numerics.BigInteger.Abs(Unsafe.As<MpzObj>(o).m_value);
                long nbytes = v.GetByteCount(isUnsigned: true);
                return gmp ? MpzGmpHeader + 8 * ((nbytes + 7) / 8) : Align8(MpzLeanHeader + 4 * ((nbytes + 3) / 4));
            }
            case LeanRt.LeanThunk: return ThunkSize;
            case LeanRt.LeanTask: return TaskSize;
            case LeanRt.LeanPromise: return PromiseSize;
            case LeanRt.LeanRef: return RefSize;
            case LeanRt.LeanClosure: return ClosureHeader + 8L * Unsafe.As<Closure>(o).m_num_fixed;
            default: throw new OleanFormatException($"unexpected object tag {tag} in compacted region");
        }
    }
}
