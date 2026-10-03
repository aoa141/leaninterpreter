// Port of runtime/hash.{h,cpp}. These must match the C implementation bit for bit since hashes
// are stored in `.olean` files (e.g. `Name` hashes).

using System.Runtime.CompilerServices;

namespace LeanInterpreter.Runtime;

public static class LeanHash
{
    const ulong M = 0xc6a4a7935bd1e995UL;
    const int R = 47;

    /// <summary>`lean::hash(h, k)` / `lean_uint64_mix_hash`.</summary>
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static ulong Mix(ulong h, ulong k)
    {
        k *= M;
        k ^= k >> R;
        k ^= M;
        h ^= k;
        h *= M;
        return h;
    }

    public static ulong MurmurHash64A(ReadOnlySpan<byte> data, ulong seed)
    {
        ulong len = (ulong)data.Length;
        ulong h = seed ^ (len * M);
        int nblocks = data.Length / 8;
        for (int i = 0; i < nblocks; i++)
        {
            ulong k = Unsafe.ReadUnaligned<ulong>(ref Unsafe.AsRef(in data[i * 8]));
            k *= M;
            k ^= k >> R;
            k *= M;
            h ^= k;
            h *= M;
        }
        int tail = nblocks * 8;
        switch (data.Length & 7)
        {
            case 7: h ^= (ulong)data[tail + 6] << 48; goto case 6;
            case 6: h ^= (ulong)data[tail + 5] << 40; goto case 5;
            case 5: h ^= (ulong)data[tail + 4] << 32; goto case 4;
            case 4: h ^= (ulong)data[tail + 3] << 24; goto case 3;
            case 3: h ^= (ulong)data[tail + 2] << 16; goto case 2;
            case 2: h ^= (ulong)data[tail + 1] << 8; goto case 1;
            case 1:
                h ^= data[tail];
                h *= M;
                break;
        }
        h ^= h >> R;
        h *= M;
        h ^= h >> R;
        return h;
    }

    /// <summary>`lean::hash_str`.</summary>
    public static ulong HashStr(ReadOnlySpan<byte> s, ulong init) => MurmurHash64A(s, init);
}
