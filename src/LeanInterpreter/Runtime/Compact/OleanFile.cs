// Managed API for reading and writing compacted region files (`.olean` & co.). The Lean externs in
// LeanRt.Compact.cs are thin wrappers around this.

using System.Runtime.CompilerServices;
using System.Text;

namespace LeanInterpreter.Runtime.Compact;

public static class OleanFile
{
    /// <summary>Version string written into new files (`get_short_version_string()`).</summary>
    public static string LeanVersion = "4.36.0-pre";
    /// <summary>Githash written into new files (`LEAN_GITHASH`).</summary>
    public static string GitHash = "77f336f7ae6a60419d3882e0d5ca7ac3a2155528";
    /// <summary>Write big numbers in the GMP layout (flags bit 0), as the native release build does.</summary>
    public static bool UseGmpLayout = true;

    /// <summary>Reads a compacted region as `CompactedRegion.read` does.</summary>
    public static CompactedRegionData ReadForLean(string path, params CompactedRegionData[] deps) =>
        LazyRegion.Enabled ? LazyRegion.Open(path, deps) : RegionReader.ReadFile(path, deps);

    /// <summary>
    /// Decode the regions read by Lean on demand (see LazyRegion.cs). On by default; also turned
    /// off by the environment variable LEANINTERP_OLEAN_LAZY=0.
    /// </summary>
    public static bool LazyDecoding { get => LazyRegion.Enabled; set => LazyRegion.Enabled = value; }

    /// <summary>
    /// Opens a compacted region for decoding on demand: the file stays mapped, and objects are
    /// created when they are first reached. Falls back to `Read` if the address range of the
    /// file is already in use in this process.
    /// </summary>
    public static CompactedRegionData ReadLazy(string path, params CompactedRegionData[] deps) =>
        LazyRegion.Open(path, deps);

    /// <summary>Number of lazily decoded regions, their total size and the objects created so far.</summary>
    public static (int Regions, long Bytes, long Objects) LazyStatistics => LazyRegion.Stats();

    public static OleanHeader ReadHeader(string path)
    {
        var b = new byte[OleanHeader.Size];
        using var f = File.OpenRead(path);
        int n = f.ReadAtLeast(b, b.Length, throwOnEndOfStream: false);
        if (n != b.Length || !OleanHeader.TryParse(b, out var h))
            throw new OleanFormatException("invalid header");
        return h;
    }

    /// <summary>
    /// Reads a compacted region. Pointers outside of the file are resolved in `deps` (e.g. the
    /// `.olean` part when reading the `.olean.server` part). The objects are persistent.
    /// </summary>
    public static CompactedRegionData Read(string path, params CompactedRegionData[] deps) =>
        RegionReader.ReadFile(path, deps);

    /// <summary>
    /// Releases the per-thread scratch buffers of the reader (e.g. after importing). They are
    /// recreated on demand; pointer resolution into recently read regions becomes a bit slower.
    /// </summary>
    public static void ReleaseScratchBuffers() => RegionReader.ReleaseScratch();

    /// <summary>Reads a compacted region from an in-memory image of the file.</summary>
    public static CompactedRegionData Parse(string path, byte[] image, params CompactedRegionData[] deps) =>
        RegionReader.Parse(path, image, image.LongLength, deps);

    /// <summary>`lean_name_hash` of a `Name` object.</summary>
    public static ulong NameHash(Obj n) =>
        LeanRt.lean_is_scalar(n) ? 1723UL : LeanRt.lean_ctor_get_uint64_s(n, 0);

    /// <summary>Hash of a `Name` built from its components (for checks): Name.str hash = mixHash(p, String.hash).</summary>
    public static ulong ComputeNameHash(Obj n)
    {
        if (LeanRt.lean_is_scalar(n)) return 1723UL;
        ulong ph = ComputeNameHash(LeanRt.lean_ctor_get(n, 0));
        Obj f = LeanRt.lean_ctor_get(n, 1);
        if (n.m_tag == 1)
            return LeanHash.Mix(ph, LeanHash.HashStr(LeanRt.lean_string_span(f), 11));
        var v = LeanRt.lean_nat_to_big(f);
        return LeanHash.Mix(ph, v < ulong.MaxValue + (System.Numerics.BigInteger)1 ? (ulong)v : 17UL);
    }

    /// <summary>The deterministic base address native Lean derives from the module name.</summary>
    public static ulong BaseAddrForKey(Obj name)
    {
        ulong a = NameHash(name);
        a %= 0x7f0000000000UL;
        a &= ~(OleanLayout.PartAlign - 1);
        return a;
    }

    public static ObjectCompactor NewCompactor(Obj key, IEnumerable<CompactedRegionData> deps = null, bool allowClosures = false) =>
        new ObjectCompactor(BaseAddrForKey(key), deps, allowClosures, UseGmpLayout);

    /// <summary>
    /// Compacts `data` as the next part of `compactor` and returns the file image
    /// (port of the body of `lean_compacted_region_save`).
    /// </summary>
    /// <param name="v3">Write the `v3` format (closure tables); defaults to the compactor's `AllowClosures`.
    /// As in native Lean, closures are accepted iff the compactor was created with `allowClosures`.</param>
    public static byte[] SavePart(ObjectCompactor compactor, Obj data, bool? v3 = null)
    {
        bool isV3 = v3 ?? compactor.AllowClosures;
        const long ALIGN = (long)OleanLayout.PartAlign;
        if (compactor.Size % ALIGN != 0)
            compactor.Alloc(ALIGN - compactor.Size % ALIGN);
        long fileOffset = compactor.Size;
        compactor.Alloc(OleanHeader.Size);
        var header = new OleanHeader
        {
            Version = (byte)(isV3 ? 3 : 2),
            Flags = (byte)(compactor.Gmp ? 1 : 0),
            LeanVersion = LeanVersion,
            GitHash = GitHash,
            BaseAddr = compactor.BaseAddr + (ulong)fileOffset,
        };
        var ms = new MemoryStream();
        var hb = new byte[OleanHeader.Size];
        header.WriteTo(hb);
        ms.Write(hb);
        if (!isV3)
        {
            compactor.Compact(data);
            ms.Write(compactor.Data.Slice((int)(fileOffset + OleanHeader.Size)));
        }
        else
        {
            compactor.Alloc(8); // data_size slot
            compactor.Compact(data);
            long dataOffset = fileOffset + OleanHeader.Size + 8;
            long dataSize = compactor.Size - dataOffset;
            ms.Write(BitConverter.GetBytes((ulong)dataSize));
            ms.Write(compactor.Data.Slice((int)dataOffset, (int)dataSize));
            var offs = compactor.ClosureOffsets;
            var fileOffs = offs.Select(o => (ulong)(o - dataOffset)).ToList();
            offs.Clear();
            compactor.Alloc(4);
            ms.Write(BitConverter.GetBytes((uint)fileOffs.Count));
            if (fileOffs.Count > 0)
            {
                compactor.Alloc(8L * fileOffs.Count);
                foreach (var o in fileOffs) ms.Write(BitConverter.GetBytes(o));
            }
            // "Library" table: natively the shared libraries the closures' functions live in;
            // here one entry per function, by name (entry i: u64 i, u32 length, name).
            unsafe
            {
                var funs = fileOffs.Count > 0 ? compactor.Functions : new List<nint>();
                var names = funs.Select(f => FunctionTable.Encode(FunctionTable.NameOf((void*)f))).ToList();
                compactor.Alloc(4 + names.Sum(n => 8L + 4 + n.Length));
                ms.Write(BitConverter.GetBytes((uint)names.Count));
                for (int i = 0; i < names.Count; i++)
                {
                    ms.Write(BitConverter.GetBytes((ulong)i));
                    ms.Write(BitConverter.GetBytes((uint)names[i].Length));
                    ms.Write(names[i]);
                }
            }
        }
        return ms.ToArray();
    }

    /// <summary>Writes `image` to `path` atomically (temp file + rename), as native Lean does.</summary>
    public static void WriteAtomically(string path, byte[] image)
    {
        string tmp = path + ".tmp." + Environment.ProcessId;
        try
        {
            File.WriteAllBytes(tmp, image);
        }
        catch
        {
            try { File.Delete(tmp); } catch { }
            throw;
        }
        File.Move(tmp, path, overwrite: true);
    }

    /// <summary>Saves `data` to `path` in a fresh compactor (`saveModuleData`).</summary>
    public static void Write(string path, Obj key, Obj data)
    {
        var c = NewCompactor(key);
        WriteAtomically(path, SavePart(c, data));
    }
}
