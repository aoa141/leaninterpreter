// Port of the file system primitives of runtime/io.cpp (and the current directory functions of
// runtime/process.cpp) on top of System.IO.

using System.Numerics;
using System.Security.Cryptography;

namespace LeanInterpreter.Runtime;

public static unsafe partial class LeanRt
{
    // ------------------------------------------------------------------
    // Helpers

    /// <summary>`lean_int64_to_int` (same boxing convention as the Numbers area).</summary>
    internal static Obj IoInt64ToInt(long n)
    {
        if (int.MinValue <= n && n <= int.MaxValue) return lean_box((uint)(int)n);
        return lean_alloc_mpz(new BigInteger(n));
    }

    /// <summary>`lean_uint64_of_nat`.</summary>
    internal static ulong IoUInt64OfNat(Obj n)
    {
        if (lean_is_scalar(n)) return lean_unbox(n);
        return (ulong)(lean_nat_to_big(n) & ulong.MaxValue);
    }

    /// <summary>Whether `path` names an existing file system entry (including dangling symlinks).</summary>
    internal static bool IoEntryExists(string path)
    {
        try
        {
            if (File.Exists(path) || Directory.Exists(path)) return true;
            return new FileInfo(path).LinkTarget != null;
        }
        catch (Exception) { return false; }
    }

    static bool IoIsSymlink(string path)
    {
        try { return new FileInfo(path).LinkTarget != null; }
        catch (Exception) { return false; }
    }

    /// <summary>`errno` for a missing path: `ENOTDIR` if a proper prefix is a file, `ENOENT` otherwise.</summary>
    static int IoMissingErrno(string path)
    {
        try
        {
            var dir = Path.GetDirectoryName(Path.GetFullPath(path));
            while (!string.IsNullOrEmpty(dir))
            {
                if (Directory.Exists(dir)) return LeanErrno.ENOENT;
                if (File.Exists(dir)) return LeanErrno.ENOTDIR;
                dir = Path.GetDirectoryName(dir);
            }
        }
        catch (Exception) { }
        return LeanErrno.ENOENT;
    }

    /// <summary>
    /// What `GetFinalPathNameByHandle` gives natively: every link and junction on the path
    /// resolved, every component spelled as on disk (case, long names), the drive letter in
    /// lower case.
    /// </summary>
    static string IoRealPathWindows(string path)
    {
        var full = Path.GetFullPath(path);
        if (!IoEntryExists(full)) return null;
        try
        {
            string root = Path.GetPathRoot(full);
            var todo = new List<string>(full.Substring(root.Length).Split(Path.DirectorySeparatorChar, StringSplitOptions.RemoveEmptyEntries));
            string cur = root.ToUpperInvariant();
            int links = 0;
            for (int i = 0; i < todo.Count; i++)
            {
                // the name as stored (a search for the exact name also finds it by its short name)
                string name = Directory.EnumerateFileSystemEntries(cur, todo[i]).Select(Path.GetFileName).FirstOrDefault();
                if (name == null) return null;
                string next = Path.Combine(cur, name);
                string target = new FileInfo(next).LinkTarget;
                if (target == null) { cur = next; continue; }
                if (++links > 40) return null;
                // continue with the components of the target, then the rest of the path
                string t = Path.GetFullPath(target, cur);
                string troot = Path.GetPathRoot(t);
                var rest = todo.GetRange(i + 1, todo.Count - i - 1);
                todo = new List<string>(t.Substring(troot.Length).Split(Path.DirectorySeparatorChar, StringSplitOptions.RemoveEmptyEntries));
                todo.AddRange(rest);
                cur = troot.ToUpperInvariant();
                i = -1;
            }
            full = cur;
        }
        catch (Exception) { }
        if (full.Length >= 2 && full[1] == ':') full = char.ToLowerInvariant(full[0]) + full.Substring(1);
        return full;
    }

    /// <summary>`realpath(3)`: absolute path with all symbolic links resolved; null if it does not exist.</summary>
    public static string IoRealPath(string path)
    {
        path = LeanContext.ResolvePath(path);
        if (OperatingSystem.IsWindows()) return IoRealPathWindows(path);
        string start = Path.IsPathRooted(path) ? path : Path.Combine(Directory.GetCurrentDirectory(), path);
        var todo = new List<string>(start.Split('/', StringSplitOptions.RemoveEmptyEntries));
        string cur = "/";
        int links = 0;
        int i = 0;
        while (i < todo.Count)
        {
            string part = todo[i++];
            if (part == ".") continue;
            if (part == "..")
            {
                cur = Path.GetDirectoryName(cur) ?? "/";
                continue;
            }
            string next = cur == "/" ? "/" + part : cur + "/" + part;
            string target;
            try { target = new FileInfo(next).LinkTarget; }
            catch (Exception) { return null; }
            if (target != null)
            {
                if (++links > 40) return null;
                var rest = todo.GetRange(i, todo.Count - i);
                todo = new List<string>(target.Split('/', StringSplitOptions.RemoveEmptyEntries));
                todo.AddRange(rest);
                i = 0;
                if (target.StartsWith('/')) cur = "/";
                continue;
            }
            if (Directory.Exists(next)) { cur = next; continue; }
            if (File.Exists(next) && i == todo.Count) { cur = next; continue; }
            return null;
        }
        return cur;
    }

    // ------------------------------------------------------------------
    // Externs

    /* IO.setAccessRights (filename : @& String) (mode : UInt32) : IO Unit */
    public static Obj lean_chmod(Obj filename, uint mode)
    {
        if (IoHasNul(filename)) return IoEmbeddedNulError(filename);
        string path = LeanContext.ResolvePath(lean_string_to_net(filename));
        try
        {
            if (!IoEntryExists(path)) return LeanIOErrors.DecodeResult(IoMissingErrno(path), filename);
            if (OperatingSystem.IsWindows())
            {
                var attrs = File.GetAttributes(path);
                if ((mode & 0x80) == 0) attrs |= FileAttributes.ReadOnly; else attrs &= ~FileAttributes.ReadOnly;
                File.SetAttributes(path, attrs);
            }
            else
            {
                File.SetUnixFileMode(path, (UnixFileMode)(mode & 0xFFF));
            }
            return IoOkUnit();
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, filename); }
    }

    /* realPath (fname : FilePath) : IO FilePath */
    public static Obj lean_io_realpath(Obj filename)
    {
        if (IoHasNul(filename))
        {
            var r = IoEmbeddedNulError(filename);
            lean_dec(filename);
            return r;
        }
        string res;
        try { res = IoRealPath(lean_string_to_net(filename)); }
        catch (Exception) { res = null; }
        if (res == null)
        {
            // mk_file_not_found_error
            var err = LeanIOErrors.MkFile("lean_mk_io_error_no_file_or_directory", filename, (uint)LeanErrno.ENOENT, lean_mk_string(""));
            return lean_io_result_mk_error(err);
        }
        lean_dec(filename);
        return lean_io_result_mk_ok(lean_mk_string(res));
    }

    /*
    structure DirEntry where
      root     : String
      filename : String
    readDir : @& FilePath → IO (Array DirEntry)
    */
    public static Obj lean_io_read_dir(Obj dirname)
    {
        if (IoHasNul(dirname)) return IoEmbeddedNulError(dirname);
        string path = LeanContext.ResolvePath(lean_string_to_net(dirname));
        try
        {
            if (!Directory.Exists(path))
            {
                int en = File.Exists(path) ? LeanErrno.ENOTDIR : IoMissingErrno(path);
                return LeanIOErrors.DecodeResult(en, dirname);
            }
            var entries = new List<Obj>();
            foreach (var e in Directory.EnumerateFileSystemEntries(path))
            {
                string name = Path.GetFileName(e);
                if (name == "." || name == "..") continue;
                var lentry = lean_alloc_ctor(0, 2, 0);
                lean_inc(dirname);
                lean_ctor_set(lentry, 0, dirname);
                lean_ctor_set(lentry, 1, lean_mk_string(name));
                entries.Add(lentry);
            }
            return lean_io_result_mk_ok(MkArray(entries));
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, dirname); }
    }

    static Obj IoTimeToObj(DateTime utc)
    {
        long ticks = utc.Ticks - DateTime.UnixEpoch.Ticks;
        long sec = Math.DivRem(ticks, TimeSpan.TicksPerSecond, out long rem);
        if (rem < 0) { sec--; rem += TimeSpan.TicksPerSecond; }
        var o = lean_alloc_ctor(0, 1, 4);
        lean_ctor_set(o, 0, IoInt64ToInt(sec));
        lean_ctor_set_uint32(o, 8, (uint)(rem * 100));
        return o;
    }

    /*
    structure Metadata where
      accessed : SystemTime
      modified : SystemTime
      byteSize : UInt64
      type     : FileType
      numLinks : UInt64
    */
    static Obj IoMetadata(Obj filename, bool follow)
    {
        if (IoHasNul(filename)) return IoEmbeddedNulError(filename);
        string path = LeanContext.ResolvePath(lean_string_to_net(filename));
        try
        {
            if (!IoEntryExists(path)) return LeanIOErrors.DecodeResult(IoMissingErrno(path), filename);
            FileSystemInfo fi = Directory.Exists(path) ? new DirectoryInfo(path) : new FileInfo(path);
            string linkTarget = fi.LinkTarget;
            byte type;
            ulong size;
            if (linkTarget != null && !follow)
            {
                type = 2;
                size = (ulong)System.Text.Encoding.UTF8.GetByteCount(linkTarget);
            }
            else
            {
                if (linkTarget != null)
                {
                    var t = fi.ResolveLinkTarget(true);
                    if (t == null || !(File.Exists(t.FullName) || Directory.Exists(t.FullName)))
                        return LeanIOErrors.DecodeResult(LeanErrno.ENOENT, filename);
                    fi = Directory.Exists(t.FullName) ? new DirectoryInfo(t.FullName) : new FileInfo(t.FullName);
                }
                if (fi is DirectoryInfo) { type = 0; size = 0; }
                else
                {
                    var f = (FileInfo)fi;
                    size = (ulong)f.Length;
                    type = (f.Attributes & FileAttributes.Device) != 0 ? (byte)3 : (byte)1;
                }
            }
            var mdata = lean_alloc_ctor(0, 2, 2 * 8 + 1);
            lean_ctor_set(mdata, 0, IoTimeToObj(fi.LastAccessTimeUtc));
            lean_ctor_set(mdata, 1, IoTimeToObj(fi.LastWriteTimeUtc));
            lean_ctor_set_uint64(mdata, 2 * 8, size);
            lean_ctor_set_uint64(mdata, 2 * 8 + 8, type == 1 ? IoHardLinks.Count(fi.FullName) : 1);
            lean_ctor_set_uint8(mdata, 2 * 8 + 16, type);
            return lean_io_result_mk_ok(mdata);
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, filename); }
    }

    /* metadata : @& FilePath → IO IO.FS.Metadata */
    public static Obj lean_io_metadata(Obj filename) => IoMetadata(filename, true);

    /* symlinkMetadata : @& FilePath → IO IO.FS.Metadata */
    public static Obj lean_io_symlink_metadata(Obj filename) => IoMetadata(filename, OperatingSystem.IsWindows());

    /* createDir : @& FilePath → IO Unit (mkdir: fails if it exists or the parent is missing) */
    public static Obj lean_io_create_dir(Obj p)
    {
        if (IoHasNul(p)) return IoEmbeddedNulError(p);
        string path = LeanContext.ResolvePath(lean_string_to_net(p));
        try
        {
            if (IoEntryExists(path)) return LeanIOErrors.DecodeResult(LeanErrno.EEXIST, p);
            string parent = Path.GetDirectoryName(Path.GetFullPath(path).TrimEnd('/', '\\'));
            if (!string.IsNullOrEmpty(parent) && !Directory.Exists(parent))
            {
                int en = File.Exists(parent) ? LeanErrno.ENOTDIR : LeanErrno.ENOENT;
                return LeanIOErrors.DecodeResult(en, p);
            }
            Directory.CreateDirectory(path);
            return IoOkUnit();
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, p); }
    }

    /* removeDir : @& FilePath → IO Unit (rmdir) */
    public static Obj lean_io_remove_dir(Obj p)
    {
        if (IoHasNul(p)) return IoEmbeddedNulError(p);
        string path = LeanContext.ResolvePath(lean_string_to_net(p));
        try
        {
            if (!IoEntryExists(path)) return LeanIOErrors.DecodeResult(IoMissingErrno(path), p);
            // Windows: removing a directory link or junction removes the link (`rmdir(2)` fails on a symlink)
            bool link = IoIsSymlink(path);
            if (!Directory.Exists(path) || (link && !OperatingSystem.IsWindows())) return LeanIOErrors.DecodeResult(LeanErrno.ENOTDIR, p);
            if (!link && Directory.EnumerateFileSystemEntries(path).Any())
                return LeanIOErrors.DecodeResult(LeanErrno.ENOTEMPTY, p);
            Directory.Delete(path, false);
            return IoOkUnit();
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, p); }
    }

    /* rename (old new : @& FilePath) : IO Unit (replaces existing files, like rename(2)) */
    public static Obj lean_io_rename(Obj from, Obj to)
    {
        if (IoHasNul(from)) return IoEmbeddedNulError(from);
        if (IoHasNul(to)) return IoEmbeddedNulError(to);
        string fname = lean_string_to_net(from), tname = lean_string_to_net(to);
        string f = LeanContext.ResolvePath(fname), t = LeanContext.ResolvePath(tname);
        int en;
        Exception exn = null;
        try
        {
            if (!IoEntryExists(f)) en = IoMissingErrno(f);
            else if (Directory.Exists(f) && !IoIsSymlink(f))
            {
                if (Directory.Exists(t) && !IoIsSymlink(t))
                {
                    if (Directory.EnumerateFileSystemEntries(t).Any()) en = LeanErrno.ENOTEMPTY;
                    else { Directory.Delete(t); Directory.Move(f, t); return IoOkUnit(); }
                }
                else if (IoEntryExists(t)) en = LeanErrno.ENOTDIR;
                else { Directory.Move(f, t); return IoOkUnit(); }
            }
            else
            {
                if (Directory.Exists(t) && !IoIsSymlink(t)) en = LeanErrno.EISDIR;
                else { File.Move(f, t, true); IoHardLinks.Renamed(f, t); return IoOkUnit(); }
            }
        }
        catch (Exception e) { exn = e; en = LeanIOErrors.ErrnoOf(e); }
        var out_ = lean_mk_string(fname + " and/or " + tname);
        var r = LeanIOErrors.DecodeResult(en, out_);
        lean_dec(out_);
        return r;
    }

    /* hardLink (orig link : @& FilePath) : IO Unit */
    public static Obj lean_io_hard_link(Obj orig, Obj link)
    {
        if (IoHasNul(orig)) return IoEmbeddedNulError(orig);
        if (IoHasNul(link)) return IoEmbeddedNulError(link);
        string o = LeanContext.ResolvePath(lean_string_to_net(orig)), l = LeanContext.ResolvePath(lean_string_to_net(link));
        try
        {
            if (!IoEntryExists(o)) return LeanIOErrors.DecodeResult(IoMissingErrno(o), orig);
            if (IoEntryExists(l)) return LeanIOErrors.DecodeResult(LeanErrno.EEXIST, orig);
            if (Directory.Exists(o)) return LeanIOErrors.DecodeResult(LeanErrno.EPERM, orig);
            string parent = Path.GetDirectoryName(Path.GetFullPath(l));
            if (!string.IsNullOrEmpty(parent) && !Directory.Exists(parent))
                return LeanIOErrors.DecodeResult(File.Exists(parent) ? LeanErrno.ENOTDIR : LeanErrno.ENOENT, orig);
            IoHardLinks.Create(o, l);
            return IoOkUnit();
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, orig); }
    }

    static string IoTempBase()
    {
        string tmp = Path.GetTempPath();
        if (string.IsNullOrEmpty(tmp)) return null;
        char sep = OperatingSystem.IsWindows() ? '\\' : '/';
        if (tmp[tmp.Length - 1] != sep && tmp[tmp.Length - 1] != '/') tmp += sep;
        return tmp;
    }

    static string IoTempName(string baseDir)
    {
        const string chars = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789";
        Span<char> s = stackalloc char[8];
        for (int i = 0; i < 8; i++) s[i] = chars[RandomNumberGenerator.GetInt32(chars.Length)];
        return baseDir + "tmp." + new string(s);
    }

    /* createTempFile : IO (Handle × FilePath) */
    public static Obj lean_io_create_tempfile()
    {
        string baseDir = IoTempBase();
        if (baseDir == null) return LeanIOErrors.DecodeResult(LeanErrno.ENOENT, null);
        for (int attempt = 0; ; attempt++)
        {
            string path = IoTempName(baseDir);
            try
            {
                var fs = new FileStream(path, FileMode.CreateNew, FileAccess.ReadWrite, FileShare.ReadWrite | FileShare.Delete, 4096, FileOptions.None);
                if (!OperatingSystem.IsWindows())
                {
                    try { File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite); } catch (Exception) { }
                }
                var h = LeanHandle.Wrap(new LeanHandle(fs, path));
                return lean_io_result_mk_ok(lean_mk_pair(h, lean_mk_string(path)));
            }
            catch (IOException e) when (attempt < 100 && LeanIOErrors.ErrnoOf(e) == LeanErrno.EEXIST) { }
            catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
        }
    }

    /* createTempDir : IO FilePath */
    public static Obj lean_io_create_tempdir()
    {
        string baseDir = IoTempBase();
        if (baseDir == null) return LeanIOErrors.DecodeResult(LeanErrno.ENOENT, null);
        for (int attempt = 0; ; attempt++)
        {
            string path = IoTempName(baseDir);
            if (IoEntryExists(path))
            {
                if (attempt < 100) continue;
                return LeanIOErrors.DecodeResult(LeanErrno.EEXIST, null);
            }
            try
            {
                if (OperatingSystem.IsWindows()) Directory.CreateDirectory(path);
                else Directory.CreateDirectory(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
                return lean_io_result_mk_ok(lean_mk_string(path));
            }
            catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
        }
    }

    /* removeFile (fname : @& FilePath) : IO Unit (unlink) */
    public static Obj lean_io_remove_file(Obj filename)
    {
        if (IoHasNul(filename)) return IoEmbeddedNulError(filename);
        string path = LeanContext.ResolvePath(lean_string_to_net(filename));
        try
        {
            if (!IoEntryExists(path)) return LeanIOErrors.DecodeResult(IoMissingErrno(path), filename);
            if (Directory.Exists(path) && !IoIsSymlink(path))
                return LeanIOErrors.DecodeResult(OperatingSystem.IsLinux() ? LeanErrno.EISDIR : LeanErrno.EPERM, filename);
            if (OperatingSystem.IsWindows())
            {
                // as in C (`lean_io_remove_file`): read-only files can be removed, too
                var attrs = File.GetAttributes(path);
                if ((attrs & FileAttributes.ReadOnly) != 0) File.SetAttributes(path, attrs & ~FileAttributes.ReadOnly);
            }
            File.Delete(path);
            IoHardLinks.Removed(path);
            return IoOkUnit();
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, filename); }
    }

    /* appPath : IO FilePath */
    public static Obj lean_io_app_path()
    {
        string p = LeanPaths.AppPath;
        if (p == null) return LeanIOErrors.UserErrorResult("failed to locate application");
        return lean_io_result_mk_ok(lean_mk_string(p));
    }

    /* currentDir : IO FilePath */
    public static Obj lean_io_current_dir()
    {
        try { return lean_io_result_mk_ok(lean_mk_string(LeanContext.Proc.Cwd)); }
        catch (Exception) { return LeanIOErrors.UserErrorResult("failed to retrieve current working directory"); }
    }

    /* IO.Process.getCurrentDir : IO FilePath */
    public static Obj lean_io_process_get_current_dir()
    {
        try { return lean_io_result_mk_ok(lean_mk_string(LeanContext.Proc.Cwd)); }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, null); }
    }

    /* IO.Process.setCurrentDir (path : @& FilePath) : IO Unit */
    public static Obj lean_io_process_set_current_dir(Obj path)
    {
        var proc = LeanContext.Proc;
        string p = proc.Resolve(lean_string_to_net(path));
        try
        {
            if (!Directory.Exists(p))
            {
                int en = File.Exists(p) ? LeanErrno.ENOTDIR : IoMissingErrno(p);
                return LeanIOErrors.DecodeResult(en, path);
            }
            // A logical process (in-process child) changes its own working directory only.
            if (proc.HasLogicalCwd) proc.SetCwd(IoRealPath(p) ?? Path.GetFullPath(p));
            else Directory.SetCurrentDirectory(p);
            return IoOkUnit();
        }
        catch (Exception e) { return LeanIOErrors.FromExceptionResult(e, path); }
    }

    /* getEnv (var : @& String) : BaseIO (Option String) */
    public static Obj lean_io_getenv(Obj env_var)
    {
        if (IoHasNul(env_var)) return lean_mk_option_none();
        string name = lean_string_to_net(env_var);
        if (name.Length == 0 || name.Contains('=')) return lean_mk_option_none();
        string v = LeanContext.Proc.GetEnv(name);
        return v != null ? lean_mk_option_some(lean_mk_string(v)) : lean_mk_option_none();
    }
}

/// <summary>Paths used by the runtime.</summary>
public static class LeanPaths
{
    static string s_appPath;

    /// <summary>
    /// The value of `IO.appPath` (Lean locates its library directory relative to it, as
    /// `appDir/../lib/lean`). Defaults to the (symlink-resolved) path of the current process
    /// executable; hosts running under `dotnet` should set it, e.g. to `<toolchain>/bin/lean`.
    /// </summary>
    public static string AppPath
    {
        get
        {
            string own = LeanContext.Proc.AppPath;
            if (own != null) return own;
            if (s_appPath != null) return s_appPath;
            string p = System.Environment.ProcessPath;
            if (p == null) return null;
            try { return LeanRt.IoRealPath(p) ?? p; }
            catch (Exception) { return p; }
        }
        set
        {
            // An in-process child (logical process) has its own executable path.
            var proc = LeanContext.Proc;
            if (ReferenceEquals(proc, LeanLogicalProcess.Root)) s_appPath = value;
            else proc.AppPath = value;
        }
    }
}

/// <summary>
/// Hard links (`IO.FS.hardLink`, `Metadata.numLinks`) in pure managed code.
///
/// .NET 10 has no public API for creating hard links or reading a file's link count, and LeanInterpreter
/// must not use P/Invoke. Links are created with the one managed API that calls `link(2)` /
/// `CreateHardLink`: extracting a hard-link entry of a (here: in-memory, one-entry) tar archive
/// with `System.Formats.Tar`.
///
/// For the link count there is no managed API at all. This class therefore records the links
/// created through `IO.FS.hardLink` *by this OS process* (groups of paths naming the same file),
/// follows `IO.FS.rename`/`IO.FS.removeFile` of those paths, and reports the number of paths of
/// the group that still exist and still look like the same file (same size and modification
/// time). Limitation: files with hard links created by other means (before the process started,
/// by other processes, or by child processes) report `numLinks = 1`, as do directories.
/// </summary>
internal static class IoHardLinks
{
    static readonly object s_lock = new();
    // normalized full path -> the group (set of normalized full paths) it belongs to
    static readonly Dictionary<string, HashSet<string>> s_groups = new(PathComparer);

    static StringComparer PathComparer => OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;

    static string Key(string path)
    {
        try { return Path.GetFullPath(path); }
        catch (Exception) { return path; }
    }

    /// <summary>Creates `link` as a hard link to the existing file `target` (both resolved paths).</summary>
    public static void Create(string target, string link)
    {
        target = Path.GetFullPath(target);
        link = Path.GetFullPath(link);
        // The tar extractor requires the link and its target to be inside the destination
        // directory: extract into their closest common ancestor.
        var cmp = OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal;
        string root = Path.GetDirectoryName(link);
        while (root != null && !target.StartsWith(Path.EndsInDirectorySeparator(root) ? root : root + Path.DirectorySeparatorChar, cmp))
            root = Path.GetDirectoryName(root);
        if (root == null) throw new LeanErrnoException(LeanErrno.EXDEV); // different volumes (Windows)
        using var ms = new MemoryStream();
        using (var w = new System.Formats.Tar.TarWriter(ms, System.Formats.Tar.TarEntryFormat.Pax, leaveOpen: true))
        {
            var e = new System.Formats.Tar.PaxTarEntry(System.Formats.Tar.TarEntryType.HardLink, Path.GetRelativePath(root, link))
            {
                LinkName = Path.GetRelativePath(root, target),
            };
            w.WriteEntry(e);
        }
        ms.Position = 0;
        System.Formats.Tar.TarFile.ExtractToDirectory(ms, root, overwriteFiles: false);
        lock (s_lock)
        {
            if (!s_groups.TryGetValue(target, out var g))
            {
                g = new HashSet<string>(PathComparer) { target };
                s_groups[target] = g;
            }
            Forget(link);
            g.Add(link);
            s_groups[link] = g;
        }
    }

    // must hold s_lock
    static void Forget(string key)
    {
        if (!s_groups.Remove(key, out var g)) return;
        g.Remove(key);
        if (g.Count == 1)
            foreach (var last in g) s_groups.Remove(last);
    }

    /// <summary>`path` was unlinked.</summary>
    public static void Removed(string path)
    {
        if (s_groups.Count == 0) return;
        string key = Key(path);
        lock (s_lock) Forget(key);
    }

    /// <summary>The file `from` was renamed to `to` (replacing it).</summary>
    public static void Renamed(string from, string to)
    {
        if (s_groups.Count == 0) return;
        string f = Key(from), t = Key(to);
        lock (s_lock)
        {
            s_groups.TryGetValue(f, out var g);
            // rename(2) does nothing if both names already refer to the same file
            if (g != null && g.Contains(t)) return;
            Forget(t);
            if (g == null || !s_groups.ContainsKey(f)) return;
            s_groups.Remove(f);
            g.Remove(f);
            g.Add(t);
            s_groups[t] = g;
        }
    }

    /// <summary>The number of hard links of the regular file `path` (see the class comment).</summary>
    public static ulong Count(string path)
    {
        if (s_groups.Count == 0) return 1;
        string key = Key(path);
        lock (s_lock)
        {
            if (!s_groups.TryGetValue(key, out var g)) return 1;
            ulong n = 0;
            try
            {
                var self = new FileInfo(key);
                foreach (var m in g)
                {
                    if (PathComparer.Equals(m, key)) { n++; continue; }
                    var fi = new FileInfo(m);
                    if (fi.Exists && fi.LinkTarget == null && fi.Length == self.Length && fi.LastWriteTimeUtc == self.LastWriteTimeUtc) n++;
                }
            }
            catch (Exception) { }
            return Math.Max(n, 1);
        }
    }
}
