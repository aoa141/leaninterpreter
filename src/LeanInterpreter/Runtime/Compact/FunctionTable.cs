// Names for the functions closures point to, so that closures can be written to a file
// (`CompactedRegion.save (allowClosures := true)`, used by `lean --incr-save`) and read back by
// another process.
//
// Natively a closure's function pointer is stored relative to the base address of the shared
// library it lives in, and the file lists those libraries. Here every function a closure can
// point to is a static method of a LeanInterpreter assembly (generated code, or a runtime helper), so
// the file lists the *methods*: the `m_fun` slot of a saved closure holds an index into that
// list, and the reader resolves each entry by assembly, type and method name. The files are
// therefore only readable by a LeanInterpreter build that has the same methods (the same generated
// code), which is also the native restriction (same binary).

using System.Reflection;
using System.Text;

namespace LeanInterpreter.Runtime.Compact;

internal static unsafe class FunctionTable
{
    const string Prefix = "LeanInterpreter.fn";
    const BindingFlags Statics = BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static | BindingFlags.DeclaredOnly;

    static readonly object s_lock = new();
    static Dictionary<nint, MethodInfo> s_byPointer;
    static int s_assembliesSeen;

    /// <summary>The assemblies whose static methods closures may point to: LeanInterpreter's, and the host program.</summary>
    static bool IsOurs(Assembly a) =>
        (a.GetName().Name ?? "").StartsWith("LeanInterpreter", StringComparison.Ordinal) || a == Assembly.GetEntryAssembly();

    /// <summary>Entry point of every static method of the loaded LeanInterpreter assemblies.</summary>
    static Dictionary<nint, MethodInfo> ByPointer()
    {
        var assemblies = AppDomain.CurrentDomain.GetAssemblies().Where(IsOurs).ToArray();
        lock (s_lock)
        {
            if (s_byPointer != null && s_assembliesSeen == assemblies.Length) return s_byPointer;
            var map = new System.Collections.Concurrent.ConcurrentDictionary<nint, MethodInfo>();
            var types = new List<Type>();
            foreach (var a in assemblies)
            {
                try { types.AddRange(a.GetTypes()); }
                catch (ReflectionTypeLoadException e) { types.AddRange(e.Types.Where(t => t != null)); }
            }
            Parallel.ForEach(types, t =>
            {
                if (t.ContainsGenericParameters) return;
                foreach (var m in t.GetMethods(Statics))
                {
                    if (m.ContainsGenericParameters || m.IsAbstract) continue;
                    try { map.TryAdd(m.MethodHandle.GetFunctionPointer(), m); }
                    catch (Exception) { /* not callable through a pointer */ }
                }
            });
            s_byPointer = new Dictionary<nint, MethodInfo>(map);
            s_assembliesSeen = assemblies.Length;
            return s_byPointer;
        }
    }

    /// <summary>The name written to the file for the function `fn` of a closure.</summary>
    public static string NameOf(void* fn)
    {
        if (!ByPointer().TryGetValue((nint)fn, out var m))
            throw new OleanFormatException("cannot save a closure whose function is not a static method of a LeanInterpreter assembly");
        var type = m.DeclaringType;
        // position among the overloads with the same name and arity (almost always 0)
        var same = Overloads(type, m.Name, m.GetParameters().Length);
        int ordinal = same.IndexOf(m);
        return string.Join("\t", Prefix, type.Assembly.GetName().Name, type.FullName, m.Name,
            m.GetParameters().Length.ToString(System.Globalization.CultureInfo.InvariantCulture),
            ordinal.ToString(System.Globalization.CultureInfo.InvariantCulture));
    }

    /// <summary>The function a name written by <see cref="NameOf"/> refers to, or null if this process does not have it.</summary>
    public static void* Resolve(string name)
    {
        var p = name.Split('\t');
        if (p.Length != 6 || p[0] != Prefix) return null;
        if (!int.TryParse(p[4], out int arity) || !int.TryParse(p[5], out int ordinal)) return null;
        var type = s_types.GetOrAdd((p[1], p[2]), static k =>
            AppDomain.CurrentDomain.GetAssemblies().FirstOrDefault(a => a.GetName().Name == k.Item1)?.GetType(k.Item2, throwOnError: false));
        if (type == null) return null;
        var same = Overloads(type, p[3], arity);
        if (ordinal < 0 || ordinal >= same.Count) return null;
        return (void*)same[ordinal].MethodHandle.GetFunctionPointer();
    }

    static readonly System.Collections.Concurrent.ConcurrentDictionary<(string, string), Type> s_types = new();

    /// <summary>The static methods of `type` called `name` with `arity` parameters, in metadata order (looked up by name: the generated classes have thousands of methods).</summary>
    static List<MethodInfo> Overloads(Type type, string name, int arity) =>
        type.GetMember(name, MemberTypes.Method, Statics).Cast<MethodInfo>()
            .Where(x => x.GetParameters().Length == arity && !x.ContainsGenericParameters)
            .OrderBy(x => x.MetadataToken).ToList();

    public static byte[] Encode(string name) => Encoding.UTF8.GetBytes(name);
}
