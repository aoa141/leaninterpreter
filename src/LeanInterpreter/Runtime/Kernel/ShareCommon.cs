// A kernel-local version of `sharecommon_persistent_fn` (runtime/sharecommon.cpp): maximally
// share the subterms of a Lean object graph (hash-consing). Used when type checking theorems.
// The result is a structurally identical object in which equal subobjects are pointer-equal.

using System.Runtime.CompilerServices;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

internal sealed class ShareCommon
{
    /// <summary>Shallow structural equality: same kind, scalar data and pointer-equal children.</summary>
    sealed class ShallowComparer : IEqualityComparer<Obj>
    {
        public static readonly ShallowComparer Instance = new();

        public bool Equals(Obj a, Obj b)
        {
            if (ReferenceEquals(a, b)) return true;
            if (a.m_tag != b.m_tag) return false;
            byte tag = a.m_tag;
            if (tag <= LeanMaxCtorTag)
            {
                if (a.m_other != b.m_other || a.m_cs_sz != b.m_cs_sz) return false;
                int n = a.m_other;
                for (int i = 0; i < n; i++)
                    if (!ReferenceEquals(lean_ctor_get(a, (uint)i), lean_ctor_get(b, (uint)i))) return false;
                var ca = (Ctor)a; var cb = (Ctor)b;
                if (ca.s0 != cb.s0) return false;
                if (ca.sx == null) return cb.sx == null;
                return cb.sx != null && ca.sx.AsSpan().SequenceEqual(cb.sx);
            }
            switch (tag)
            {
                case LeanString: return Name.StringEq(a, b);
                case LeanMPZ: return ((MpzObj)a).m_value == ((MpzObj)b).m_value;
                case LeanArray:
                {
                    var x = (ArrayObj)a; var y = (ArrayObj)b;
                    if (x.m_size != y.m_size) return false;
                    for (long i = 0; i < x.m_size; i++)
                        if (!ReferenceEquals(x.m_data[i], y.m_data[i])) return false;
                    return true;
                }
            }
            return false;
        }

        public int GetHashCode(Obj o)
        {
            byte tag = o.m_tag;
            if (tag <= LeanMaxCtorTag)
            {
                var h = new HashCode();
                h.Add(tag);
                int n = o.m_other;
                for (int i = 0; i < n; i++) h.Add(RuntimeHelpers.GetHashCode(lean_ctor_get(o, (uint)i)));
                h.Add(((Ctor)o).s0);
                return h.ToHashCode();
            }
            switch (tag)
            {
                case LeanString: return (int)LeanHash.HashStr(lean_string_span(o), 11);
                case LeanMPZ: return ((MpzObj)o).m_value.GetHashCode();
                case LeanArray:
                {
                    var x = (ArrayObj)o;
                    var h = new HashCode();
                    for (long i = 0; i < x.m_size; i++) h.Add(RuntimeHelpers.GetHashCode(x.m_data[i]));
                    return h.ToHashCode();
                }
            }
            return RuntimeHelpers.GetHashCode(o);
        }
    }

    readonly Dictionary<Obj, Obj> m_cache = new(ReferenceEqualityComparer.Instance);
    readonly Dictionary<Obj, Obj> m_set = new(ShallowComparer.Instance);

    Obj Intern(Obj candidate)
    {
        if (m_set.TryGetValue(candidate, out var existing)) return existing;
        m_set.Add(candidate, candidate);
        return candidate;
    }

    Obj Visit(Obj a)
    {
        if (lean_is_scalar(a)) return a;
        if (m_cache.TryGetValue(a, out var r)) return r;
        KernelLimits.CheckStack("sharecommon");
        byte tag = a.m_tag;
        Obj result;
        if (tag <= LeanMaxCtorTag)
        {
            int n = a.m_other;
            Obj[] newFields = n == 0 ? Array.Empty<Obj>() : new Obj[n];
            bool changed = false;
            for (int i = 0; i < n; i++)
            {
                Obj c = lean_ctor_get(a, (uint)i);
                Obj nc = Visit(c);
                newFields[i] = nc;
                if (!ReferenceEquals(c, nc)) changed = true;
            }
            Obj candidate = a;
            if (changed)
            {
                candidate = lean_alloc_ctor(tag, (uint)n, a.m_cs_sz);
                for (int i = 0; i < n; i++) lean_ctor_set(candidate, (uint)i, RC.Own(newFields[i]));
                var src = (Ctor)a; var dst = (Ctor)candidate;
                dst.s0 = src.s0;
                if (src.sx != null) dst.sx = (byte[])src.sx.Clone();
            }
            result = Intern(candidate);
        }
        else if (tag == LeanString || tag == LeanMPZ)
        {
            result = Intern(a);
        }
        else
        {
            result = a;
        }
        m_cache[a] = result;
        return result;
    }

    /// <summary>Share `a` (borrowed); the result is a borrowed view kept alive by this object or `a`.</summary>
    public Obj Share(Obj a) => Visit(a);
}
