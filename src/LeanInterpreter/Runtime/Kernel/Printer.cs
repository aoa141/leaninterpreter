// Port of library/print.cpp: very basic printer for expressions (`lean_expr_dbg_to_string`).

using System.Text;
using LeanInterpreter.Runtime;
using static LeanInterpreter.Runtime.LeanRt;

namespace LeanInterpreter.Kernel;

internal static class ExprPrinter
{
    static bool IsUsedName(Expr t, Name n)
    {
        bool found = false;
        ForEachFn.ForEachOffset(t, (e, _) =>
        {
            if (found) return false;
            if ((e.IsConst && e.ConstName.GetRoot() == n) || (e.IsFVar && e.FVarName == n))
            {
                found = true;
                return false;
            }
            return true;
        });
        return found;
    }

    static Name PickUnusedName(Expr t, Name s)
    {
        Name r = s;
        uint i = 1;
        while (IsUsedName(t, r))
        {
            r = s.AppendAfter(i);
            i++;
        }
        return r;
    }

    static bool IsNumericalName(Name n)
    {
        while (!n.IsAtomic) n = n.GetPrefix();
        return n.IsNumeral;
    }

    static Name CleanupName(Name n) => IsNumericalName(n) ? KConsts.X : n;

    static (Expr, Expr) BindingBodyFresh(Expr b)
    {
        Name n = CleanupName(b.BindingName);
        n = PickUnusedName(b.BindingBody, n);
        Expr c = Expr.MkFVar(n);
        return (Inst.Instantiate(b.BindingBody, c), c);
    }

    static (Expr, Expr) LetBodyFresh(Expr b)
    {
        Name n = CleanupName(b.LetName);
        n = PickUnusedName(b.LetBody, n);
        Expr c = Expr.MkFVar(n);
        return (Inst.Instantiate(b.LetBody, c), c);
    }

    static Name FixName(Name a)
    {
        if (a.IsAtomic)
        {
            if (a.IsNumeral) return KConsts.M;
            return a;
        }
        Name p = FixName(a.GetPrefix());
        if (p == a.GetPrefix()) return a;
        if (a.IsNumeral) return Name.MkNum(p, a.GetNumeralObj());
        return Name.MkStr(p, a.GetStringObj());
    }

    /// <summary>`escaped`: escape double quotes.</summary>
    static void AppendEscaped(StringBuilder sb, string s)
    {
        int nul = s.IndexOf('\0');
        if (nul >= 0) s = s.Substring(0, nul); // C string semantics
        foreach (char c in s)
        {
            if (c == '"') sb.Append('\\');
            sb.Append(c);
        }
    }

    sealed class Fn
    {
        readonly StringBuilder m_out;
        public Fn(StringBuilder sb) { m_out = sb; }

        static bool IsAtomicP(Expr a)
        {
            if (Expr.IsAtomic(a)) return true;
            if (a.IsProj) return IsAtomicP(a.ProjExpr);
            return false;
        }

        void PrintChild(Expr a)
        {
            if (IsAtomicP(a)) Print(a);
            else { m_out.Append('('); Print(a); m_out.Append(')'); }
        }

        void PrintSort(Expr a)
        {
            Level l = a.SortLevel;
            if (l.IsZero) m_out.Append("Prop");
            else if (Level.IsOne(l)) m_out.Append("Type");
            else if (l.IsSucc) { m_out.Append("Type.{"); Level.Print(m_out, l.SuccOf); m_out.Append('}'); }
            else { m_out.Append("Sort.{"); Level.Print(m_out, l); m_out.Append('}'); }
        }

        void PrintApp(Expr e)
        {
            Expr f = e.AppFn;
            if (f.IsApp) Print(f);
            else PrintChild(f);
            m_out.Append(' ');
            PrintChild(e.AppArg);
        }

        static bool IsArrowP(Expr t) => Expr.IsArrow(t) && t.BindingInfo == BinderInfo.Default;

        void PrintArrowBody(Expr a)
        {
            if (IsAtomicP(a) || IsArrowP(a)) Print(a);
            else PrintChild(a);
        }

        void PrintBinding(string bname, Expr e, bool isLambda)
        {
            ExprKind k = e.Kind;
            m_out.Append(bname);
            while (e.Kind == k && !IsArrowP(e))
            {
                m_out.Append(' ');
                var p = BindingBodyFresh(e);
                Expr n = p.Item2;
                BinderInfo bi = e.BindingInfo;
                if (bi == BinderInfo.Implicit) m_out.Append('{');
                else if (bi == BinderInfo.InstImplicit) m_out.Append('[');
                else if (bi == BinderInfo.StrictImplicit) m_out.Append("{{");
                else m_out.Append('(');
                new Fn(m_out).Print(n);
                m_out.Append(" : ");
                Print(e.BindingDomain);
                if (bi == BinderInfo.Implicit) m_out.Append('}');
                else if (bi == BinderInfo.InstImplicit) m_out.Append(']');
                else if (bi == BinderInfo.StrictImplicit) m_out.Append("}}");
                else m_out.Append(')');
                e = p.Item1;
            }
            m_out.Append(isLambda ? " => " : ", ");
            Print(e);
        }

        void PrintLet(Expr e)
        {
            m_out.Append(e.LetNonDep ? "have " : "let ");
            var p = LetBodyFresh(e);
            new Fn(m_out).Print(p.Item2);
            m_out.Append(" : ");
            Print(e.LetType);
            m_out.Append(" := ");
            Print(e.LetValue);
            m_out.Append("; ");
            Print(p.Item1);
        }

        void PrintConst(Expr a)
        {
            Obj ls = a.ConstLevels;
            Name.Display(m_out, a.ConstName.Raw);
            if (!KList.IsNil(ls))
            {
                m_out.Append(".{");
                bool first = true;
                foreach (var l in KList.Iter(ls))
                {
                    if (first) first = false; else m_out.Append(", ");
                    Level.Print(m_out, new Level(l));
                }
                m_out.Append('}');
            }
        }

        void PrintMData(Expr a)
        {
            m_out.Append("[mdata ");
            Obj k = a.MDataData;
            while (!KList.IsNil(k))
            {
                Obj entry = KList.Head(k);
                Name.Display(m_out, lean_ctor_get(entry, 0));
                m_out.Append(':');
                Obj v = lean_ctor_get(entry, 1);
                switch (lean_obj_tag(v))
                {
                    case 1: m_out.Append(lean_ctor_get_uint8_s(v, 0) != 0 ? '1' : '0'); break;
                    case 2: Name.Display(m_out, lean_ctor_get(v, 0)); break;
                    case 3: m_out.Append(Nat.ToDecimal(lean_ctor_get(v, 0))); break;
                    case 0: AppendEscaped(m_out, lean_string_to_net(lean_ctor_get(v, 0))); break;
                }
                m_out.Append(' ');
                k = KList.Tail(k);
            }
            Print(a.MDataExpr);
            m_out.Append(']');
        }

        public void Print(Expr a)
        {
            KernelLimits.CheckStack("print");
            switch (a.Kind)
            {
                case ExprKind.MVar:
                    m_out.Append('?');
                    Name.Display(m_out, FixName(a.MVarName).Raw);
                    break;
                case ExprKind.FVar:
                    Name.Display(m_out, a.FVarName.Raw);
                    break;
                case ExprKind.MData:
                    PrintMData(a);
                    break;
                case ExprKind.Proj:
                    PrintChild(a.ProjExpr);
                    m_out.Append('.');
                    m_out.Append((Nat.ToBig(a.ProjIdx) + 1).ToString());
                    break;
                case ExprKind.BVar:
                    m_out.Append('#');
                    m_out.Append(Nat.ToDecimal(a.BVarIdx));
                    break;
                case ExprKind.Const:
                    PrintConst(a);
                    break;
                case ExprKind.App:
                    PrintApp(a);
                    break;
                case ExprKind.Let:
                    PrintLet(a);
                    break;
                case ExprKind.Lambda:
                    PrintBinding("fun", a, true);
                    break;
                case ExprKind.Pi:
                    if (!IsArrowP(a))
                    {
                        PrintBinding("forall", a, false);
                    }
                    else
                    {
                        PrintChild(a.BindingDomain);
                        m_out.Append(" -> ");
                        PrintArrowBody(Expr.LowerLooseBVars(a.BindingBody, 1));
                    }
                    break;
                case ExprKind.Sort:
                    PrintSort(a);
                    break;
                case ExprKind.Lit:
                    if (a.IsNatLit)
                    {
                        m_out.Append(Nat.ToDecimal(a.LitNat));
                    }
                    else
                    {
                        m_out.Append('"');
                        AppendEscaped(m_out, lean_string_to_net(a.LitString));
                        m_out.Append('"');
                    }
                    break;
            }
        }
    }

    public static string ToString(Expr e)
    {
        var sb = new StringBuilder();
        new Fn(sb).Print(e);
        return sb.ToString();
    }
}
