// Function pointers for closures of interpreted functions (generated text, see the comment in
// Machine.cs). A closure of `g` with `k` fixed arguments is `{Stub(g.Arity + 1), fixed = [g.Handle, args...]}`.

using LeanInterpreter.Runtime;

namespace LeanInterpreter.Interp;

internal static unsafe class Stubs
{
    public static void* For(int arity) => arity switch
    {
        1 => (delegate*<Obj, Obj>)&Stub1,
        2 => (delegate*<Obj, Obj, Obj>)&Stub2,
        3 => (delegate*<Obj, Obj, Obj, Obj>)&Stub3,
        4 => (delegate*<Obj, Obj, Obj, Obj, Obj>)&Stub4,
        5 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj>)&Stub5,
        6 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj, Obj>)&Stub6,
        7 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>)&Stub7,
        8 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>)&Stub8,
        9 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>)&Stub9,
        10 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>)&Stub10,
        11 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>)&Stub11,
        12 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>)&Stub12,
        13 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>)&Stub13,
        14 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>)&Stub14,
        15 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>)&Stub15,
        16 => (delegate*<Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj, Obj>)&Stub16,
        _ => (delegate*<Obj[], Obj>)&StubN,
    };

    static Obj Stub1(Obj h)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, []);
        var s = m.Enter(g, out int bp, out var mark);
        
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub2(Obj h, Obj a1)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub3(Obj h, Obj a1, Obj a2)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub4(Obj h, Obj a1, Obj a2, Obj a3)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub5(Obj h, Obj a1, Obj a2, Obj a3, Obj a4)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub6(Obj h, Obj a1, Obj a2, Obj a3, Obj a4, Obj a5)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4, a5]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4); s[bp + 4] = Value.Of(a5);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub7(Obj h, Obj a1, Obj a2, Obj a3, Obj a4, Obj a5, Obj a6)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4, a5, a6]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4); s[bp + 4] = Value.Of(a5); s[bp + 5] = Value.Of(a6);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub8(Obj h, Obj a1, Obj a2, Obj a3, Obj a4, Obj a5, Obj a6, Obj a7)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4, a5, a6, a7]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4); s[bp + 4] = Value.Of(a5); s[bp + 5] = Value.Of(a6); s[bp + 6] = Value.Of(a7);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub9(Obj h, Obj a1, Obj a2, Obj a3, Obj a4, Obj a5, Obj a6, Obj a7, Obj a8)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4, a5, a6, a7, a8]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4); s[bp + 4] = Value.Of(a5); s[bp + 5] = Value.Of(a6); s[bp + 6] = Value.Of(a7); s[bp + 7] = Value.Of(a8);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub10(Obj h, Obj a1, Obj a2, Obj a3, Obj a4, Obj a5, Obj a6, Obj a7, Obj a8, Obj a9)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4, a5, a6, a7, a8, a9]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4); s[bp + 4] = Value.Of(a5); s[bp + 5] = Value.Of(a6); s[bp + 6] = Value.Of(a7); s[bp + 7] = Value.Of(a8); s[bp + 8] = Value.Of(a9);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub11(Obj h, Obj a1, Obj a2, Obj a3, Obj a4, Obj a5, Obj a6, Obj a7, Obj a8, Obj a9, Obj a10)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4); s[bp + 4] = Value.Of(a5); s[bp + 5] = Value.Of(a6); s[bp + 6] = Value.Of(a7); s[bp + 7] = Value.Of(a8); s[bp + 8] = Value.Of(a9); s[bp + 9] = Value.Of(a10);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub12(Obj h, Obj a1, Obj a2, Obj a3, Obj a4, Obj a5, Obj a6, Obj a7, Obj a8, Obj a9, Obj a10, Obj a11)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4); s[bp + 4] = Value.Of(a5); s[bp + 5] = Value.Of(a6); s[bp + 6] = Value.Of(a7); s[bp + 7] = Value.Of(a8); s[bp + 8] = Value.Of(a9); s[bp + 9] = Value.Of(a10); s[bp + 10] = Value.Of(a11);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub13(Obj h, Obj a1, Obj a2, Obj a3, Obj a4, Obj a5, Obj a6, Obj a7, Obj a8, Obj a9, Obj a10, Obj a11, Obj a12)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4); s[bp + 4] = Value.Of(a5); s[bp + 5] = Value.Of(a6); s[bp + 6] = Value.Of(a7); s[bp + 7] = Value.Of(a8); s[bp + 8] = Value.Of(a9); s[bp + 9] = Value.Of(a10); s[bp + 10] = Value.Of(a11); s[bp + 11] = Value.Of(a12);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub14(Obj h, Obj a1, Obj a2, Obj a3, Obj a4, Obj a5, Obj a6, Obj a7, Obj a8, Obj a9, Obj a10, Obj a11, Obj a12, Obj a13)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4); s[bp + 4] = Value.Of(a5); s[bp + 5] = Value.Of(a6); s[bp + 6] = Value.Of(a7); s[bp + 7] = Value.Of(a8); s[bp + 8] = Value.Of(a9); s[bp + 9] = Value.Of(a10); s[bp + 10] = Value.Of(a11); s[bp + 11] = Value.Of(a12); s[bp + 12] = Value.Of(a13);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub15(Obj h, Obj a1, Obj a2, Obj a3, Obj a4, Obj a5, Obj a6, Obj a7, Obj a8, Obj a9, Obj a10, Obj a11, Obj a12, Obj a13, Obj a14)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4); s[bp + 4] = Value.Of(a5); s[bp + 5] = Value.Of(a6); s[bp + 6] = Value.Of(a7); s[bp + 7] = Value.Of(a8); s[bp + 8] = Value.Of(a9); s[bp + 9] = Value.Of(a10); s[bp + 10] = Value.Of(a11); s[bp + 11] = Value.Of(a12); s[bp + 12] = Value.Of(a13); s[bp + 13] = Value.Of(a14);
        return m.Leave(g, s, bp, mark);
    }

    static Obj Stub16(Obj h, Obj a1, Obj a2, Obj a3, Obj a4, Obj a5, Obj a6, Obj a7, Obj a8, Obj a9, Obj a10, Obj a11, Obj a12, Obj a13, Obj a14, Obj a15)
    {
        Fn g = Fn.OfHandle(h);
        var m = Machine.Current;
        if (!Machine.Simple(g)) return m.CallBoxed(g, [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15]);
        var s = m.Enter(g, out int bp, out var mark);
        s[bp + 0] = Value.Of(a1); s[bp + 1] = Value.Of(a2); s[bp + 2] = Value.Of(a3); s[bp + 3] = Value.Of(a4); s[bp + 4] = Value.Of(a5); s[bp + 5] = Value.Of(a6); s[bp + 6] = Value.Of(a7); s[bp + 7] = Value.Of(a8); s[bp + 8] = Value.Of(a9); s[bp + 9] = Value.Of(a10); s[bp + 10] = Value.Of(a11); s[bp + 11] = Value.Of(a12); s[bp + 12] = Value.Of(a13); s[bp + 13] = Value.Of(a14); s[bp + 14] = Value.Of(a15);
        return m.Leave(g, s, bp, mark);
    }

    static Obj StubN(Obj[] a)
    {
        Fn g = Fn.OfHandle(a[0]);
        return Machine.Current.CallBoxed(g, a.AsSpan(1));
    }
}
