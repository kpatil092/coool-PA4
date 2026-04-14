class Base {
    void foo() { }
}

class A extends Base {
    Base f;
}

class B extends Base {
    void foo() { }
}

class C {
    A a;
}

class D {
    C c;

    void process() {
        c.a.f.foo();   // 🔴 target
    }
}

class E {
    D d;

    void call() {
        d.process();
    }
}

public class Test {
    public static void main(String[] args) {

        // --- Level 1 ---
        E e1 = new E(); // o_e1
        E e2 = new E(); // o_e2

        // --- Level 2 ---
        D d1 = new D(); // o_d1
        D d2 = new D(); // o_d2

        // --- Level 3 ---
        C c1 = new C(); // o_c1
        C c2 = new C(); // o_c2

        // --- Separate A objects (IMPORTANT CHANGE) ---
        A a1 = new A(); // o_a1
        A a2 = new A(); // o_a2

        // --- Leaf objects ---
        A f1 = new A(); // o_f1
        B f2 = new B(); // o_f2

        // Wiring

        c1.a = a1;
        c2.a = a2;

        d1.c = c1;
        d2.c = c2;

        e1.d = d1;
        e2.d = d2;

        // Assign different f per A
        a1.f = f1;   // always A
        a2.f = f2;   // always B

        // Calls
        e1.call();   // path 1 → A.foo
        e2.call();   // path 2 → B.foo

        // Cross calls (create ambiguity for low k)
        e1.d = d2;
        e1.call();   // path 3

        e2.d = d1;
        e2.call();   // path 4
    }
}