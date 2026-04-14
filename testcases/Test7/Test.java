class A {
    int x;
}

class C {
    void foo(A a) {
        a.x = 99;
    }
}

class D extends C {
    void foo(A a) {
        System.out.println(a.x);
    }
}

public class Test {
    public static void main(String[] args) {
        A a = new A(); // O19
        C c = new D(); // O20
        // C c = new C(); // O20
        c.foo(a);
    }
}


// NOTE: Call site at 22 will resolve to D.foo only

// O19 = Y[22]
// O20 = Y[22]