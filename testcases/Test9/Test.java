class A {
    void foo() { System.out.println("A"); }
}

class B extends A {
    void foo() { System.out.println("B"); }
}

class C {
    static A get() {
        if (System.currentTimeMillis() > 0)
            return new A();
        else
            return new B();
    }
}

public class Test {
    public static void main(String[] args) {
        A x = C.get();
        x.foo();   // ❌ SPARK fails
    }
}

// Method return-based imprecision