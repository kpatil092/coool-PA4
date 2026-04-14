class A {
    void foo() { System.out.println("A"); }
}

class B extends A {
    void foo() { System.out.println("B"); }
}

class C {
    A val;
}

public class Test {
    public static void main(String[] args) {
        C h = new C();

        if (args.length > 0)
            h.val = new A();
        else
            h.val = new B();

        A x = h.val;
        x.foo();                                                                        
    }
}

// Field-based aliasing