interface I {
    void foo();
}

class A implements I {
    public void foo() { System.out.println("A"); }
}

class B implements I {
    public void foo() { System.out.println("B"); }
}

public class Test {
    public static void main(String[] args) {
        I x;

        if (args.length > 0)
            x = new A();
        else
            x = new B();

        x.foo();   // ❌ SPARK fails
    }
}

// Interface dispatch