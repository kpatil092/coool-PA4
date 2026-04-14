class A {
    void foo() { System.out.println("A"); }
}

class B extends A {
    void foo() { System.out.println("B"); }
}

public class Test {
    public static void main(String[] args) {
        A x = new A();

        for (int i = 0; i < 10; i++) {
            if (i % 2 == 0)
                x = new B();
        }

        x.foo();
    }
}

// Loop-induced merging