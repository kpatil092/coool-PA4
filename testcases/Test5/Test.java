class A {
    int x, y;
    void foo(A a) {
        System.out.println(a.x);
        return;
    }
}

class B {
    A a;

    void foo(A a) {
        System.out.println(a.x);
        a.foo(a);
        return;
    }
}

public class Test {
    public static void main(String[] args) {
        A a = new A();
        B b = new B();
        b.a = a;
        A q = b.a;
        b.foo(q);
    }
}
