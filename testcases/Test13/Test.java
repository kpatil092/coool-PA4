import java.util.*;

class A {
    void foo() { System.out.println("A"); }
}

class B extends A {
    void foo() { System.out.println("B"); }
}

public class Test {
    public static void main(String[] args) {
        List<A> list = new ArrayList<>();

        list.add(new A());
        // list.add(new B());

        A x = list.get(0);
        x.foo();   // ❌ SPARK fails
    }
}

// Collection-based imprecision