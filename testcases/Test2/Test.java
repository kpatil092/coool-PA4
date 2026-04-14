class A {
    int x, y;
}

public class Test {
    static void foo(int x) {
        System.out.println(x);
    }
    public static void main(String[] args) {
        A a = new A(); // O10
        foo(a.x); // line L1
    }
}

// Passing of non-object field to method