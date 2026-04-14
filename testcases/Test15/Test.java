class A { void foo() {} }
class B extends A { void foo() {} }

class X {
    void call(A a) { a.foo(); }
}

class Y {
    void invoke(X x, A a) { x.call(a); }
}

class Test {
    public static void main(String[] args) {
        Y y = new Y();
        X x = new X();

        y.invoke(x, new A());
        y.invoke(x, new B());
    }
}

// not working