class A { void foo() { System.out.println("A"); } }
class B extends A { void foo() { System.out.println("B"); } }

class C {
    A f;
}

class Test {
    static void call(C w) {
        w.f.foo();
    }

    public static void main(String[] args) {
        C w1 = new C();
        w1.f = new A();

        C w2 = new C();
        w2.f = new B();

        call(w1);
        call(w2);
    }
}

//  Here too the static methods parameter will be grouped 
