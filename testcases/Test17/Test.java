class Base {
    void foo() { }
}

class A extends Base {
    Wrapper w;

    void set(Wrapper w) {
        this.w = w;
    }

    void callF() {
        w.f.foo();   // 🔴 target
    }
}

class B extends Base {
    void foo() { }
}

class Wrapper {
    Base f;
}

class Runner {
    void run(A a, Wrapper w) {
        a.set(w);
        a.callF();
    }
}

public class Test {
    public static void main(String[] args) {
        A a = new A();               // o_a (single object!)

        Wrapper w1 = new Wrapper(); // o_w1
        w1.f = new A();             // o_f1

        Wrapper w2 = new Wrapper(); // o_w2
        w2.f = new B();             // o_f2

        Runner r1 = new Runner();   // o_r1
        Runner r2 = new Runner();   // o_r2

        r1.run(a, w1);
        r2.run(a, w2);
    }
}