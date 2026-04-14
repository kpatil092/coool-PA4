class A { void foo() { System.out.println("A"); } }
class B extends A { void foo() { System.out.println("B"); } }

class Wrapper {
    A f;
}

class Manager {
    void process(Wrapper w) {
        w.f.foo();   // 🔴 target
    }
}

class Test {
    public static void main(String[] args) {
        Wrapper w1 = new Wrapper();
        w1.f = new A();

        Wrapper w2 = new Wrapper();
        w2.f = new B();

        // Manager m = new Manager();
        Manager m1 = new Manager();
        Manager m2 = new Manager();

        m1.process(w1);
        m2.process(w2);
    }
}