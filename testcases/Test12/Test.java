class A {
    void foo() { System.out.println("A"); }
}

class B extends A {
    void foo() { System.out.println("B"); }
}

class Test {

    static void call(A x) {
        x.foo();  
    }

    public static void main(String[] args) {
        call(new A());
        call(new B());
    }
}

//  Parameter-based polymorphism