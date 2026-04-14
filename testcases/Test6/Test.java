class A { void foo() {} }
class B extends A { void foo() {} }

class Test {
    static A id(A x) { return x; }

    public static void main(String[] args) {
        A a = id(new A());
        A b = id(new B());

        a.foo();
        b.foo();
    }
}

// Need lookup

// foos will not be resolve because the a and b points to more than one objects due to flow insensitivity, constext aware cloning of static might resolve this.