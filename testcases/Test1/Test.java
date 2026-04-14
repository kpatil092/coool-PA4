class M {
    int x, y;
}

class N {
    void foo(M mm) {
        System.out.println(mm.x);
        bar(mm);
    }

    void bar(M mm) {
        System.out.println(mm.y);
    }
}

class O {
    void foo(M mm) {
        System.out.println(mm.x);
    }
}

class P extends O {
    void foo(M mm) {
        mm.x = 112;
    }
}

public class Test {
    public static void main(String[] args) {
        { // Case 1
            M o1 = new M(); // 031
            o1.x = 8;
            System.out.println(o1.x);
        }

        { // Case 2
            M o2 = new M(); // 037
            N o3 = new N(); // 038
            o2.x = 27;
            o2.y = 125;
            o3.foo(o2);
        }

        { // Case 3
            M o4 = new M(); // 045
            O o5 = new O(); // 046
            o4.x = 343;
            o5.foo(o4);
        }

        return;
    }
}