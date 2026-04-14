class Node {
    int x;
    static Node p;
    void foo() {
        Node a = new Node();  //O4
        a = bar(a);
        p = a;
    }
    Node bar(Node a) {
        this.x = 12;
        return a;
    }
}

public class Test {
    public static void main(String[] args) {
        Node a = new Node(); //O15
        a.foo();
    }
}


// field write of this
// Need to handle this static case because we are not doing flowwise movement

// O5 = N
// O17 = N