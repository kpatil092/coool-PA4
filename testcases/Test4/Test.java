class Node {
    int x;
    void foo() {
        Node a = new Node();  //O4
        a = bar(a);
    }
    Node bar(Node a) {
        Node b = new Node();
        foo();
        return b;
    }
}

public class Test {
    public static void main(String[] args) {
        Node a = new Node(); //O17
        a.foo();
    }
}

//  Recusion 2