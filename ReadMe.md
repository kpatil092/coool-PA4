 
**Programming Assignment 2: Objects and Their Shadows**

---

## 1. Assignment Objective

Use Soot to identify objects that are **scalar replaceable** in a Java program by performing a **flow-sensitive analysis** over simple programs. An object is considered scalar replaceable (in context of Java) if:

- It is safely allocatable on the stack of the declaring method, and  
- It is never used in a manner requiring object identity, and  
- Even if it escapes to other methods, its fields are only read and never modified  

---

## 2. Detailed Specification

Your task is to design an analysis that determines which allocation sites correspond to scalar-replaceable objects.

### Analysis Requirements

- Generate **flow-sensitive intraprocedural points-to information** or **interprocedural analysis**
- Perform **escape analysis** using this information
- Determine whether allocated objects remain eligible for scalar replacement
- Objects escaping to other methods may still be scalar replaceable **if they are only read and never modified**
- Objects escaping to global variables must be marked **non scalar replaceable**
- Analysis must use **Soot’s inbuilt Class Hierarchy Analysis (CHA)** for resolving call sites
- The analysis must take the input program **at face value**, including dead or unreachable code

### Testcase Guarantees

You may assume:

- No direct or indirect recursion  
- No `instanceof`, reference equality, or operations requiring object headers  

---

## 3. Public Testcase

```java
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
            M o1 = new M(); // O31
            o1.x = 8;
            System.out.println(o1.x);
        }

        { // Case 2
            M o2 = new M(); // O37
            N o3 = new N(); // O38
            o2.x = 27;
            o2.y = 125;
            o3.foo(o2);
        }

        { // Case 3
            M o4 = new M(); // O45
            O o5 = new O(); // O46
            o4.x = 343;
            o5.foo(o4);
        }

        return;
    }
}
```
---

### Expected Output
```
O31 = Y[]
O37 = Y[8,41]
O38 = Y[8,41]
O45 = N
O46 = Y[48]
```

---

### Explaination

- O31 is a local object that does not escape main.
- O37 is a local object that does not escape main. Although it is passed to foo (Line 41) and bar (Line 8), its fields are only read and never modified.
    * Can be scalar replaced if calls at Lines 8 and 41 are rewritten.
- O38 is also a non-escaping local object within main. Even when passed as this to foo and bar, none of its fields are written.
    * Eligible for scalar replacement.
- O45 is a local object that does not escape main. However, when passed to foo (Line 48), CHA resolves two targets: O::foo and P::foo.
    * In P::foo, field x may be modified
    * Therefore, scalar replacement is disallowed
- O46 is a non-escaping object passed as this at Line 48. Both possible targets (O::foo, P::foo) do not modify its fields
    * Scalar replacement is safe


---

