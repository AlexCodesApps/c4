# I Need to Reason About What Im Doing Here

this is a theoretical program in a future version

```c4
const fn times2(x: usize): usize {
    return x * x;
}
struct A {
    a: *[times2(sizeof(a))]typeof(b::a);
}

mod b {
    const a: A = A { a: null };
}

const fn calculate(a: &A): usize {
    return (a.*a as usize) - 10;
}

fn main() {
    let a: A = { a: null };
    let b: A = { a: &a };
    let c = calculate(&b);
}
```

In this program, what is important rn is how cyclical types are evaluated at
compile time.
It appears that uhh, type evaluation is in someways shallow, to prevent
infinite recursion, and to allow for introspecting on the type of a constant of
the same type (value is irrelevant in the usage).
So a shallow type impl (enough to define sizeof()), and a somehow recursive one
(probably using some sort of queue to prevent infinite cycles).

ULTIMATUM. implement the VM so that it works properly, then implement cycle
checks, because reasoning about that without proper examples is difficult?
idk might have to check back on this one.

CONSIDER: typeof(expr) does not have the same semantics as expr
typeof(expr) maybe be more charitable in what it accepts.
sizeof(expr) functionality is in the same boat as it is functionally a
sizeof(typeof(expr)) which should be valid in all the same places.
