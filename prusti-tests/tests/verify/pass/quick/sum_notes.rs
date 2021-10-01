use prusti_contracts::*;
prusti! {

type Range<const L, const U> = t!{i32 | _ >= L && _ < U}

fn odd( mut k: Range<0, 10> ) -> i32 {
    for i in [0..10] {

    }
    k = k+2;
    if k % 2 == 1 { k = k+1; k }
    else { -1 }
}

// TODO
type Index<collection> = {i32 | _ < collection.len()}

fn getVal(cl: &[i32], idx: Index<cl>) {
    
}

let mut b = 0;
let mut a: {i32 | pure(a) || a.f > 0 || a.f == b}
a.g = 2;
// Must check inv
foo(mut a);
// Must check inv
b = 1
// Must check inv

// Wherever ANY var mentioned in `inv` may mutably be modified

loop (*) {
    // If `a` is live add inv as loop_inv
    ...
}


}