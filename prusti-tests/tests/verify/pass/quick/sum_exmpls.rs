use prusti_contracts::*;
prusti! {

fn main() {}

fn sum( k: i32 ) -> t!{i32 | _ >= 0 && _ >= k} {
    if k < 0 { 0 }
    else { k + sum(k-1) }
}



fn sum_n( k: (i32, Box<Box<i32>>) ) -> i32 {k.0}

fn sum_2( k: (t!{i32 | _ == 0}, Box<Box<t!{i32 | _ >= 3}>>) ) -> t!{i32 | _ >= 3 && _ > **k.1} {
    if **k.1 == 2 { 3 }
    else { **k.1 + sum_2( (0, Box::new(Box::new(**k.1 - 1))) ) }
}


fn closure() {
    let odd_to_even =
        |i: t!{i32 | _ % 2 == 1} |
            -> t!{i32 | _ == i * 2}
                { i * 2 };
    assert!(odd_to_even(1) % 2 == 0);
}

}