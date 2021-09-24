use prusti_contracts::*;

liquid! {
    fn sum(k: Box<i32, {true}>) -> i32<{_ < 0 && _ >= k}> {
        if *k < 0 { 0 }
        else {
            let s: i32 = sum (Box::new(*k-1));
            s+*k
        }
    }
}

fn main() {}