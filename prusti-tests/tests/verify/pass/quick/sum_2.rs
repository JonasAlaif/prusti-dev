use prusti_contracts::*;

macro_rules! LT {
    ($t:ty, $l:expr) => {$t}
}

#[ensures(result >= 0 && result >= k)]
fn sum(k: i32) -> LT!{i32, val >= 0 && val >= k} {
    if k < 0 { 0 }
    else {
        let s = sum (k-1);
        s+k
    }
}

fn main() {}