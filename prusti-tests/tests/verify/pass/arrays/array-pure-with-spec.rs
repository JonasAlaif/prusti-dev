#![feature(box_patterns)]
use prusti_contracts::*;

fn main() {}

/*
struct List {
    current: i32,
    rest: Option<Box<List>>
}
#[pure]
#[ensures(result > 0)]
fn length(r: &List) -> i32 {
    1 + match r.rest {
        Some(box ref q) => length(q),
        None => 0
    } 
}

#[requires(0 <= n && n < length(r))]
// #[ensures(result.x == old(nth_x(r, n)))]
fn nth_point(r: &mut List, n: i32) -> &mut i32 {
    if n == 0 { &mut r.current }
    else {
        match r.rest {
            Some(box ref mut q) => nth_point(q, n-1),
            None => unreachable!()
        }
    }
}
*/

fn borrow_first(t: &mut (i32, i32)) -> &mut i32 {
    &mut t.0
}
