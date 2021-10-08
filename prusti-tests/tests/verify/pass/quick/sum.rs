// #![feature(specialization)]

use prusti_contracts::*;

fn main() { println!("{}", tst([2])) }

// #[verify]
// fn closure() {
//     let odd_to_even =
//         |i: i!{i32 | _ % 2 == 1}|
//             -> i!{i32 | _ == i * 2}
//                 { i * 2 };
//     assert!(odd_to_even(1) % 2 == 0);
// }

// type Nat = i32;

// trait TypeConstr<T> {
//     fn test(a: T) -> bool;
// }
// default impl<T> TypeConstr<T> for T {
//     #[pure]44
//     fn test(a: T) -> bool { true }
// }

// impl<Nat> TypeConstr<Nat> for Nat {
//     #[pure]
//     fn test(a: Nat) -> bool { false }
// }

// #[requires( <i32 as TypeConstr>::test() )]
// fn tst(x: i32) {}

// prusti! {

// type Index<T, const s: &[T]> = i!{usize | _ >= 0 && _ < s.len() };
// type Index<const s: &[T]> where T: = i!{usize | _ >= 0 && _ < s.len() };

// type Index<const s: &[i32]> = i!{usize | _ >= 0 && _ < s.len() };


// fn get_val(s: &[i!{i32 | _ > 0}], idx: Index<{s}>) -> i!{i32 | _ > 0} {
//     s[idx]
// }

// type Nat = i!{i32 | _ > 0};

// fn get_val_issue(s: &[Nat], idx: Index<{s}>) -> Nat {
//     s[idx]
// }

// fn slice(s: i!{ &[i!{i32 | _ > 0}] | _.len() > 0 }) {
//     assert!(s[0] > 0)
// }

// }

// type A<const usize: usize> = [usize; usize];

// type B<const usize: usize> = A<{}>;


// fn tst(x: B<1>) -> usize {
//     x[0]
// }

fn tst<const T: usize>(a: [usize; T]) -> usize { a[0]+T }

// prusti! {

// type LessEq<const x: i32, const y: i32> = i!{i32 | _ <= x && _ <= y};

// fn min(a: i32, b: i32) -> i!{LessEq<{a}, {b}> | _ == a || _ == b} {
//     if a < b { a }
//     else { b }
// }

// }
// #[verify]
// fn closure() {
//     let cl = |s: i!{&[i!{i32 | _ > 0}] | _.len() > 0}| -> () {
//         assert!(s[0] > 0);
//     };
// }



// type a = i32;
// fn test(a: i32, b: Box<a>) -> i32 { a + *b }