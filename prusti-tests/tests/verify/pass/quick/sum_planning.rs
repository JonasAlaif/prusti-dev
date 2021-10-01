use prusti_contracts::*;

/*
fn foo(k: &[i32] + NonEmpty) ...

fn foo(#[Lt{...}] k: &[i32]) ...

fn foo(k: i32]) ...
*/


dep! {


fn sum(k: mut i32<{ Odd }>, l: Odd ) -> i32 {
    let j = k + l; // -> j: i32
    let j: i32<{ Even }> = k + l;
    assert! (j: Even);

    let j = k; // -> j: i32
    let j: i32<{ Odd }> = k;

    k = 2;
    assert! (k: Odd);


    if k < 0 { 0 }
    else {
        let s = sum (k-1);
        s+k
    }
}


}



/*
fn sum(mut k: i32 + Odd, l: Odd ) -> i32 { 
    let mut k: i32 = 42;
    k = 42;
    assert!( Odd(k) );
}

->

#[invariant( Odd(k) )]
fn sum(mut k: i32, l: Odd ) -> i32 { }


fn at(i: { i32 | _ > self.len() } ) -> i32 { }



fn main(x: i32, y: i32) { 
    ...
    let j = x + y;
    array.at(j)
    ...
}*/

// dep! {
//     #[ensures(result > 2)]
//     fn sum_error(k: Box<i32><{let i = 1; *__ > i}>) -> i32<{__ > *k}> {
//         if *k < 0 { 0 }
//         else {
//             let s = sum_error (Box::new(*k-1));
//             s+*k
//         }
//     }
// }

// dep! {

// #[ensures(result >= 0)]
// fn sum_box(k: Box<i32, {*__ >= -1}>) -> i32<{__ >= *k}> {
//     if *k < 0 { 0 }
//     else {
//         let s = sum_box (Box::new(*k-1));
//         s+*k
//     }
// }

// fn main() {}

//}

dep2!{


#[requires(k >= 2)]
#[ensures(result >= 3 && result > k)]
fn sum_2(k: i32) -> i32 {
    if k == 2 { 3 }
    else { k + sum_2(k-1) }
}


dep!{ &[i32] | __.len() >= 2 }

-->

Reft<&[i32], |__: &[i32]| -> bool {__.len() >= 2} >


type Reft<T, const U: Fn (T) -> bool> = T;



fn sum(k: dep!{ &[i32] | __.len() >= 2 } ) -> i32<{__ >= 3 && __ > k}> {
    if k == 2 { 3 }
    else { k + sum(k-1) }
}

fn sum(k: Box<i32><{*__ >= 2 }> ) -> i32<{__ >= 3 && __ > k}> {
    if k == 2 { 3 }
    else { k + sum(k-1) }
}

fn main() {
    assert!(sum(3) >= 4);
}


}



#[depfn]
fn closure() {
    let odd_to_even =
        |i: i32<{__ % 2 == 1}>|
            -> i32<{__ == i * 2}>
                { i * 2 };
    assert!(odd_to_even(1) % 2 == 0);
}

fn closure_2() {
    let odd_to_even = closure!(
        requires(i % 2 == 1),
            ensures(result == i * 2),
                |i:i32| -> i32 { i * 2 }
    );
    assert!(odd_to_even(1) % 2 == 0);
}