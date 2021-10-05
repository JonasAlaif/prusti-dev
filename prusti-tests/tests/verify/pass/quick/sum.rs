use prusti_contracts::*;

fn main() {}

prusti! {

type Index<const s: &[T]> where T: = i!{usize | _ >= 0 && _ < s.len()};

fn get_val(s: &[i32], idx: Index<{s}>) -> i32 {
    s[idx]
}

}

prusti! {

type LessEq<const x: i32, const y: i32> = i!{i32 | _ <= x && _ <= y};

fn min(mut a: i!{i32 | _ >= 0}, b: i32) -> i!{LessEq<{a}, {b}> | _ == a || _ == b} {
    if a < b { a }
    else { b }
}


}


// type a = i32;
// fn test(a: i32, b: Box<a>) -> i32 { a + *b }