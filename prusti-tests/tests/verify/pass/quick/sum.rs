use prusti_contracts::*;

fn main() {}

prusti! {

type Index<const s: &[T]> where T: = i!{usize | _ >= 0 && _ < s.len()};

fn get_val(s: &[i32], idx: Index<{s}>) -> i32 {
    s[idx]
}

}

prusti! {

type LessEq<const other: i32> = i!{i32 | _ <= other};
type Eq<const other: i32> = i!{i32 | _ == other};

fn min(a: i32, b: LessEq<{a}>) -> Eq<{b}> {
    if a < b { a }
    else { b }
}


}


// type a = i32;
// fn test(a: i32, b: Box<a>) -> i32 { a + *b }