use prusti_contracts::*;
prusti! {

type Index<T, const s: &[i32], const r: i32> = t!{i32 | _ < s.len()};

}

prusti! {

fn main() {}


fn getVal(cl: &[i32], idx: Index<i32, {cl}, 0>) -> bool {

}


}