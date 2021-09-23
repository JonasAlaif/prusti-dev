use prusti_contracts::*;

fn main() {}

fn slice(a: &[i32; 6]) {
    let s = &a[1..4];
    assert!(s[0] == a[1]);
    let s = &a[..2];
    assert!(s[1] == a[1]);
    let s = &a[1..];
    assert!(s[2] == a[3]);
    let s = &a[..];
    assert!(s[3] == a[3]);
    // Unsupported
    //let s = &a[1..=4];
    //assert!(s[3] == a[4]);
    let s = &a[..=5];
    assert!(s[5] == a[5]);
}
