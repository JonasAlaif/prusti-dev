use prusti_contracts::*;

fn main() {}

type Link = Option<Box<Node>>;
struct Node(i32, Link);

#[pure]
fn sll_eq(l: &Link, r: &Link) -> bool {
    if let Some(l) = l {
        if let Some(r) = r {
            l.0 == r.0 && sll_eq(&l.1, &r.1)
        } else {
            false
        }
    } else {
        if let Some(_) = r {
            false
        } else {
            true
        }
    }
}

#[ensures(sll_eq(l, &result))]
fn sll_copy(l: &Link) -> Link {
    // Note: switch the branches here
    // if (l == 0) {
    if let Some(l) = l {
        // let f_0 = *l;
        let f_0 = (**l).0;
        // let f_1 = *(l + 1);
        let f_1 = &(*l).1;
        // Note: due to the aforementioned limitation,
        //       it is unclear how we know to insert the `&` borrow here:
        // sll_copy(f_1, result);
        let r1 = sll_copy(f_1);
        let mut b = Box::new(Node(0, None));
        let n = Node(f_0, r1);
        *b = n;
        // Note: The `malloc` is translated as `Some(Box::new(...))`, however
        //       we must initialize the memory straight away in Rust
        // let r = malloc(2);
        // *result = r;
        // *(r + 1) = r1;
        // *r = f_0;
        Some(b)
    } else {
        // *result = 0;
        None
    }
}