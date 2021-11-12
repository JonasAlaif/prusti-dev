use prusti_contracts::*;

fn main() {}

type Link = Option<Box<Node>>;
struct Node(i32, Link);

fn copy(x: &mut Link, ret: &mut Link) {
    // if (x != 0) {
    if let Some(x) = x.take() {
        // let v = *x;
        let mut v = x.0;
        // let n = *(x + 1);
        let mut n = x.1;
        // copy(n, ret);
        copy(&mut n, ret);
        // let y1 = *ret;
        let y1 = ret.take();
        // let y = malloc(2);
        let y = Box::new(Node(v, y1));
        // *ret = y;
        *ret = Some(y);
        // Done above (cannot have uninitialized memory)
        // *(y + 1) = y1;
        // *y = v;
    } else {
        // *ret = 0;
        *ret = None;
    }
}
