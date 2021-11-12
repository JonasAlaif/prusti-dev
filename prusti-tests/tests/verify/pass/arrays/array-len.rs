use prusti_contracts::*;

fn main() {}


type Link<'a> = &'a mut Option<Node<'a>>;

struct Node<'a>(i32, Link<'a>, Link<'a>);

fn flatten (x: Link) {
    if let Some(x1) = x {
        let l = x1.1;
        let r = x1.2;
        {
            flatten(l);
            flatten(r);
        }
        flatten118(r, l, &mut x1);
    } else {
    }
}

fn flatten118<'a> (r: Link<'a>, l: Link<'a>, x: &mut Node<'a>) {
    if let Some(l1) = l {
        // let v = &mut l1.0;
        let y = &mut l1.1;
        *l1.2 = *r;
        flatten118(r, y, l1);
        *l1.2 = Some(*x);
    } else {
        if let Some(r1) = r {
            *r1.2 = Some(*x);
            *x.1 = *r;
        } else {
        }
    }
}

/*
fn flatten (loc x) {
    if (x == 0) {
    } else {
        let l = *(x + 1);
        let r = *(x + 2);
        flatten(l);
        flatten(r);
        flatten118(r, l, x);
    }
}

fn flatten118 (loc r, loc l, loc x) {
    if (l == 0) {
        if (r == 0) {
        } else {
        *(r + 2) = x;
        *(x + 1) = r;
        }
    } else {
        let v = *l;
        let y = *(l + 1);
        *(l + 2) = r;
        flatten118(r, y, l);
        *(l + 2) = x;
    }
}
*/