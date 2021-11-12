use prusti_contracts::*;
fn main() {}

// ---- Prusti signature ----
type Link = Option<Box<Node>>;
struct Node(i32, Link);

fn sll_copy(l: &Link) -> Link { ?? }


// ---- SuSLik output ----
{r :-> x           ** sll(x)}
{r :-> y ** sll(y) ** sll(x)}
void sll_copy (loc r) {
  *r = 0;
}

// ---- Rust code ----
fn sll_copy(l: &Link) -> Link {
    None
}


// ---- How to add fn. spec? ----

