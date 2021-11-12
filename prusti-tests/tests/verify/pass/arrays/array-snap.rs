use prusti_contracts::*;
fn main() {}


type Tree = Option<Box<Node>>;
struct Node(i32, Tree, Tree);


