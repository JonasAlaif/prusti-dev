use prusti_contracts::*;
fn main() {}

// ---- Prusti signature ----
type Link = Option<Box<Node>>;
struct Node(i32, Link);
fn sll_copy(l: &Link) -> Link { ?? }


// ---- SuSLik output ----
{result :-> x           ** sll(x)}
{result :-> y ** sll(y) ** sll(x)}
void sll_copy (loc result) {
  *result = 0;
}

// ---- Rust code ----
fn sll_copy(l: &Link) -> Link {
    None
}

// ------------------------------
// ---- How to add fn. spec? ----
#[pure]
fn sll_eq(l: &Link, r: &Link) -> bool {
    match (l, r) {
      (Some(l), Some(r)) => l.0 == r.0 && sll_eq(&l.1, &r.1),
      (None, None) => true,
      _ => false
    }
}
#[ensures(sll_eq(l, &result))]
fn sll_copy(l: &Link) -> Link { ?? }

// ---- A: Viper predicates ----
// Encoding of Option (can be replaced by `| self == 0 =>` in SuSLik)
predicate Option(self: Ref) {
    acc(self.discriminant, write) && (0 <= self.discriminant && self.discriminant <= 1 && (acc(self.enum_Some, write) && (self.discriminant == 1 ==> acc(Some(self.enum_Some), write))))
}
predicate Some(self: Ref) {
    acc(self.f_0, write) && acc(Box(self.f_0), write)
}
// Encoding of Box (pointer to heap allocation, again simply tells us that `self` is a `loc` in SuSLik)
predicate Box(self: Ref) {
    acc(self.val_ref, write) && acc(Node(self.val_ref), write)
}
// The main predicate (to translate to SuSLik we need to layout the fields in memory)
predicate Node(self: Ref) {
    acc(self.f_0, write) && (acc(i32(self.f_0), write) && (acc(self.f_1, write) && acc(Option(self.f_1), write)))
}
// Ignore this for now; do not enforce the type of `f_0`
predicate i32(self: Ref) {
  acc(self.val_int, write)
}
// ---- A: SuSLik predicates ----
predicate Link(loc box) {
| box != 0 => { box :-> node ** Node(node) }
| box == 0 => { emp }
}
predicate Node(loc self) {
| true => { [self, 2] ** self :-> f0 ** self+1 :-> f1 ** Link(f1) }
}

// ---- B: Viper pure fn ----
// Prusti uses Viper `domain`s to encode pure function arguments, but
// I have "inlined" that representation (would require some 'slight?' modifications in Prusti):
function sll_eq(l: Ref, r: Ref): Bool
  requires acc(Option(l), read())
  requires acc(Option(r), read())
{
  (unfolding acc(Option(l), read()) in (unfolding acc(Option(r), read()) in (l.dc == 1 ?
    (r.dc == 1 ?
      (unfolding acc(Some(l.enum_Some), read()) in
        (unfolding acc(Box(l.enum_Some.f_0), read()) in
          (unfolding acc(Node(l.enum_Some.f_0.val_ref), read()) in
            (unfolding acc(i32(l.enum_Some.f_0.val_ref.f_0), read()) in
              (unfolding acc(Some(r.enum_Some), read()) in
                (unfolding acc(Box(r.enum_Some.f_0), read()) in
                  (unfolding acc(Node(r.enum_Some.f_0.val_ref), read()) in
                    (unfolding acc(i32(r.enum_Some.f_0.val_ref.f_0), read()) in
                      (l.enum_Some.f_0.val_ref.f_0.val_int == r.enum_Some.f_0.val_ref.f_0.val_int) &&
                      ((l.enum_Some.f_0.val_ref.f_0.val_int == r.enum_Some.f_0.val_ref.f_0.val_int) ==> 
                        sll_eq(l.enum_Some.f_0.val_ref.f_1, r.enum_Some.f_0.val_ref.f_1))
        ))))))))
    : false)
  : r.dc != 1)))
}
// With `read()` defined as:
function read(): Perm
  ensures none < result
  ensures result < write
// ---- B: SuSLik pure fn ----
// To translate the above directly we would need a construct of the form `pure_fn(); predicate()`:
//  { result :-> a ** Node(l) }
//  void sll_copy(loc l, loc result)
//  { sll_eq(l, y); result :-> y ** Node(l) ** Node(y) }
// Instead, we must combine `sll_eq` and `Node` into one predicate:
predicate P_sll_eq(loc l, loc r) {
| not (l == 0) => {
    not (r == 0) && l_f_0 == r_f_0;
    [l, 2] ** l :-> l_f_0 ** (l + 1) :-> l_f_1 **
    [r, 2] ** r :-> r_f_0 ** (r + 1) :-> r_f_1 **
    sll_eq(l_f_1, r_f_1)
}
| l == 0 => { r == 0; emp }
}

// ---- SuSLik input ----
{ result :-> a ** Node(l) }
void sll_copy(loc l, loc result)
{ result :-> r ** P_sll_eq(l, r) }
// Note: we do not use `l :-> x ** Node(x)` even though in Rust we have `l: &Link`
//       as SuSLik cannot "borrow" (`&`) to construct the correct form of the argument
//       for the recursive call - instead, it would write to l:
//          let x = *l;
//          ...
//          *l = *(x + 1);
//          sll_copy(l, result);
//          *l = x;
//       If we could somehow make `l` read-only then I assume SuSLik would generate:
//          let l1 = malloc(1);
//          *l1 = *(x + 1);
//          sll_copy(l1, result);
//          free(l1);
//       As the alternative to:
//          let f_1 = *(x + 1);
//          sll_copy(&f_1, result);

// ---- SuSLik output ----
void sll_copy (loc l, loc result) {
    if (l == 0) {
        *result = 0;
    } else {
        let f_0 = *l;
        let f_1 = *(l + 1);
        sll_copy(f_1, result);
        let r1 = *result;
        let r = malloc(2);
        *result = r;
        *(r + 1) = r1;
        *r = f_0;
    }
}

// ---- Rust code ----
fn sll_copy(l: &Link) -> Link {
    // Note: switch the branches here
    // if (l == 0) {
    if let Some(l) = l {
        // let f_0 = *l;
        let f_0 = l.0;
        // Note: due to the aforementioned limitation,
        //       it is unclear how we know to insert the `&` borrow here:
        // let f_1 = *(l + 1);
        let f_1 = &l.1;
        // sll_copy(f_1, result);
        // let r1 = *result;
        let r1 = sll_copy(f_1);
        // Note: The `malloc` is translated as `Some(Box::new(...))`, however
        //       we must initialize the memory straight away in Rust
        // let r = malloc(2);
        // *result = r;
        // *(r + 1) = r1;
        // *r = f_0;
        Some(Box::new(Node(f_0, r1)))
    } else {
        // *result = 0;
        None
    }
}
fn sll_copy(l: &Link) -> Link {
  let lbox = *l; // Error
  if let Some(lbox) == lbox {
    let lnode = *lbox; // Error
    let f0 = lnode.0;
    let f1 = lnode.1;
    *l = f1; // Error
    let res = sll_copy(l);
    let rbox = malloc(1); // ?
    let rnode = malloc(2); // ?
    *l = lbox; // Error
    *rbox = rnode;
    *(rnode + 1) = res;
    *rnode = f0;
    rbox
  } else {
    None
  }
}
