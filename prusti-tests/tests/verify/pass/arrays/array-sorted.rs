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
fn sll_copy(l: &Link) -> Link { ?? }

// ---- A: Viper predicates ----
// Encoding of Option (can be replaced by `| self == 0 =>` in SuSLik)
predicate P_Link(self: Ref) {
    acc(self.discriminant, write) && (0 <= self.discriminant && self.discriminant <= 1 && (acc(self.enum_Some, write) && (self.discriminant == 1 ==> acc(P_Some(self.enum_Some), write))))
}
predicate P_Some(self: Ref) {
    acc(self.f_0, write) && acc(P_BoxNode(self.f_0), write)
}
// Encoding of Box (pointer to heap allocation, again simply tells us that `self` is a `loc` in SuSLik)
predicate P_BoxNode(self: Ref) {
    acc(self.val_ref, write) && acc(P_Node(self.val_ref), write)
}
// The main predicate (to translate to SuSLik we need to layout the fields in memory)
predicate P_Node(self: Ref) {
    acc(self.f_0, write) && (acc(i32(self.f_0), write) && (acc(self.f_1, write) && acc(P_Link(self.f_1), write)))
}
// Ignore this for now; do not enforce the type of `f_0`
predicate i32(self: Ref) {
  acc(self.val_int, write)
}
// ---- A: SuSLik predicates ----
predicate P_Node(loc self) {
| self == 0 => { emp }
| not (self == 0) => { [self, 2] ** self :-> f_0 ** (self + 1) :-> f_1 ** P_Node(f_1) }
}

// ---- B: Viper pure fn ----
// Prusti uses Viper `domain`s to encode pure function argurments, but
// I have "inlined" that representation (would require some 'slight?' modifications in Prusti):
function sll_eq(l: Ref, r: Ref): Bool
  requires acc(P_Link(l), read())
  requires acc(P_Link(r), read())
{
  (unfolding acc(P_Link(l), read()) in (unfolding acc(P_Link(r), read()) in (l.discriminant == 1 ?
    (r.discriminant == 1 ?
      (unfolding acc(P_Some(l.enum_Some), read()) in
        (unfolding acc(P_BoxNode(l.enum_Some.f_0), read()) in
          (unfolding acc(P_Node(l.enum_Some.f_0.val_ref), read()) in
            (unfolding acc(i32(l.enum_Some.f_0.val_ref.f_0), read()) in
              (unfolding acc(P_Some(r.enum_Some), read()) in
                (unfolding acc(P_BoxNode(r.enum_Some.f_0), read()) in
                  (unfolding acc(P_Node(r.enum_Some.f_0.val_ref), read()) in
                    (unfolding acc(i32(r.enum_Some.f_0.val_ref.f_0), read()) in
                      (l.enum_Some.f_0.val_ref.f_0.val_int == r.enum_Some.f_0.val_ref.f_0.val_int) &&
                      ((l.enum_Some.f_0.val_ref.f_0.val_int == r.enum_Some.f_0.val_ref.f_0.val_int) ==> 
                        sll_eq(l.enum_Some.f_0.val_ref.f_1, r.enum_Some.f_0.val_ref.f_1))
        ))))))))
    : false)
  : r.discriminant != 1)))
}
// With `read()` defined as:
function read(): Perm
  ensures none < result
  ensures result < write
// ---- B: SuSLik pure fn ----
// To translate the above directly we would need a construct of the form `pure_fn(); predicate()`:
//  { result :-> a ** P_Node(l) }
//  void sll_copy(loc l, loc result)
//  { sll_eq(l, y); result :-> y ** P_Node(l) ** P_Node(y) }
// Instead, we must combine `sll_eq` and `P_Node` into one predicate:
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
{ result :-> a ** P_Node(l) }
void sll_copy(loc l, loc result)
{ result :-> r ** P_sll_eq(l, r) }
// Note: we do not use `l :-> x ** P_Node(x)` even though in Rust we have `l: &Link`
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
