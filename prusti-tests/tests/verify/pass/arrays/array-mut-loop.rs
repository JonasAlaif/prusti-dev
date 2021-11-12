use prusti_contracts::*;

fn main() {}

/*
type Loc<'a, T> = Option<&'a T>;
#[pure]
fn loc_eq<T>(x: Loc<T>, y: Loc<T>) -> bool {
    match x {
        Some(xr) => {
            match y {
                Some(yr) => std::ptr::eq(xr, yr),
                None => false
            }
        }
        None => {
            match y {
                Some(_) => false,
                None => true
            }
        }
    }
}

#[ensures( loc_eq(*x, old(*y)) )]
// #[ensures(*y == old(*x))]
fn swap<'a, T>(x: &mut Loc<'a, T>, y: &mut Loc<'a, T>) {
    let a = *x;
    let b = *y;
    *x = b;
    *y = a;
}
*/


/*
// With read ref as loc, but deep comparison
type Loc<'a, T> = &'a T;

#[ensures( *x == old(*y) )]
#[ensures( *y == old(*x) )]
fn swap<'a, T: PartialEq>(x: &mut Loc<'a, T>, y: &mut Loc<'a, T>) {
    let a = *x;
    let b = *y;
    *x = b;
    *y = a;
}
*/


/*
// With read ref as loc, but deep comparison
type Loc<'a, T> = &'a T;

#[ensures( std::ptr::eq(*x, old(*y)) )]
#[ensures( std::ptr::eq(*y, old(*x)) )]
fn swap<'a, T: PartialEq>(x: &mut Loc<'a, T>, y: &mut Loc<'a, T>) {
    let a = *x;
    let b = *y;
    *x = b;
    *y = a;
}
*/

//  Ideally `Loc` is:
// type Loc<'a, T> = &'a T;
//  Would require ptr comparison `*x as *const _ == old(*y as *const _)` to be supported in Prusti
//  (Which is easily expressible in Viper)

type Loc = i32;

#[ensures( *x == old(*y) )]
#[ensures( *y == old(*x) )]
fn swap(x: &mut Loc, y: &mut Loc) {
    let a = *x;
    let b = *y;
    *x = b;
    *y = a;
}


// Predicates
predicate i32(self: Ref) {
  acc(self.val_int, write)
}

// Preconds
inhale acc(x.val_ref, write)
  && ( acc(i32(x.val_ref), write)
  && ( acc(y.val_ref, write)
  &&   acc(i32(y.val_ref), write)
))

// Postconds
assert x.val_ref.val_int == old[pre](y.val_ref.val_int)
    && y.val_ref.val_int == old[pre](x.val_ref.val_int)

exhale acc(i32(x.val_ref), write) && acc(i32(y.val_ref), write)
