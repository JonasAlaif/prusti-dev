use prusti_contracts::*;
fn main() {}

// ---- Prusti signature + spec ----
#[ensures(result <= x && result <= y)]
fn min2(x: i32, y: i32) -> i32 {
    ??
}

// ---- Viper encoding ----
// Pred defns.
predicate i32(self: Ref) {
    acc(self.val_int, write)
}
// Preconds
inhale acc(i32(x), write) && acc(i32(y), write)
// Postconds
assert result.val_int <= old[pre](x.val_int) && result.val_int <= old[pre](y.val_int)
exhale acc(i32(result), write)

// ---- SuSLik input ----
{ true; result :-> 0 }
void min2(int x, int y, loc result)
{ m <= x /\ m <= y; result :-> m }
// Notes:
// - We can ignore `old[pre](...)` since it's only used for non-reference types
// - The int (i32) predicate can also be ignored
// - The return transformation should not be too difficult (maybe more so on the way back)

// ---- SuSLik output ----
void min2(int x, int y, loc result) {
    if (x <= y) {
        *result = x;
    } else {
        *result = y;
    }
}

// ---- Rust code ----
fn min2(x: i32, y: i32) -> i32 {
    let mut result: i32 = 0;
    if (x <= y) {
        result = x;
    } else {
        result = y;
    }
    result
}
