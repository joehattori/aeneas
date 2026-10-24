//@ [!lean] skip
//@ charon-args=--monomorphize-mut=except-types --remove-adt-clauses --lift-associated-types=*
//@ charon-args=--exclude core::slice::iter::{core::iter::traits::iterator::Iterator<_>}::find

// The blanket IntoIterator call is an identity. Its now-unused specialized
// Iterator declarations must not collide with the generic Iterator model.
pub fn increment_until_zero(values: &mut [u32]) -> bool {
    for value in values.iter_mut() {
        if *value == 0 {
            return true;
        }
        *value += 1;
    }
    false
}
