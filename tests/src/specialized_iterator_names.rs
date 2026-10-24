//@ [!lean] skip
//@ charon-args=--monomorphize-mut=except-types --remove-adt-clauses --lift-associated-types * --exclude core::slice::iter::_::find
#![feature(register_tool)]
#![register_tool(verify)]

pub trait Pass: Sized {
    fn pass(self) -> Self {
        self
    }
}
impl<T> Pass for T {}

pub fn pass_value<T>(value: T) -> T {
    value.pass()
}

// Shared and mutable iterators refer to the same external trait models.
// Generic and specialized default methods must still have distinct names.
pub fn fill(values: &mut [u32]) {
    let _taken = values.iter().take(0);
    let values = values.pass();
    for value in values.iter_mut() {
        *value = 7;
    }
}

#[cfg_attr(test, test)]
#[verify::test]
pub fn test_fill() {
    assert!(pass_value(true));
    let mut values = [1, 2];
    fill(&mut values);
    assert!(values[0] == 7);
    assert!(values[1] == 7);
}
