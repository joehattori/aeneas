//@ [!lean] skip

#![feature(register_tool)]
#![register_tool(verify)]

struct Struct {
    name: String,
}

// Local names must not shadow the namespace of a builtin function.
fn push(alloc: u32, mut values: Vec<u32>) -> Vec<u32> {
    values.push(alloc);
    values
}

// The same applies to generic parameters and types in their signatures.
#[allow(non_camel_case_types)]
fn singleton<alloc>(value: alloc) -> Vec<alloc> {
    let mut values = Vec::new();
    values.push(value);
    values
}

mod nested {
    pub fn id(value: u32) -> u32 {
        value
    }
}

// User-defined namespace roots must also be reserved, for parameters and lets.
fn call_nested(nested: u32) -> u32 {
    nested::id(nested)
}

fn local_nested(value: u32) -> u32 {
    let nested = nested::id(value);
    nested::id(nested)
}

// Std is also a namespace root in the backend's predefined names.
#[allow(non_upper_case_globals)]
fn const_namespace<const Std: usize>(values: [u32; Std]) -> u32 {
    values[0]
}

#[verify::test]
fn namespace_collisions() {
    let values = push(2, singleton(1));
    assert!(values[0] == 1);
    assert!(values[1] == 2);
    assert!(call_nested(3) == 3);
    assert!(local_nested(4) == 4);
    assert!(const_namespace([5]) == 5);
}
