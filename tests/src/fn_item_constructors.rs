//@ [!lean] skip
// Enum constructors used as closures. Their function items have `FnOnce`
// implementations, which must get distinct names.

enum E {
    A(u32),
    B(u32),
}

fn apply<T, U, F: FnOnce(T) -> U>(x: T, f: F) -> U {
    f(x)
}

fn mk_a(x: u32) -> E {
    apply(x, E::A)
}

fn mk_b(x: u32) -> E {
    apply(x, E::B)
}
