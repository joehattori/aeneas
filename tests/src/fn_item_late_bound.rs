//@ [!lean] skip
// A method whose `&self` region is late-bound, used as a closure. The type of
// the function item binds that region: `for<'a> Region::end<'a>`.

struct Region {
    start: u64,
    len: u64,
}

impl Region {
    fn end(&self) -> u64 {
        self.start + self.len
    }
}

fn apply<T, U, F: FnOnce(T) -> U>(x: T, f: F) -> U {
    f(x)
}

fn region_end(r: &Region) -> u64 {
    apply(r, Region::end)
}
