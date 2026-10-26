//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

trait Trait {
    fn get(&self) -> u32;
}

impl Trait for u32 {
    fn get(&self) -> u32 {
        *self
    }
}

impl Trait for bool {
    fn get(&self) -> u32 {
        *self as u32
    }
}

fn bool_to_trait(b: bool) -> impl Trait {
    b
}

fn mk_trait(b: bool) -> Box<dyn Trait> {
    if b {
        Box::new(b)
    } else {
        Box::new(0)
    }
}

trait Into<T> {
    fn into(self) -> T;
}

// Checking that nothing wrong happens when mixing type variable indices
fn mk_into<U, V, T: Into<V> + 'static, W: Into<V> + 'static>(
    b: bool,
    x: T,
    y: W,
) -> Box<dyn Into<V>> {
    if b {
        Box::new(x)
    } else {
        Box::new(y)
    }
}

trait Trivial {}

fn dyn_closure(_: impl Trivial) {
    let f = |x: u32| -> u32 { x };
}

// A shared trait object stored inside an ADT, as in MemoryMappingBuilder.
struct DynBuilder<'a> {
    source: Option<&'a dyn Trait>,
    is_u32: bool,
    offset: u64,
}

impl<'a> DynBuilder<'a> {
    fn new() -> Self {
        Self {
            source: None,
            is_u32: false,
            offset: 0,
        }
    }

    fn from_u32(mut self, source: &'a u32) -> Self {
        self.is_u32 = true;
        self.source = Some(source as &dyn Trait);
        self
    }

    fn from_bool(mut self, source: &'a bool) -> Self {
        self.source = Some(source as &dyn Trait);
        self
    }

    fn offset(mut self, offset: u64) -> Self {
        self.offset = offset;
        self
    }
}

#[verify::test]
fn dyn_builder_configuration() {
    let number = 42;
    let flag = false;
    let builder = DynBuilder::new()
        .from_u32(&number)
        .from_bool(&flag)
        .offset(7);
    match builder.source {
        Some(_) => (),
        None => panic!(),
    }
    assert!(builder.is_u32);
    assert!(builder.offset == 7);
}
