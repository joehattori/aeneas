//@ [!lean] skip
// Function pointers without regions: their types and calls through them.

pub struct Callbacks {
    pub on_event: fn(u32) -> u32,
    pub ready: fn() -> bool,
    pub count: u32,
}

fn get_count(c: &Callbacks) -> u32 {
    c.count
}

fn set_on_event(c: Callbacks, f: fn(u32) -> u32) -> Callbacks {
    Callbacks { on_event: f, ..c }
}

fn call(f: fn(u32) -> u32, x: u32) -> u32 {
    f(x)
}

fn call_ready(c: &Callbacks) -> bool {
    (c.ready)()
}

fn call_twice(c: &Callbacks, x: u32) -> u32 {
    let y = (c.on_event)(x);
    (c.on_event)(y)
}
