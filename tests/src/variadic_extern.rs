//@ [!lean] skip
// Calls to external C-variadic functions.

extern "C" {
    fn fcntl(fd: i32, cmd: i32, ...) -> i32;
}

fn get_flags(fd: i32) -> i32 {
    unsafe { fcntl(fd, 1) }
}

fn set_flags(fd: i32, flags: i32) -> i32 {
    unsafe { fcntl(fd, 2, flags) }
}

fn set_two(fd: i32, x: u64, y: i32) -> i32 {
    unsafe { fcntl(fd, 3, x, y) }
}
