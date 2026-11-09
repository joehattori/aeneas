//@ [!lean] skip
//@ charon-args=--opaque=effectful::read --opaque=effectful::write
//@ [lean] subdir=Effectful
//@ [lean] aeneas-args=-split-files -effectful effectful::read -effectful effectful::write

pub fn read(_addr: u64) -> u8 {
    unreachable!()
}

pub fn write(_addr: u64, _v: u8) {
    unreachable!()
}

pub fn pure_helper(x: u8, y: u8) -> u8 {
    x.wrapping_add(y)
}

pub fn double_fetch(addr: u64) -> (u8, u8) {
    let a = read(addr);
    let b = read(addr);
    (a, b)
}

pub struct Device {
    pub base: u64,
}

impl Device {
    pub fn write_reg(&self, offset: u64, v: u8) {
        write(self.base + offset, v);
    }
}

pub fn read_sum(addr: u64, count: u64) -> u8 {
    let mut acc: u8 = 0;
    let mut i: u64 = 0;
    while i < count {
        acc = acc.wrapping_add(read(addr + i));
        i += 1;
    }
    acc
}

pub fn read_into(addr: u64, dst: &mut [u8]) {
    dst[0] = read(addr);
}

pub fn caller(dev: &Device, addr: u64, dst: &mut [u8]) -> u8 {
    let (a, b) = double_fetch(addr);
    dev.write_reg(0, pure_helper(a, b));
    read_into(addr + 1, dst);
    read_sum(addr, 2)
}

pub trait Tr {
    fn next(&mut self) -> u8;
}

pub struct EffImpl {
    pub addr: u64,
}

impl Tr for EffImpl {
    fn next(&mut self) -> u8 {
        read(self.addr)
    }
}

pub struct PureImpl {
    pub val: u8,
}

impl Tr for PureImpl {
    fn next(&mut self) -> u8 {
        self.val
    }
}

pub fn use_it<T: Tr>(t: &mut T) -> (u8, u8) {
    let a = t.next();
    let b = t.next();
    (a, b)
}
