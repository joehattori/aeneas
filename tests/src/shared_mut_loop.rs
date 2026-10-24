//@ [!lean] skip
//@ [lean] aeneas-args=-filter-trait-methods
//@ charon-args=--exclude=core::slice::iter::_::find
#![feature(register_tool)]
#![register_tool(verify)]

// A shared receiver contains a mutable slice borrow. Preparing a loop must
// keep that borrow in its frozen abstraction instead of copying it into a
// fresh shared loan. Minimized from AddressAllocatorSet::get in crosvm.
pub struct Entry {
    pub key: u32,
    pub value: u32,
}

impl Entry {
    pub fn get(&self, key: u32) -> Option<&u32> {
        if self.key == key {
            Some(&self.value)
        } else {
            None
        }
    }
}

pub struct Set<'a> {
    pub entries: &'a mut [Entry],
}

impl Set<'_> {
    pub fn get(&self, key: u32) -> Option<&u32> {
        for entry in self.entries.iter() {
            let found = entry.get(key);
            if found.is_some() {
                return found;
            }
        }
        None
    }
}

#[cfg_attr(test, test)]
#[verify::test]
pub fn test_get() {
    let mut entries = [
        Entry { key: 1, value: 10 },
        Entry { key: 2, value: 20 },
        Entry { key: 2, value: 30 },
    ];
    let set = Set {
        entries: &mut entries,
    };
    assert!(*set.get(1).unwrap() == 10);
    assert!(*set.get(2).unwrap() == 20);
    assert!(set.get(3).is_none());
    set.entries[1].value = 21;
    assert!(*set.get(2).unwrap() == 21);
    assert!(entries[0].value == 10);
    assert!(entries[1].value == 21);
    assert!(entries[2].value == 30);
}

#[cfg_attr(test, test)]
#[verify::test]
pub fn test_empty() {
    let mut entries: [Entry; 0] = [];
    let set = Set {
        entries: &mut entries,
    };
    assert!(set.get(1).is_none());
}
