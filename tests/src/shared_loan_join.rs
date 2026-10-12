//@ [!lean] skip
#![feature(register_tool)]
#![register_tool(verify)]

// Joining the match branches must account for the shared borrow inside the
// shared loan of `range`. If matching the joined contexts is unsupported, the
// translator must fall back to translating the continuation in each branch.
pub struct Range {
    pub start: u64,
    pub end: u64,
}

fn apply<F: FnMut(&&Range) -> bool>(mut predicate: F, range: &&Range) -> bool {
    predicate(range)
}

pub fn fits(range: &Range, size: u64, alignment: u64) -> bool {
    apply(
        |range| {
            match range.start % alignment {
                0 => range.start.checked_add(size - 1),
                r => range.start.checked_add(size - 1 + alignment - r),
            }
            .is_some_and(|end| end <= range.end)
        },
        &range,
    )
}

#[cfg_attr(test, test)]
#[verify::test]
pub fn test_fits() {
    assert!(fits(&Range { start: 4, end: 15 }, 4, 4));
    assert!(fits(&Range { start: 5, end: 15 }, 4, 4));
    assert!(!fits(&Range { start: 5, end: 10 }, 4, 8));
    assert!(!fits(
        &Range {
            start: u64::MAX - 3,
            end: u64::MAX,
        },
        8,
        4,
    ));
}
