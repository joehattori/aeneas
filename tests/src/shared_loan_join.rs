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

// A shared borrow of this set freezes the mutable slice field. Loop joins
// must not duplicate the nested mutable borrow when reborrowing shared loans.
pub struct ResultSet<'a> {
    pub results: &'a mut [Result<u64, u64>],
}

impl ResultSet<'_> {
    pub fn first_success(&self) -> Result<u64, u64> {
        let mut last = Err(0);
        for result in self.results.iter() {
            last = *result;
            if last.is_ok() {
                return last;
            }
        }
        last
    }
}

fn expect_ok(result: Result<u64, u64>, expected: u64) {
    match result {
        Ok(value) => assert!(value == expected),
        Err(_) => panic!(),
    }
}

fn expect_err(result: Result<u64, u64>, expected: u64) {
    match result {
        Ok(_) => panic!(),
        Err(error) => assert!(error == expected),
    }
}

#[cfg_attr(test, test)]
#[verify::test]
pub fn test_first_success() {
    let mut empty = [];
    expect_err(
        ResultSet {
            results: &mut empty,
        }
        .first_success(),
        0,
    );
    let mut failures = [Err(1), Err(2)];
    expect_err(
        ResultSet {
            results: &mut failures,
        }
        .first_success(),
        2,
    );
    let mut results = [Err(1), Ok(42), Ok(7)];
    let set = ResultSet {
        results: &mut results,
    };
    expect_ok(set.first_success(), 42);
    // Ending the shared borrow must leave the mutable slice available.
    results[1] = Ok(8);
    expect_ok(
        ResultSet {
            results: &mut results,
        }
        .first_success(),
        8,
    );
}
