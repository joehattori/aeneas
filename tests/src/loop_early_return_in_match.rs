//@ [!lean] skip
// A loop with an early return, nested in a branch of a `match`. The statements
// after the loop in this branch don't return: the control-flow continues after
// the `match`.

fn check_then_inc(start: Option<u32>, xs: &[u32]) -> Option<u32> {
    let base = match start {
        Some(b) => {
            for x in xs {
                if *x > b {
                    return None;
                }
            }
            b
        }
        None => 0,
    };
    Some(base + 1)
}
