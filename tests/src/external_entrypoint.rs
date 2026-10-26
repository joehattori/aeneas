//@ [!lean] skip
//@ charon-args=--start-from=core::convert::identity --include=core::convert::identity

// An explicitly selected dependency function must survive dependency pruning,
// even when no local function calls it. The generated Lean must contain identity.
