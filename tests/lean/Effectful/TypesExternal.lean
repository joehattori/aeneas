module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error

namespace effectful

/-- Oracle state for effectful tests: `step` counts effectful operations and
    `oracle` yields the value read at each step and address. -/
structure State where
  step : Nat
  oracle : Nat → Std.U64 → Std.U8

end effectful
