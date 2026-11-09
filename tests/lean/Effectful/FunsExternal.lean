module
public import Aeneas
public import Effectful.Types
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
open effectful

/-- Oracle `read`: advances `st.step` and returns `st.oracle st.step addr`. -/
def read (addr : Std.U64) (st : State) : Result (State × Std.U8) :=
  ok ({ st with step := st.step + 1 }, st.oracle st.step addr)

/-- Oracle `write`: advances `st.step` and returns `()`. -/
def write (_addr : Std.U64) (_v : Std.U8) (st : State) : Result (State × Unit) :=
  ok ({ st with step := st.step + 1 }, ())

@[step]
theorem read.spec (addr : Std.U64) (st : State) :
    _root_.read addr st ⦃ res =>
      res = ({ st with step := st.step + 1 }, st.oracle st.step addr) ⦄ := by
  unfold _root_.read
  simp

@[step]
theorem write.spec (addr : Std.U64) (v : Std.U8) (st : State) :
    write addr v st ⦃ res =>
      res = ({ st with step := st.step + 1 }, ()) ⦄ := by
  unfold write
  simp
