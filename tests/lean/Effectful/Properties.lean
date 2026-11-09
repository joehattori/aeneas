module
public import Aeneas
public import Effectful.Funs
public section

open Aeneas Aeneas.Std Result ControlFlow Error

namespace effectful

@[step]
theorem double_fetch_spec (addr : Std.U64) (st : State) :
    double_fetch addr st ⦃ res =>
      res = ({ st with step := st.step + 2 },
        (st.oracle st.step addr, st.oracle (st.step + 1) addr)) ⦄ := by
  unfold double_fetch
  step*

theorem double_fetch_can_differ (addr : Std.U64) :
    ∃ st st' a b, double_fetch addr st = ok (st', (a, b)) ∧ a ≠ b := by
  let st : State := ⟨0, fun i _ => if i = 0 then 1#u8 else 2#u8⟩
  refine ⟨st, { st with step := 2 }, 1#u8, 2#u8, ?_, by decide⟩
  unfold double_fetch _root_.read
  simp [st]

@[step]
theorem Device.write_reg_spec (dev : Device) (offset : Std.U64) (v : Std.U8) (st : State)
    (h : dev.base.val + offset.val ≤ U64.max) :
    dev.write_reg offset v st ⦃ res =>
      res = ({ st with step := st.step + 1 }, ()) ⦄ := by
  unfold Device.write_reg
  step*

@[step]
theorem read_into_spec (addr : Std.U64) (dst : Slice Std.U8) (st : State)
    (h : 0 < dst.length) :
    read_into addr dst st ⦃ res =>
      res.1 = { st with step := st.step + 1 } ∧
      res.2 = dst.set 0#usize (st.oracle st.step addr) ⦄ := by
  unfold read_into
  step*
  simp_all

theorem read_sum_loop.body_spec (addr count : Std.U64) (acc : Std.U8) (i : Std.U64)
    (st : State) (haddr : addr.val + count.val ≤ U64.max) :
    read_sum_loop.body addr count acc i st ⦃ res =>
      if i < count then
        ∃ (i1 i3 : Std.U64),
          i1.val = addr.val + i.val ∧
          i3.val = i.val + 1 ∧
          res = cont ((core.num.U8.wrapping_add acc (st.oracle st.step i1), i3),
            { st with step := st.step + 1 })
      else
        res = done (st, acc) ⦄ := by
  unfold read_sum_loop.body
  split <;> step*
  exact ⟨i1, i3, i1_post, i3_post, by simp [*]⟩

@[step]
theorem EffImpl.next_spec (self : EffImpl) (st : State) :
    EffImpl.Insts.EffectfulTr.next self st ⦃ res =>
      res = ({ st with step := st.step + 1 }, (st.oracle st.step self.addr, self)) ⦄ := by
  unfold EffImpl.Insts.EffectfulTr.next
  step*

@[step]
theorem PureImpl.next_spec (self : PureImpl) (st : State) :
    PureImpl.Insts.EffectfulTr.next self st ⦃ res =>
      res = (st, (self.val, self)) ⦄ := by
  unfold PureImpl.Insts.EffectfulTr.next
  simp

theorem use_it_eff_can_differ (addr : Std.U64) :
    ∃ st st' a b e',
      use_it EffImpl.Insts.EffectfulTr ⟨addr⟩ st = ok (st', ((a, b), e')) ∧ a ≠ b := by
  let st : State := ⟨0, fun i _ => if i = 0 then 1#u8 else 2#u8⟩
  refine ⟨st, { st with step := 2 }, 1#u8, 2#u8, ⟨addr⟩, ?_, by decide⟩
  unfold use_it EffImpl.Insts.EffectfulTr EffImpl.Insts.EffectfulTr.next _root_.read
  simp [st]

theorem use_it_pure_eq (p : PureImpl) (st : State) :
    use_it PureImpl.Insts.EffectfulTr p st ⦃ res =>
      res = (st, ((p.val, p.val), p)) ⦄ := by
  unfold use_it PureImpl.Insts.EffectfulTr PureImpl.Insts.EffectfulTr.next
  simp

end effectful
