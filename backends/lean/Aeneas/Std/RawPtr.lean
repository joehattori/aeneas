module
public import Aeneas.Std.Scalar.Core
public import Aeneas.Std.Scalar.Casts
@[expose] public section

namespace Aeneas.Std

inductive Mutability where
| Mut | Const
deriving DecidableEq, Repr

/-- Raw pointer represented by its address in the Lean model. -/
structure RawPtr (T : Type _) (M : Mutability) where
  addr : Usize
deriving Repr, Inhabited

instance {T : Type _} {M : Mutability} : BEq (RawPtr T M) where
  beq a b := a.addr == b.addr

instance {T : Type _} {M : Mutability} : DecidableEq (RawPtr T M) :=
  fun a b => decidable_of_iff (a.addr = b.addr)
    ⟨fun h => by cases a; cases b; simp_all, fun h => by subst h; rfl⟩

abbrev MutRawPtr (T : Type _) := RawPtr T .Mut
abbrev ConstRawPtr (T : Type _) := RawPtr T .Const

@[step_pure_def, simp]
def RawPtr.cast (T' : Type) (M' : Mutability) {T : Type} {M : Mutability}
    (p : RawPtr T M) : RawPtr T' M' :=
  ⟨p.addr⟩

@[step_pure_def, simp]
def RawPtr.toUScalar {T : Type} {M : Mutability} (ty : UScalarTy)
    (p : RawPtr T M) : UScalar ty :=
  UScalar.cast ty p.addr

@[step_pure_def, simp]
def RawPtr.toIScalar {T : Type} {M : Mutability} (ty : IScalarTy)
    (p : RawPtr T M) : IScalar ty :=
  UScalar.hcast ty p.addr

@[step_pure_def, simp]
def RawPtr.ofUScalar (T : Type) (M : Mutability) {ty : UScalarTy}
    (x : UScalar ty) : RawPtr T M :=
  ⟨UScalar.cast .Usize x⟩

@[step_pure_def, simp]
def RawPtr.ofIScalar (T : Type) (M : Mutability) {ty : IScalarTy}
    (x : IScalar ty) : RawPtr T M :=
  ⟨IScalar.hcast .Usize x⟩

inductive ScalarKind where
| Signed (ty : IScalarTy)
| Unsigned (ty : UScalarTy)

class IsScalar (T : Type) where
  isScalar : (∃ ty, T = UScalar ty) ∨ (∃ ty, T = IScalar ty)

instance {ty} : IsScalar (UScalar ty) where
  isScalar := by simp

instance {ty} : IsScalar (IScalar ty) where
  isScalar := by simp

-- TODO: we can properly define this once we have separation logic
def RawPtr.cast_scalar {T} {M} (T' : Type) (M' : Mutability) [IsScalar T] [IsScalar T'] (_ : RawPtr T M) :
  Result (RawPtr T' M') :=
  .fail .undef

end Aeneas.Std
