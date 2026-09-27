/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Module (Matrix n n R) (n → R)` through `Matrix.mulVec` is the action restricted below.
public import Mathlib.LinearAlgebra.Matrix.Action
-- `GL` occurs in every statement below.
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
-- `SubMulAction` carries the action on the nonzero vectors.
public import Mathlib.GroupTheory.GroupAction.SubMulAction
-- `Nat.card` occurs in the count below, and `Nat.card_fun` and `Finite.card_option` prove it.
public import Mathlib.SetTheory.Cardinal.Finite
-- Non-public: `Equiv.optionSubtypeNe` splits off the zero vector, inside the count only.
import Mathlib.Logic.Equiv.Option

/-!
# The general linear group permuting the nonzero vectors

An invertible matrix carries a nonzero vector to a nonzero vector, because it has an inverse; so
`GL n R` acts on the nonzero vectors of `n → R`. The underlying `GL n R`-set is
`Matrix.GeneralLinearGroup.nonzeroVectors`, a `SubMulAction` of the `Matrix.mulVec` action of
`Mathlib.LinearAlgebra.Matrix.Action`, and the permutation representation it carries is Mathlib's
`MulAction.toPermHom`.

That representation is faithful as soon as `R` is nontrivial: the standard basis vector `eⱼ` is
then nonzero and `g • eⱼ` is the `j`-th column of `g`, so an element acting trivially on the
nonzero vectors has the columns of the identity matrix. Over a finite ring the set being permuted
has `|R| ^ |n| - 1` elements, which is what can make the representation surjective as well in
small cases; the smallest such coincidence, `GL₂(𝔽₂) ≅ S₃`, is in
`TauCeti/LinearAlgebra/Matrix/GeneralLinearGroup/FieldCardTwo.lean`.

## Main definitions

* `Matrix.GeneralLinearGroup.nonzeroVectors`: the nonzero vectors of `n → R` as a `GL n R`-set.

## Main results

* `Matrix.GeneralLinearGroup.faithfulSMulNonzeroVectors`: the action on the nonzero vectors is
  faithful over a nontrivial ring.
* `Matrix.GeneralLinearGroup.natCard_nonzeroVectors`: there are `|R| ^ |n| - 1` nonzero vectors.
-/

public section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [Semiring R]

/-- **The nonzero vectors of `n → R` as a `GL n R`-set.** An invertible matrix has an inverse, so
it cannot send a nonzero vector to zero; the action is the `Matrix.mulVec` action of
`Mathlib.LinearAlgebra.Matrix.Action` read through the unit group. -/
def nonzeroVectors (n R : Type*) [Fintype n] [DecidableEq n] [Semiring R] :
    SubMulAction (GL n R) (n → R) where
  carrier := {v | v ≠ 0}
  smul_mem' g _ hv := (smul_ne_zero_iff_ne g).2 hv

@[simp]
theorem mem_nonzeroVectors {v : n → R} : v ∈ nonzeroVectors n R ↔ v ≠ 0 := Iff.rfl

/-- **The action of `GL n R` on the nonzero vectors of `n → R` is faithful** over a nontrivial
ring. -/
instance faithfulSMulNonzeroVectors [Nontrivial R] :
    FaithfulSMul (GL n R) (nonzeroVectors n R) where
  eq_of_smul_eq_smul {g h} H := by
    -- The standard basis vector `eⱼ` is nonzero, and `g • eⱼ` is the `j`-th column of `g`.
    refine Units.ext (Matrix.ext fun i j ↦ ?_)
    have hj : (Pi.single j (1 : R)) ∈ nonzeroVectors n R := by
      refine mem_nonzeroVectors.2 fun hc ↦ one_ne_zero (α := R) ?_
      simpa using congrFun hc j
    have hcol := congrArg Subtype.val (H ⟨Pi.single j 1, hj⟩)
    simp only [SubMulAction.val_smul, Units.smul_def, Matrix.smul_eq_mulVec,
      Matrix.mulVec_single_one] at hcol
    exact congrFun hcol i

/-- **The number of nonzero vectors** is `|R| ^ |n| - 1`. -/
theorem natCard_nonzeroVectors [Finite R] :
    Nat.card (nonzeroVectors n R) = Nat.card R ^ Nat.card n - 1 := by
  classical
  have e : ↥(nonzeroVectors n R) ≃ {v : n → R // v ≠ 0} :=
    Equiv.subtypeEquivRight fun _ ↦ mem_nonzeroVectors
  have key := Nat.card_congr (Equiv.optionSubtypeNe (0 : n → R))
  rw [Finite.card_option, Nat.card_fun] at key
  rw [Nat.card_congr e]
  omega

end Matrix.GeneralLinearGroup
