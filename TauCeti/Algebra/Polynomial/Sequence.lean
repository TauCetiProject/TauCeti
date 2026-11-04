/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Sequence

/-!
# Linear independence of polynomial sequences

This file generalizes Mathlib's `Polynomial.Sequence.linearIndependent` from domains to additive
cancellation semirings where the sequence elements have right-regular leading coefficients, and
constructs a basis over rings when those coefficients are units.

## Main statements

* `Polynomial.Sequence.linearIndependent_of_isRightRegular_leadingCoeff`: a polynomial sequence
  whose elements have right-regular leading coefficients is linearly independent over any additive
  cancellation semiring.
* `Polynomial.Sequence.basisOfIsUnitLeadingCoeff`: the corresponding basis of `R[X]`.
-/

public section

namespace Polynomial.Sequence

open Module Submodule

variable {R : Type*}

section Semiring

variable [Semiring R] (S : Polynomial.Sequence R)

/-- Polynomials in a polynomial sequence whose leading coefficients are right-regular are linearly
independent. -/
theorem linearIndependent_of_isRightRegular_leadingCoeff
    [IsRightCancelAdd R] (hCoeff : ∀ i, IsRightRegular (S i).leadingCoeff) :
    LinearIndependent R S := by
  refine linearIndependent_iff'ₛ.2 fun s f g => ?_
  -- Peel off the largest index: only `S a` contributes to the coefficient of `X ^ a`.
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    intro hsum i hi
    have ha : a ∉ s := fun h => (hlt a h).false
    have hzero (c : ℕ → R) : (∑ j ∈ s, c j • S j).coeff a = 0 := by
      rw [finsetSum_coeff]
      exact Finset.sum_eq_zero fun j hj => by
        rw [coeff_smul, coeff_eq_zero_of_natDegree_lt (by simpa using hlt j hj), smul_zero]
    rw [Finset.sum_insert ha, Finset.sum_insert ha] at hsum
    have hfg : f a = g a := hCoeff a <| by
      simpa [hzero, leadingCoeff] using congrArg (coeff · a) hsum
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hfg
    · have := AddCommMagma.IsRightCancelAdd.toIsLeftCancelAdd R
      refine ih (Polynomial.ext fun n => add_left_cancel (a := (g a • S a).coeff n) ?_) i hi
      simpa only [hfg, coeff_add] using congrArg (coeff · n) hsum

end Semiring

section Ring

variable [Ring R] (S : Polynomial.Sequence R)

/-- Every polynomial sequence with unit leading coefficients is a basis of `R[X]`. -/
noncomputable def basisOfIsUnitLeadingCoeff
    (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) :
    Basis ℕ R R[X] :=
  Basis.mk (S.linearIndependent_of_isRightRegular_leadingCoeff fun i =>
      (hCoeff i).isRegular.right)
    (eq_top_iff.mp (S.span hCoeff))

/-- The `i`-th basis vector is the `i`-th polynomial in the sequence. -/
@[simp]
theorem basisOfIsUnitLeadingCoeff_apply
    (hCoeff : ∀ i, IsUnit (S i).leadingCoeff) (i : ℕ) :
    S.basisOfIsUnitLeadingCoeff hCoeff i = S i :=
  Basis.mk_apply _ _ _

end Ring

end Polynomial.Sequence
