/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Analysis.Normed.Algebra.Exponential

/-!
# Exponential unitaries in Banach star-algebras

Let `A` be a complete normed complex algebra with a continuous star structure and `h` a
self-adjoint element of `A`. The adjoint of the unitary `selfAdjoint.expUnitary h` is
`expUnitary (-h)`, `selfAdjoint.star_expUnitary`, whose underlying element is `exp (-(I • h))`.
For a star projection `p`, evaluating `expUnitary` at `π • p` yields the self-adjoint unitary
reflection `1 - (2 : ℝ) • p` (`IsStarProjection.coe_expUnitary_pi_smul`).

## Main declarations

* `selfAdjoint.star_expUnitary`: the adjoint of `expUnitary`.
* `IsStarProjection.coe_expUnitary_pi_smul`: `(expUnitary (π • p) : A) = 1 - (2 : ℝ) • p`.

## References

Bratteli--Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, second edition,
Section 2.5.3, for the one-parameter group `t ↦ exp (ith)` of a self-adjoint element.
-/

public section

noncomputable section

namespace selfAdjoint

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

/-- The adjoint of `expUnitary` is `expUnitary` of the negative. -/
@[simp]
theorem star_expUnitary (b : selfAdjoint A) : star (expUnitary b) = expUnitary (-b) := by
  rw [Unitary.star_eq_inv, inv_eq_of_mul_eq_one_right]
  rw [← Commute.expUnitary_add (Commute.refl (b : A)).neg_right, add_neg_cancel, expUnitary_zero]

/-- Evaluating `selfAdjoint.expUnitary` at `π • p` for a star projection `p` produces the
self-adjoint unitary reflection `1 - (2 : ℝ) • p`. -/
theorem _root_.IsStarProjection.coe_expUnitary_pi_smul {p : A} (hp : IsStarProjection p) :
    (expUnitary ⟨Real.pi • p, (IsSelfAdjoint.all Real.pi).smul hp.isSelfAdjoint⟩ : A) =
      1 - (2 : ℝ) • p := by
  rw [expUnitary_coe]
  dsimp only
  rw [← Complex.coe_smul, smul_smul, mul_comm, hp.isIdempotentElem.exp_smul,
    ← Complex.exp_eq_exp_ℂ, Complex.exp_pi_mul_I]
  have htwo : (-1 - 1 : ℂ) = -((2 : ℝ) : ℂ) := by norm_num
  rw [htwo, neg_smul, Complex.coe_smul, ← sub_eq_add_neg]

end selfAdjoint
