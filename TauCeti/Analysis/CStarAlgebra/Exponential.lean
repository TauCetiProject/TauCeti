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
# Exponential unitaries of self-adjoint elements and projections

Let `A` be a complete normed complex algebra with a continuous star structure and `h` a
self-adjoint element of `A`. The adjoint of the unitary `selfAdjoint.expUnitary h` is
`expUnitary (-h)`, `selfAdjoint.star_expUnitary`, whose underlying element is `exp (-(I • h))`.

By `IsIdempotentElem.exp_smul`, an idempotent `e` in a normed algebra satisfies
`exp (z • e) = 1 + (exp z - 1) • e`. For a star projection `p`, the one-parameter unitary group
`t ↦ expUnitary (t • p)` therefore has underlying element `1 + (exp (t * I) - 1) • p`, taking the
value `1 - 2 • p` at `t = π`. Conversely, every self-adjoint unitary `u` arises as
`expUnitary (π • r)` for the star projection `r = 2⁻¹ • (1 - u)`.

## Main declarations

* `selfAdjoint.star_expUnitary`: the adjoint of `expUnitary`.
* `IsStarProjection.coe_expUnitary_smul`, `IsStarProjection.coe_expUnitary_pi_smul`: explicit
  formulas for `expUnitary (t • p)` and `expUnitary (π • p)` of a star projection `p`.
* `Unitary.isStarProjection_half_one_sub`, `Unitary.expUnitary_pi_smul_half_one_sub`: a
  self-adjoint unitary `u` yields a star projection `r = 2⁻¹ • (1 - u)` satisfying
  `expUnitary (π • r) = u`.

## References

* O. Bratteli and D. W. Robinson, *Operator Algebras and Quantum Statistical Mechanics 1*, 2nd ed.,
  Section 2.5.3, for the one-parameter group `t ↦ exp (ith)` of a self-adjoint element.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6, for the rotation path of a
  self-adjoint unitary via `r = (1 - u) / 2`.
-/

public section

noncomputable section

section Star

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [ContinuousStar A]
  [CompleteSpace A] [StarModule ℂ A]

namespace selfAdjoint

/-- The adjoint of `expUnitary` is `expUnitary` of the negative. -/
@[simp]
theorem star_expUnitary (b : selfAdjoint A) : star (expUnitary b) = expUnitary (-b) := by
  rw [Unitary.star_eq_inv, inv_eq_of_mul_eq_one_right]
  rw [← Commute.expUnitary_add (Commute.refl (b : A)).neg_right, add_neg_cancel, expUnitary_zero]

end selfAdjoint

namespace IsStarProjection

/-- For a star projection `p`, the underlying element of `expUnitary (t • p)` is
`1 + (exp (t * I) - 1) • p`. -/
theorem coe_expUnitary_smul {p : A} (hp : IsStarProjection p) (t : ℝ) :
    ((selfAdjoint.expUnitary (t • ⟨p, hp.isSelfAdjoint⟩) : unitary A) : A) =
      1 + (Complex.exp (t * Complex.I) - 1) • p := by
  simp only [selfAdjoint.expUnitary_coe, selfAdjoint.val_smul]
  rw [← Complex.coe_smul t p, smul_smul, mul_comm Complex.I, hp.isIdempotentElem.exp_complex_smul]

/-- At `t = π`, `expUnitary (π • p)` equals the reflection `1 - 2 • p`. -/
theorem coe_expUnitary_pi_smul {p : A} (hp : IsStarProjection p) :
    ((selfAdjoint.expUnitary (Real.pi • ⟨p, hp.isSelfAdjoint⟩) : unitary A) : A) =
      1 - (2 : ℝ) • p := by
  have htwo : (-1 - 1 : ℂ) = -((2 : ℝ) : ℂ) := by norm_num
  rw [hp.coe_expUnitary_smul Real.pi, Complex.exp_pi_mul_I, htwo, neg_smul, Complex.coe_smul,
    sub_eq_add_neg]

end IsStarProjection

end Star

namespace Unitary

/-- For a self-adjoint unitary `u` in a real star-algebra, `(2⁻¹ : ℝ) • (1 - u)` is a star
projection. -/
theorem isStarProjection_half_one_sub {A : Type*} [Ring A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [StarModule ℝ A] (u : unitary A)
    (hu : IsSelfAdjoint (u : A)) : IsStarProjection ((2⁻¹ : ℝ) • (1 - (u : A))) := by
  have hu2 : (u : A) * (u : A) = 1 := by simpa [hu.star_eq] using Unitary.coe_star_mul_self u
  refine ⟨?_, (IsSelfAdjoint.all (2⁻¹ : ℝ)).smul ((IsSelfAdjoint.one A).sub hu)⟩
  have hsub : (1 - (u : A)) * (1 - (u : A)) = (2 : ℝ) • (1 - (u : A)) := by
    simp only [mul_sub, sub_mul, mul_one, one_mul, hu2, two_smul]; abel
  rw [IsIdempotentElem, smul_mul_smul_comm, hsub, smul_smul]; norm_num

/-- Every self-adjoint unitary `u` is `expUnitary (π • r)` for `r = 2⁻¹ • (1 - u)`. -/
theorem expUnitary_pi_smul_half_one_sub {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [ContinuousStar A] [CompleteSpace A] [StarModule ℂ A] (u : unitary A)
    (hu : IsSelfAdjoint (u : A)) :
    selfAdjoint.expUnitary (Real.pi • ⟨(2⁻¹ : ℝ) • (1 - (u : A)),
      (isStarProjection_half_one_sub u hu).isSelfAdjoint⟩) = u := by
  ext; rw [(isStarProjection_half_one_sub u hu).coe_expUnitary_pi_smul, smul_smul]; norm_num

end Unitary
