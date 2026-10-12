/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import TauCeti.Geometry.Lie.Exponential.OneParameter

/-!
# Exponential lines inside the unitary group of a Banach star algebra

For an element `x` of a complete normed real star algebra `R`, the exponential line
`t ↦ exp (t • x)` is the one-parameter subgroup of `Rˣ` that `x` generates.  This file
characterizes the generators whose whole line stays inside the unitary group: they are exactly
the skew-adjoint elements, `star x = -x`.

One direction is Mathlib's `exp_mem_unitary_of_mem_skewAdjoint`, applied at every `t • x`.  The
other is where the *line*, rather than a single exponential, is doing the work.  Unitarity of
`exp (t • x)` says `star (exp (t • x)) = exp (t • x)⁻¹`, and both sides are exponentials:
the left is `exp (t • star x)` and the right is `exp (t • (-x))`.  Two exponential lines that
agree have equal generators (`TauCeti.eq_of_forall_exp_smul_eq`), so `star x = -x`.  Unitarity
of the single exponential `exp x` would not be enough: `exp` is not injective, so it does not see
the generator, and it is the whole line that pins `x` down.

This is the algebra-side input for computing the Lie algebra of the unitary group; the geometric
statement is in `TauCeti/Geometry/Lie/Subgroup/Unitary.lean`.

## Main results

* `TauCeti.star_exp_eq_exp_neg_of_exp_mem_unitary`: a unitary exponential has the exponential of
  the negative as its adjoint.
* `TauCeti.forall_exp_smul_mem_unitary_iff_mem_skewAdjoint`: **an exponential line lies in the
  unitary group exactly when its generator is skew-adjoint.**
-/

public section

namespace TauCeti

open NormedSpace

section Rat

variable {R : Type*} [NormedRing R] [NormedAlgebra ℚ R] [CompleteSpace R] [StarMul R]

/-- The adjoint of a unitary exponential is the exponential of the negative.
Only a multiplicative involution is needed, in a complete normed rational algebra. -/
theorem star_exp_eq_exp_neg_of_exp_mem_unitary {y : R} (h : exp y ∈ unitary R) :
    star (exp y) = exp (-y) := by
  apply left_inv_eq_right_inv (Unitary.star_mul_self_of_mem h)
  rw [← exp_add_of_commute (Commute.refl y).neg_right, add_neg_cancel, exp_zero]

end Rat

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R] [StarRing R]
  [ContinuousStar R] [StarModule ℝ R]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- **An exponential line lies in the unitary group exactly when its generator is skew-adjoint.**
This is the Banach-algebra form of "the Lie algebra of the unitary group is the skew-adjoint
elements": the left-hand side is the condition defining the Lie algebra of a subgroup of `Rˣ`
through the exponential, and the right-hand side is `star x = -x`. -/
theorem forall_exp_smul_mem_unitary_iff_mem_skewAdjoint (x : R) :
    (∀ t : ℝ, exp (t • x) ∈ unitary R) ↔ x ∈ skewAdjoint R := by
  refine ⟨fun h => ?_, fun hx t => exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem t hx)⟩
  rw [skewAdjoint.mem_iff]
  refine eq_of_forall_exp_smul_eq fun t => ?_
  simpa only [star_exp, star_smul, star_trivial, smul_neg] using
    star_exp_eq_exp_neg_of_exp_mem_unitary (h t)

end TauCeti
