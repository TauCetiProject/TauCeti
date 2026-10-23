/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import TauCeti.Geometry.Lie.Exponential.OneParameter

/-!
# Unitary exponentials and exponential lines

In a complete normed rational algebra `R` with a multiplicative involution (`StarMul R`), a
unitary exponential satisfies `star (exp y) = exp (-y)`. Unitarity makes `star (exp y)` a left
inverse of `exp y`, while Mathlib's exponential-inverse API makes `exp (-y)` a right inverse.
Uniqueness of inverses identifies them. This identity requires no additive or continuous star
structure, and no real scalar action.

For a complete normed real star algebra `R` with continuous star compatible with real scalar
multiplication, the exponential line `t ↦ exp (t • x)` is the one-parameter subgroup of `Rˣ`
that `x` generates. Its whole line stays inside the unitary group exactly when `x` is
skew-adjoint, `star x = -x`.

For this line characterization, one direction is Mathlib's
`exp_mem_unitary_of_mem_skewAdjoint`, applied at every `t • x`. The converse uses the pointwise
inverse identity above together with star/exponential compatibility. Unitarity of
`exp (t • x)` says `star (exp (t • x)) = exp (t • x)⁻¹`, and both sides are exponentials:
the left is `exp (t • star x)` and the right is `exp (t • (-x))`.  Two exponential lines that
agree have equal generators (`TauCeti.eq_of_forall_exp_smul_eq`), so `star x = -x`.  Unitarity
of the single exponential `exp x` would not be enough: `exp` is not injective, so it does not see
the generator, and it is the whole line that pins `x` down.

The line characterization is the algebra-side input for computing the Lie algebra of the unitary
group; the geometric statement is in `TauCeti/Geometry/Lie/Subgroup/Unitary.lean`.

## Main results

* `TauCeti.star_exp_eq_exp_neg_of_exp_mem_unitary`: a unitary exponential has the exponential of
  the negative as its adjoint, in a complete normed rational algebra with a multiplicative
  involution.
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
  simpa only [Ring.inverse_exp] using Ring.mul_inverse_cancel _ (isUnit_exp y)

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
