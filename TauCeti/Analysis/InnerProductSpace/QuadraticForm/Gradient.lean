/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# The gradient of a symmetric quadratic form

For a symmetric continuous linear map `A` on a real Hilbert space, the quadratic form
`x ↦ ⟪A x, x⟫ / 2` has gradient `A x` at `x`. Symmetry is needed: for a quarter turn `A` of the
plane the form vanishes identically, so its gradient is `0`, while `A x ≠ 0` for `x ≠ 0`.

The derivative itself is Mathlib's `LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf`;
this file restates it for the gradient and the normalization with the factor `1 / 2`, in which
quadratic objectives are usually written.

## Main results

* `LinearMap.IsSymmetric.hasGradientAt_inner_div_two`,
  `LinearMap.IsSymmetric.gradient_inner_div_two`: the gradient of `x ↦ ⟪A x, x⟫ / 2` is `A x`.
-/

public section

open scoped Gradient RealInnerProductSpace

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {A : E →L[ℝ] E}

/-- The quadratic form `x ↦ ⟪A x, x⟫ / 2` of a symmetric continuous linear map `A` has gradient
`A x` at `x`. -/
theorem hasGradientAt_inner_div_two (hA : (A : E →ₗ[ℝ] E).IsSymmetric) (x : E) :
    HasGradientAt (fun x ↦ ⟪A x, x⟫ / 2) (A x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hA.hasStrictFDerivAt_reApplyInnerSelf x).hasFDerivAt.mul_const (2⁻¹ : ℝ) using 1
  · ext y
    simp [ContinuousLinearMap.reApplyInnerSelf_apply, div_eq_mul_inv]
  · ext h
    simp

/-- The gradient of the quadratic form `x ↦ ⟪A x, x⟫ / 2` of a symmetric continuous linear map
`A` at `x` is `A x`. -/
theorem gradient_inner_div_two (hA : (A : E →ₗ[ℝ] E).IsSymmetric) (x : E) :
    ∇ (fun x ↦ ⟪A x, x⟫ / 2) x = A x :=
  (hA.hasGradientAt_inner_div_two x).gradient

end LinearMap.IsSymmetric
