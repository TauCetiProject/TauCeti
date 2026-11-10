/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Defs

import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# The Jacobian matrix of an inverse map on Euclidean space

On `EuclideanSpace ℝ ι`, the derivative of a map at a point is the operator of its Jacobian matrix
under `Matrix.toEuclideanCLM`. If `Φ ∘ Ψ = id` near `x`, with `Ψ` differentiable at `x` and `Φ`
differentiable at `Ψ x`, the derivatives compose to the identity
(`TauCeti.fderiv_comp_fderiv_eq_id_of_eventuallyEq`). In matrix form, the inverse of the Jacobian
matrix of `Φ` at `Ψ x` is the Jacobian matrix of `Ψ` at `x`. This is the form in which the inverse
Jacobian enters coefficient formulas after a change of variables.

## Main results

* `TauCeti.toEuclideanCLM_inv_fderiv_of_eventuallyEq`: the operator of the inverse Jacobian matrix
  `DΦ(Ψ x)⁻¹` is `DΨ(x)`.
-/

public section

open scoped Topology

namespace TauCeti

/-- If `Φ ∘ Ψ = id` near `x` for maps of Euclidean space, with `Ψ` differentiable at `x` and `Φ`
differentiable at `Ψ x`, then the operator of the inverse Jacobian matrix of `Φ` at `Ψ x` is
`DΨ(x)`. -/
theorem toEuclideanCLM_inv_fderiv_of_eventuallyEq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {x : EuclideanSpace ℝ ι}
    (hΦ : DifferentiableAt ℝ Φ (Ψ x)) (hΨ : DifferentiableAt ℝ Ψ x) (h : Φ ∘ Ψ =ᶠ[𝓝 x] id) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) ((Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ (Ψ x)))⁻¹ =
      fderiv ℝ Ψ x := by
  rw [Matrix.inv_eq_right_inv (B := (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Ψ x)),
    StarAlgEquiv.apply_symm_apply]
  rw [← map_mul, ContinuousLinearMap.mul_def,
    fderiv_comp_fderiv_eq_id_of_eventuallyEq hΦ hΨ h, ← ContinuousLinearMap.one_def, map_one]

end TauCeti
