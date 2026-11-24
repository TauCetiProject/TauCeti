/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Sets.Opens

import TauCeti.Analysis.Calculus.FDeriv.Equiv

/-!
# The Jacobian matrix of an inverse map on Euclidean space

On `EuclideanSpace ℝ ι`, the derivative of a map at a point is the operator of its Jacobian matrix
under `Matrix.toEuclideanCLM`. For a map `Φ` differentiable on an open set `U` and mapping it into
an open set `V`, with an inverse `Ψ` differentiable on `V`, the derivatives compose to the identity
(`TauCeti.fderiv_comp_fderiv_eq_id_of_invOn`). In matrix form, the inverse of the Jacobian matrix
of `Φ` at `y` is the Jacobian matrix of `Ψ` at `Φ y`. This is the form in which the inverse
Jacobian enters coefficient formulas after a change of variables.

## Main results

* `TauCeti.toEuclideanCLM_inv_fderiv_of_invOn`: the operator of the inverse Jacobian matrix
  `DΦ(y)⁻¹` is `DΨ(Φ y)`.
-/

public section

open Set TopologicalSpace

namespace TauCeti

/-- For a map `Φ` of Euclidean space, differentiable on `U` and mapping it into `V`, with inverse
`Ψ` differentiable on `V`, the operator of the inverse Jacobian matrix of `Φ` at `y ∈ U` is
`DΨ(Φ y)`. -/
theorem toEuclideanCLM_inv_fderiv_of_invOn {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Opens (EuclideanSpace ℝ ι)} {Φ Ψ : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hΦ : DifferentiableOn ℝ Φ U) (hmaps : MapsTo Φ U V) (hΨ : DifferentiableOn ℝ Ψ V)
    (hΦΨ : RightInvOn Ψ Φ V) (hΨΦ : LeftInvOn Ψ Φ U) {y : EuclideanSpace ℝ ι}
    (hy : y ∈ (U : Set (EuclideanSpace ℝ ι))) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) ((Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Φ y))⁻¹ =
      fderiv ℝ Ψ (Φ y) := by
  rw [Matrix.inv_eq_right_inv (B := (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm (fderiv ℝ Ψ (Φ y))),
    StarAlgEquiv.apply_symm_apply]
  rw [← map_mul, ContinuousLinearMap.mul_def,
    fderiv_comp_fderiv_eq_id_of_invOn hΦ hmaps hΨ hΦΨ hΨΦ hy, ← ContinuousLinearMap.one_def,
    map_one]

end TauCeti
