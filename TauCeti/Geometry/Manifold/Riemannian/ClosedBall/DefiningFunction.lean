/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Examples
public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.Basic
public import TauCeti.Geometry.Manifold.Riemannian.InwardUnitNormal
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic

/-!
# The gradient of the defining function of the closed unit ball

On the closed unit ball of a real inner product space `E` of dimension `n + 1`, with its Euclidean
metric (`TauCeti.closedBallEuclideanMetric`), the boundary defining function `ρ = 1 - ‖x‖²`
(`TauCeti.closedBallDefiningFunction`) has gradient `grad ρ(x) = -2x`, read in `E` through the
differential of the inclusion, so `|dρ_x| = 2‖x‖`. On the boundary sphere this gives `|dρ| = 2`
and `grad ρ = 2 ν_in`, the closed-ball instance of the gradient formula
`grad ρ(q) = |dρ_q| ν_in(q)` for boundary defining functions
(`TauCeti.IsBoundaryDefiningFunctionOn.mgradient_eq_norm_smul_inwardUnitNormal`).

## Main declarations

* `TauCeti.mvfderiv_subtypeVal_mgradient_closedBallDefiningFunction`: `grad ρ(x) = -2x` in `E`.
* `TauCeti.norm_mvfderiv_closedBallDefiningFunction`: `|dρ_x| = 2‖x‖`.
* `TauCeti.norm_mvfderiv_closedBallDefiningFunction_boundary`: `|dρ| = 2` on the sphere.
* `TauCeti.mgradient_closedBallDefiningFunction_boundary`: `grad ρ = 2 ν_in` on the sphere.
-/

public section

noncomputable section

open Bundle Metric Module
open scoped Manifold RealInnerProductSpace

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n + 1)]

/-- The gradient of `ρ = 1 - ‖x‖²` on the closed unit ball, for the Euclidean metric, is the
vector `-2x`, read in `E` through the differential of the inclusion. -/
theorem mvfderiv_subtypeVal_mgradient_closedBallDefiningFunction (x : closedBall (0 : E) 1) :
    mvfderiv (𝓡∂ (n + 1)) (Subtype.val : closedBall (0 : E) 1 → E) x
        (Manifold.mgradient (𝓡∂ (n + 1)) closedBallDefiningFunction x) =
      -(2 : ℝ) • (x : E) := by
  set e := subtypeValClosedBallTangentEquiv (n := n + 1) x
  refine ext_inner_right ℝ fun w ↦ ?_
  have h := Manifold.inner_mgradient (I := 𝓡∂ (n + 1)) (f := closedBallDefiningFunction) (x := x)
    (e.symm w)
  rw [inner_tangentSpace_closedBall, mvfderiv_closedBallDefiningFunction_symm_apply,
    mvfderiv_subtypeVal_closedBall, ContinuousLinearEquiv.coe_coe, e.apply_symm_apply] at h
  rw [mvfderiv_subtypeVal_closedBall, ContinuousLinearEquiv.coe_coe]
  rw [h, inner_smul_left]
  simp

/-- The differential of `ρ = 1 - ‖x‖²` on the closed unit ball has norm `2‖x‖` for the
Euclidean metric. -/
@[simp]
theorem norm_mvfderiv_closedBallDefiningFunction (x : closedBall (0 : E) 1) :
    ‖mvfderiv (𝓡∂ (n + 1)) closedBallDefiningFunction x‖ = 2 * ‖(x : E)‖ := by
  rw [← Manifold.norm_mgradient_eq_norm_mvfderiv, norm_tangentSpace_closedBall,
    mvfderiv_subtypeVal_mgradient_closedBallDefiningFunction, norm_smul]
  simp

/-- On the boundary sphere of the closed unit ball, the differential of `ρ = 1 - ‖x‖²` has norm
`|dρ| = 2`. -/
theorem norm_mvfderiv_closedBallDefiningFunction_boundary
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    ‖mvfderiv (𝓡∂ (n + 1)) closedBallDefiningFunction (q : closedBall (0 : E) 1)‖ = 2 := by
  rw [norm_mvfderiv_closedBallDefiningFunction,
    (isBoundaryPoint_closedBall_iff (n := n + 1)).mp q.property, mul_one]

/-- On the boundary sphere of the closed unit ball, `ρ = 1 - ‖x‖²` has gradient
`grad ρ = 2 ν_in`, twice the inward unit normal. -/
theorem mgradient_closedBallDefiningFunction_boundary
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    Manifold.mgradient (𝓡∂ (n + 1)) closedBallDefiningFunction (q : closedBall (0 : E) 1) =
      (2 : ℝ) • inwardUnitNormal q := by
  rw [isBoundaryDefiningFunctionOn_closedBall.mgradient_eq_norm_smul_inwardUnitNormal
    (Set.mem_univ _), norm_mvfderiv_closedBallDefiningFunction_boundary]

end TauCeti
