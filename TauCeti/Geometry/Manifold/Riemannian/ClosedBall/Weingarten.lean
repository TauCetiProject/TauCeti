/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.SecondFundamentalForm
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Weingarten

/-!
# The Weingarten map of the unit sphere bounding the closed unit ball

For the Euclidean metric on the closed unit ball of a real inner product space `E` of dimension
`n + 1`, the second fundamental form of the boundary sphere is the induced metric
(`TauCeti.boundarySecondFundamentalForm_closedBall`). Hence the Weingarten map is the identity
(`TauCeti.boundaryWeingarten_closedBall`), every principal curvature is `1`
(`TauCeti.boundaryPrincipalCurvatures_closedBall`) and, for `n ≥ 1`, the mean curvature is `1`
(`TauCeti.boundaryMeanCurvature_closedBall`).
-/

public section

open Metric Module
open scoped Manifold

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n + 1)]

/-- The second fundamental form of the unit sphere bounding the closed unit ball is the induced
metric: `II = h`. -/
theorem boundarySecondFundamentalForm_closedBall_eq_boundaryInducedForm
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    boundarySecondFundamentalForm q = boundaryInducedForm q := by
  ext u w
  rw [boundarySecondFundamentalForm_closedBall, boundaryInducedForm_apply]

/-- **The Weingarten map of the unit sphere is the identity**: `S_q = id` at every point of the
boundary of the closed unit ball. -/
theorem boundaryWeingarten_closedBall (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    boundaryWeingarten q = LinearMap.id := by
  refine ((eq_boundaryWeingarten_iff q LinearMap.id).2 fun u w ↦ ?_).symm
  rw [LinearMap.id_apply, boundarySecondFundamentalForm_closedBall_eq_boundaryInducedForm]

/-- **Every principal curvature of the unit sphere is `1`.** -/
theorem boundaryPrincipalCurvatures_closedBall
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) (i : Fin n) :
    boundaryPrincipalCurvatures q i = 1 := by
  have h := boundaryWeingarten_boundaryPrincipalDirection q i
  rw [boundaryWeingarten_closedBall, LinearMap.id_apply] at h
  exact smul_left_injective ℝ (boundaryPrincipalDirection_ne_zero q i)
    (h.symm.trans (one_smul ℝ _).symm)

/-- **The mean curvature of the unit sphere is `1`**, for `n ≥ 1`. -/
theorem boundaryMeanCurvature_closedBall [NeZero n]
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    boundaryMeanCurvature q = 1 := by
  rw [boundaryMeanCurvature_eq_sum_div]
  simp [boundaryPrincipalCurvatures_closedBall, NeZero.ne n]

end TauCeti
