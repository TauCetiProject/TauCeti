/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.SecondFundamentalForm
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.Weingarten.Basic

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

/-- **The Weingarten map of the unit sphere is the identity**: `S_q = id` at every point of the
boundary of the closed unit ball. -/
@[simp]
theorem boundaryWeingarten_closedBall (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    boundaryWeingarten q = LinearMap.id := by
  rw [← one_smul ℝ (LinearMap.id : Module.End ℝ _), boundaryWeingarten_eq_smul_id_iff, one_smul]
  exact boundarySecondFundamentalForm_closedBall_eq_boundaryInducedForm q

/-- **Every principal curvature of the unit sphere is `1`.** -/
@[simp]
theorem boundaryPrincipalCurvatures_closedBall
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) (i : Fin n) :
    boundaryPrincipalCurvatures q i = 1 :=
  boundaryPrincipalCurvatures_eq_of_boundaryWeingarten_eq_smul
    (by rw [boundaryWeingarten_closedBall, one_smul]) i

/-- **The mean curvature of the unit sphere is `1`**, for `n ≥ 1`. -/
@[simp]
theorem boundaryMeanCurvature_closedBall [NeZero n]
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    boundaryMeanCurvature q = 1 :=
  boundaryMeanCurvature_eq_of_boundaryWeingarten_eq_smul
    (by rw [boundaryWeingarten_closedBall, one_smul])

end TauCeti
