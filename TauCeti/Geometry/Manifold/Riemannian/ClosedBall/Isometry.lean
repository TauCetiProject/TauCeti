/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Local

/-!
# The inclusion of the closed unit ball is a local Riemannian isometry

The inclusion of the closed unit ball of a real inner product space `E` of dimension `n`, with its
Euclidean metric `TauCeti.closedBallEuclideanMetric`, into `E` with its flat metric is a local
Riemannian isometry: it is analytic, its differential is invertible at every point, including the
points of the boundary sphere, and the metric of the ball is induced by it.

## Main statements

* `TauCeti.isLocalRiemannianIsometry_subtypeVal_closedBall`: the inclusion of the closed unit
  ball into `E` is a local Riemannian isometry.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (induced metrics on submanifolds).
-/

public section

open Metric Module TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n)]

/-- The inclusion of the closed unit ball, with its Euclidean metric, into `E`, with its flat
metric, is a local Riemannian isometry. -/
theorem isLocalRiemannianIsometry_subtypeVal_closedBall :
    IsLocalRiemannianIsometry (𝓡∂ n) 𝓘(ℝ, E) (Subtype.val : closedBall (0 : E) 1 → E) where
  contMDiff := contMDiff_subtypeVal_closedBall.of_le le_top
  isInvertible_mfderiv x :=
    ⟨(subtypeValClosedBallTangentEquiv (n := n) x).trans
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (x : E)).symm, by
      ext v
      have h := ContinuousLinearMap.ext_iff.1
        (subtypeValClosedBallTangentEquiv_toContinuousLinearMap (n := n) x) v
      simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coe_comp,
        Function.comp_apply] at h
      simp [h]⟩
  inner_mfderiv x v w := by
    rw [inner_tangentSpace_closedBall]
    exact inner_mfderiv_eq_inner_mvfderiv _ _ _ _

end TauCeti
