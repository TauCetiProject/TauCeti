/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Distances to midpoints

In a normed affine space over a normed field in which `2` is invertible, the midpoints of two
segments with a common endpoint are at distance `‖2‖⁻¹` times the distance between their other
endpoints: the side of the medial triangle joining the midpoints of two sides of a triangle is
half as long as the third side. These sharpen Mathlib's `dist_midpoint_midpoint_le'` when the two
segments share an endpoint. A ball about the midpoint of two points lies in the balls about either
endpoint whose radii are larger by `‖2‖⁻¹` times the distance between the endpoints.

## Main results

* `dist_midpoint_midpoint_same_left`: `dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₁ p₃)` is
  `‖2‖⁻¹ * dist p₂ p₃`.
* `dist_midpoint_midpoint_same_right`: `dist (midpoint 𝕜 p₁ p₃) (midpoint 𝕜 p₂ p₃)` is
  `‖2‖⁻¹ * dist p₁ p₂`.
* `ball_midpoint_subset_ball_left`, `ball_midpoint_subset_ball_right`: a ball about
  `midpoint 𝕜 p₁ p₂` lies in the ball about `p₁`, respectively `p₂`, of radius larger by
  `‖2‖⁻¹ * dist p₁ p₂`.
-/

public section

variable {𝕜 V P : Type*} [NormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
  [PseudoMetricSpace P] [NormedAddTorsor V P] [Invertible (2 : 𝕜)]

/-- The midpoints of two segments starting at the same point are at distance `‖2‖⁻¹` times the
distance between their other endpoints. -/
theorem dist_midpoint_midpoint_same_left (p₁ p₂ p₃ : P) :
    dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₁ p₃) = ‖(2 : 𝕜)‖⁻¹ * dist p₂ p₃ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, midpoint_vsub_midpoint_same_left, norm_smul,
    invOf_eq_inv, norm_inv]

/-- The midpoints of two segments ending at the same point are at distance `‖2‖⁻¹` times the
distance between their other endpoints. -/
theorem dist_midpoint_midpoint_same_right (p₁ p₂ p₃ : P) :
    dist (midpoint 𝕜 p₁ p₃) (midpoint 𝕜 p₂ p₃) = ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, midpoint_vsub_midpoint_same_right, norm_smul,
    invOf_eq_inv, norm_inv]

/-- A ball about the midpoint of `p₁` and `p₂` lies in the ball about `p₁` whose radius is larger
by `‖2‖⁻¹` times the distance between `p₁` and `p₂`. -/
theorem ball_midpoint_subset_ball_left (p₁ p₂ : P) (r : ℝ) :
    Metric.ball (midpoint 𝕜 p₁ p₂) r ⊆ Metric.ball p₁ (r + ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂) := by
  refine Metric.ball_subset_ball' ?_
  rw [dist_midpoint_left]

/-- A ball about the midpoint of `p₁` and `p₂` lies in the ball about `p₂` whose radius is larger
by `‖2‖⁻¹` times the distance between `p₁` and `p₂`. -/
theorem ball_midpoint_subset_ball_right (p₁ p₂ : P) (r : ℝ) :
    Metric.ball (midpoint 𝕜 p₁ p₂) r ⊆ Metric.ball p₂ (r + ‖(2 : 𝕜)‖⁻¹ * dist p₁ p₂) := by
  refine Metric.ball_subset_ball' ?_
  rw [dist_midpoint_right]
