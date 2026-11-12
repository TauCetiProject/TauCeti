/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Distances between midpoints, and homotheties of balls

In a normed affine space over a normed field in which `2` is invertible, the midpoints of two
segments with a common endpoint are at distance `‖2‖⁻¹` times the distance between their other
endpoints: the side of the medial triangle joining the midpoints of two sides of a triangle is
half as long as the third side. These sharpen Mathlib's `dist_midpoint_midpoint_le'` when the two
segments share an endpoint.

A homothety about `c` scales distances to `c` by the norm of its ratio, so a homothety whose ratio
has norm at most `1` maps every ball and closed ball centred at `c` into itself.

## Main results

* `dist_midpoint_midpoint_same_left`: `dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₁ p₃)` is
  `‖2‖⁻¹ * dist p₂ p₃`.
* `dist_midpoint_midpoint_same_right`: `dist (midpoint 𝕜 p₁ p₃) (midpoint 𝕜 p₂ p₃)` is
  `‖2‖⁻¹ * dist p₁ p₂`.
* `dist_homothety_center_of_nonneg`: a homothety of ratio `s ≥ 0` about `c` scales the distance to
  `c` by `s`.
* `Metric.mapsTo_homothety_ball`, `Metric.mapsTo_homothety_closedBall`: a homothety whose ratio has
  norm at most `1` maps a ball or closed ball about its centre into itself.
-/

public section

section Midpoint

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

end Midpoint

section Homothety

variable {𝕜 V P : Type*} [NormedField 𝕜] [SeminormedAddCommGroup V] [PseudoMetricSpace P]
  [NormedAddTorsor V P]

/-- A homothety of ratio `s ≥ 0` about `c` scales the distance to `c` by `s`. -/
theorem dist_homothety_center_of_nonneg [NormedSpace ℝ V] (c x : P) {s : ℝ} (hs : 0 ≤ s) :
    dist (AffineMap.homothety c s x) c = s * dist x c := by
  rw [dist_homothety_center, Real.norm_of_nonneg hs, dist_comm]

variable [NormedSpace 𝕜 V]

/-- A homothety whose ratio has norm at most `1` maps a ball about its centre into itself. -/
theorem Metric.mapsTo_homothety_ball (c : P) {s : 𝕜} (hs : ‖s‖ ≤ 1) (R : ℝ) :
    Set.MapsTo (AffineMap.homothety c s) (ball c R) (ball c R) := fun x hx ↦ by
  rw [mem_ball, dist_homothety_center, dist_comm]
  exact (mul_le_of_le_one_left dist_nonneg hs).trans_lt hx

/-- A homothety whose ratio has norm at most `1` maps a closed ball about its centre into itself. -/
theorem Metric.mapsTo_homothety_closedBall (c : P) {s : 𝕜} (hs : ‖s‖ ≤ 1) (R : ℝ) :
    Set.MapsTo (AffineMap.homothety c s) (closedBall c R) (closedBall c R) := fun x hx ↦ by
  rw [mem_closedBall, dist_homothety_center, dist_comm]
  exact (mul_le_of_le_one_left dist_nonneg hs).trans hx

end Homothety
