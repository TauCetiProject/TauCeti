/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Distances between midpoints sharing an endpoint

In a normed affine space over a normed field in which `2` is invertible, the midpoints of two
segments with a common endpoint are at distance `‖2‖⁻¹` times the distance between their other
endpoints: the side of the medial triangle joining the midpoints of two sides of a triangle is
half as long as the third side. These sharpen Mathlib's `dist_midpoint_midpoint_le'` when the two
segments share an endpoint.

## Main results

* `dist_midpoint_midpoint_same_left`: `dist (midpoint 𝕜 p₁ p₂) (midpoint 𝕜 p₁ p₃)` is
  `‖2‖⁻¹ * dist p₂ p₃`.
* `dist_midpoint_midpoint_same_right`: `dist (midpoint 𝕜 p₁ p₃) (midpoint 𝕜 p₂ p₃)` is
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
