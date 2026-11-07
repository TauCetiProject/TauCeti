/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Convex.Between

/-!
# Rays from a point of a seminormed affine space

The ray from a point `z` of a real seminormed affine space along a vector `d` is the set of
points `t • d +ᵥ z` with `0 ≤ t`. Within the closed ball about `z` of radius `dist c z`, the
segment from `z` to `c` agrees with the ray through `c`, provided this radius is positive. No
separation of the seminorm or pseudometric is needed.

## Main results

* `TauCeti.mem_affineSegment_iff_of_dist_le`: if `0 < dist c z` and `dist y z ≤ dist c z`, then
  `y` lies on the segment from `z` to `c` iff it lies on the ray from `z` through `c`.
-/

public section

open Set

namespace TauCeti

variable {V P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] [PseudoMetricSpace P]
  [NormedAddTorsor V P]

/-- Within the closed ball about `z` of radius `dist c z`, the segment from `z` to `c` is the
ray from `z` through `c`, provided `0 < dist c z`. Positivity matters only for seminorms: it rules
out a nonzero `c -ᵥ z` of norm zero, whose whole ray lies at distance `0` from `z`. -/
theorem mem_affineSegment_iff_of_dist_le {c y z : P} (hc : 0 < dist c z)
    (hy : dist y z ≤ dist c z) :
    y ∈ affineSegment ℝ z c ↔ ∃ t : ℝ, 0 ≤ t ∧ y = t • (c -ᵥ z) +ᵥ z := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht.1, AffineMap.lineMap_apply _ _ _⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ⟨ht, ?_⟩, AffineMap.lineMap_apply _ _ _⟩
    rw [dist_vadd_left, norm_smul, Real.norm_of_nonneg ht, dist_eq_norm_vsub V] at hy
    rw [dist_eq_norm_vsub V] at hc
    exact (mul_le_iff_le_one_left hc).1 hy

end TauCeti
