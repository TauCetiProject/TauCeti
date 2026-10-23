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
points `t • d +ᵥ z` with `0 ≤ t`. Within distance `‖c -ᵥ z‖` of `z`, the segment from `z` to
`c` agrees with the ray through `c`. No separation of the seminorm or pseudometric is needed.

## Main results

* `TauCeti.mem_affineSegment_iff_of_dist_lt`: within distance `‖c -ᵥ z‖` of `z`, the segment from
  `z` to `c` is the ray from `z` through `c`.
-/

public section

open Set

namespace TauCeti

variable {V P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] [PseudoMetricSpace P]
  [NormedAddTorsor V P]

/-- Within distance `‖c -ᵥ z‖` of `z`, the segment from `z` to `c` is the ray from `z` through
`c`. -/
theorem mem_affineSegment_iff_of_dist_lt {c y z : P} (hy : dist y z < ‖c -ᵥ z‖) :
    y ∈ affineSegment ℝ z c ↔ ∃ t : ℝ, 0 ≤ t ∧ y = t • (c -ᵥ z) +ᵥ z := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht.1, AffineMap.lineMap_apply _ _ _⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ⟨ht, ?_⟩, AffineMap.lineMap_apply _ _ _⟩
    rw [dist_vadd_left, norm_smul, Real.norm_of_nonneg ht] at hy
    exact (lt_of_mul_lt_mul_right (hy.trans_eq (one_mul _).symm) (norm_nonneg _)).le

end TauCeti
