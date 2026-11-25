/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Tangent subballs

A ball tangent at a prescribed point of a sphere can be shrunk into any neighborhood of that
point, keeping its center on the original radius and its interior inside the original ball.

For `x` on `sphere c r`, the ball of radius `δ` about the point at distance `δ` from `x` on the
line through `x` and `c` lies in `ball x (2 * δ)`, and inside `ball c r` (moving towards `c`,
`δ ≤ r`) or outside it (moving away from `c`).

## Main results

* `TauCeti.exists_tangent_subball`: arbitrarily small tangent subballs at a point of a sphere.
* `TauCeti.ball_lineMap_subset_ball_inter_ball`: the ball of radius `δ` about
  `lineMap x c (δ / r)` lies in `ball c r ∩ ball x (2 * δ)`.
* `TauCeti.ball_lineMap_neg_subset_compl_ball_inter_ball`: the ball of radius `δ` about
  `lineMap x c (-(δ / r))` lies in `(ball c r)ᶜ ∩ ball x (2 * δ)`.
-/

public section

namespace TauCeti

open Metric

/-- A ball has arbitrarily small tangent subballs at each point of its sphere. The smaller
center is obtained by moving from the contact point toward the original center. -/
theorem exists_tangent_subball {V P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [PseudoMetricSpace P] [NormedAddTorsor V P]
    {x₀ y : P} {R ε : ℝ} (hR : 0 < R) (hx₀ : x₀ ∈ sphere y R) (hε : 0 < ε) :
    ∃ r > 0, ∃ p, p = AffineMap.lineMap x₀ y (r / R) ∧
      x₀ ∈ sphere p r ∧ ball p r ⊆ ball y R ∧ ball p r ⊆ ball x₀ ε := by
  let r := min R (ε / 2)
  have hr : 0 < r := lt_min hR (half_pos hε)
  have ht : r / R ≤ 1 := (div_le_one hR).2 (min_le_left _ _)
  let p := AffineMap.lineMap x₀ y (r / R)
  have hx : dist x₀ p = r := by
    simp only [p, dist_left_lineMap, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hr.le hR.le), mem_sphere.mp hx₀]
    field_simp
  have hy : dist p y = R - r := by
    simp only [p, dist_lineMap_right, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht), mem_sphere.mp hx₀]
    field_simp
  refine ⟨r, hr, p, rfl, mem_sphere.mpr hx, ball_subset_ball' ?_, ball_subset_ball' ?_⟩
  · rw [hy]
    linarith
  · rw [dist_comm, hx]
    have hrε : r ≤ ε / 2 := min_le_right _ _
    linarith

section Segment

variable {V P : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V] [PseudoMetricSpace P]
  [NormedAddTorsor V P] {x c : P} {r δ : ℝ}

/-- For `x` on `sphere c r` and `δ ≤ r`, the ball of radius `δ` about the point at distance `δ`
from `x` towards `c` lies inside both `ball c r` and `ball x (2 * δ)`. -/
theorem ball_lineMap_subset_ball_inter_ball (hx : dist x c = r) (hδr : δ ≤ r) :
    ball (AffineMap.lineMap x c (δ / r)) δ ⊆ ball c r ∩ ball x (2 * δ) := by
  rcases le_or_gt δ 0 with hδ | hδ
  · simp [ball_eq_empty.2 hδ]
  have hr : 0 < r := hδ.trans_le hδr
  have hyx : dist (AffineMap.lineMap x c (δ / r)) x = δ := by
    simp [dist_lineMap_left, hx, abs_of_pos hδ, abs_of_pos hr, hr.ne']
  have hyc : dist (AffineMap.lineMap x c (δ / r)) c = r - δ := by
    rw [dist_lineMap_right, hx, Real.norm_of_nonneg (sub_nonneg.2 ((div_le_one hr).2 hδr))]
    field_simp
  exact Set.subset_inter (ball_subset_ball' (by linarith)) (ball_subset_ball' (by linarith))

/-- For `x` on `sphere c r`, `r > 0`, the ball of radius `δ` about the point at distance `δ` from
`x` away from `c` lies outside `ball c r` and inside `ball x (2 * δ)`. -/
theorem ball_lineMap_neg_subset_compl_ball_inter_ball (hx : dist x c = r) (hr : 0 < r) :
    ball (AffineMap.lineMap x c (-(δ / r))) δ ⊆ (ball c r)ᶜ ∩ ball x (2 * δ) := by
  rcases le_or_gt δ 0 with hδ | hδ
  · simp [ball_eq_empty.2 hδ]
  have hyx : dist (AffineMap.lineMap x c (-(δ / r))) x = δ := by
    simp [dist_lineMap_left, hx, abs_of_pos hδ, abs_of_pos hr, hr.ne']
  have hyc : dist (AffineMap.lineMap x c (-(δ / r))) c = r + δ := by
    rw [dist_lineMap_right, hx, sub_neg_eq_add, Real.norm_of_nonneg (by positivity)]
    field_simp
  exact Set.subset_inter (Set.subset_compl_iff_disjoint_right.2 (ball_disjoint_ball (by linarith)))
    (ball_subset_ball' (by linarith))

end Segment

end TauCeti
