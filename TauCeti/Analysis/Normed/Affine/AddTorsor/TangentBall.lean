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

end TauCeti
