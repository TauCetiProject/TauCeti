/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.PolarGraph.Basic

/-!
# Examples of polar graph separation

A height linear in the unrestricted polar angle separates every pair of distinct deck sheets
exactly when its slope is nonzero. At zero slope, distinct deck sheets collapse, as in the
constant-height non-injectivity theorem on the full polar cover in the basic API.

For the open angular sector `0 < θ < 3π`, the one-turn deck overlap is precisely `0 < θ < π`.
This illustrates how a domain limits the sheet comparisons available for a multi-valued graph.

## References

* T. H. Colding and W. P. Minicozzi II, *The space of embedded minimal surfaces of fixed
  genus in a 3-manifold IV*, Section 0.
-/

public noncomputable section

namespace TauCeti.PolarGraph

/-- Height with constant angular slope; its graph is the elementary helicoidal model. -/
def linearHeight (c : ℝ) (p : PolarPoint) : ℝ := c * angle p

@[simp, grind =] theorem linearHeight_apply (c : ℝ) (p : PolarPoint) :
    linearHeight c p = c * angle p := (rfl)

@[simp, grind =] theorem separation_linearHeight (c : ℝ) (k : ℤ) (p : PolarPoint) :
    separation (linearHeight c) k p = c * ((k : ℝ) * (2 * Real.pi)) := by
  simp only [separation_def, linearHeight_apply, angle_deckShift]
  ring

/-- A linear angular height separates all sheets exactly when its slope is nonzero. -/
theorem graph_linearHeight_injective_iff {c : ℝ} :
    Function.Injective (graph (linearHeight c)) ↔ c ≠ 0 := by
  constructor
  · intro h hc
    subst c
    have hzero : linearHeight 0 = fun _ ↦ (0 : ℝ) := by
      funext p
      simp
    rw [hzero] at h
    exact not_injective_graph_const 0 h
  · intro hc
    rw [← Set.injOn_univ, graph_injOn_iff]
    intro k hk p _
    rw [separation_linearHeight]
    exact mul_ne_zero hc (mul_ne_zero (by exact_mod_cast hk)
      (mul_ne_zero (by norm_num) Real.pi_ne_zero))

/-- The one-turn overlap of the open sector `0 < θ < 3π` is the sector `0 < θ < π`. -/
@[grind =] theorem mem_overlap_sector_zero_three_pi_one_iff (p : PolarPoint) :
    p ∈ overlap (sector 0 (3 * Real.pi)) 1 ↔ 0 < angle p ∧ angle p < Real.pi := by
  rw [overlap_sector_of_nonneg (by norm_num : (0 : ℤ) ≤ 1)]
  have h : 3 * Real.pi - (1 : ℤ) * (2 * Real.pi) = Real.pi := by norm_num; ring
  rw [h, mem_sector_iff]

end TauCeti.PolarGraph
