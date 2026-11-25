/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.ConvexTable
import Mathlib.Analysis.Convex.Segment

/-!
# Convex billiard tables: the stadium and the clockwise circle

Two non-examples for `TauCeti.ConvexTable`.

* The **stadium**, the set of points at distance `1` from the segment `[-1, 1]` of the real axis
  (two half-circles of radius `1` joined by the segments `[-1 + i, 1 + i]` and `[-1 - i, 1 - i]`),
  is a convex `C¹` curve but not the image of any table, of any regularity and period: it
  contains a segment, and the image of a table contains none
  (`TauCeti.ConvexTable.not_segment_subset_range`).
* The **clockwise circle** `s ↦ R exp(-i s / R)`, the counterclockwise circle
  `TauCeti.ConvexTable.circle R` run backwards, is not a table: orientation is part of the carrier
  (`TauCeti.ConvexTable.coe_ne_comp_neg`).
-/

public section

noncomputable section

open Complex Metric Set

namespace TauCeti.Examples.BilliardConvexTable

/-- The stadium: the points of `ℂ` at distance `1` from the segment `[-1, 1]` of the real axis. -/
def stadium : Set ℂ := {z | infDist z (segment ℝ (-1 : ℂ) 1) = 1}

/-- The points of the segment `[-1, 1]` of `ℂ` are real. -/
private theorem im_eq_zero_of_mem_segment {y : ℂ} (hy : y ∈ segment ℝ (-1 : ℂ) 1) : y.im = 0 := by
  obtain ⟨a, b, -, -, -, rfl⟩ := hy
  simp

/-- The upper flat side `[-1 + i, 1 + i]` lies in the stadium. -/
theorem segment_subset_stadium : segment ℝ (-1 + I) (1 + I) ⊆ stadium := by
  rintro z ⟨a, b, ha, hb, hab, rfl⟩
  have hx : ((b - a : ℝ) : ℂ) ∈ segment ℝ (-1 : ℂ) 1 :=
    ⟨a, b, ha, hb, hab, by simp only [real_smul]; push_cast; ring⟩
  have hz : a • (-1 + I) + b • (1 + I) = ((b - a : ℝ) : ℂ) + I := by
    have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
    simp only [real_smul]
    push_cast
    linear_combination I * hab'
  simp only [stadium, mem_ofPred_eq, hz]
  refine le_antisymm ?_ ?_
  · refine (infDist_le_dist_of_mem hx).trans (le_of_eq ?_)
    simp [dist_eq_norm]
  · refine (le_infDist ⟨_, hx⟩).2 fun y hy => ?_
    rw [dist_eq_norm]
    refine le_trans (le_of_eq ?_) (abs_im_le_norm _)
    simp [im_eq_zero_of_mem_segment hy]

/-- **The stadium is not a table.** No convex billiard table, of any regularity and period, has
the stadium as its image: the stadium contains the segment `[-1 + i, 1 + i]`. -/
theorem range_ne_stadium {k : ℕ∞} {ℓ : ℝ} [Fact (0 < ℓ)] (T : ConvexTable k ℓ) :
    range T ≠ stadium := fun h =>
  T.not_segment_subset_range (p := -1 + I) (q := 1 + I) (by norm_num [Complex.ext_iff])
    (h ▸ segment_subset_stadium)

/-- **The clockwise circle is not a table.** For `R > 0`, no table of any regularity is the
counterclockwise circle of radius `R` run backwards, `s ↦ R exp(-i s / R)`. -/
theorem coe_ne_circle_comp_neg (R : ℝ) [Fact (0 < 2 * Real.pi * R)] {j : ℕ∞}
    (T : ConvexTable j (2 * Real.pi * R)) :
    ⇑T ≠ ConvexTable.circle R ∘ Neg.neg :=
  (ConvexTable.circle R).coe_ne_comp_neg T

end TauCeti.Examples.BilliardConvexTable
