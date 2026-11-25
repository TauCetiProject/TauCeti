/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.OneDimensional.Weighted
import TauCeti.MeasureTheory.Covering.EssentialBoundary.Ball

/-!
# Regression examples: the Gaussian perimeter on the line counts essential boundary points

* `U = (0, 1) ∪ (1, 2)`: the point `1` has density one, so the essential boundary is `{0, 2}` and
  `P_γ(U) = φ(0) + φ(2)`, not `φ(0) + 2φ(1) + φ(2)` (`gaussianPerimeter_Ioo_union_Ioo`).
* `U = ℚ` is null: its essential boundary is empty and `P_γ(U) = 0`, although its frontier is all
  of `ℝ` (`essentialBoundary_rat`, `gaussianPerimeter_rat`).
-/

public section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace TauCeti.Examples.GaussianLine

open TauCeti TauCeti.Real

/-- `(0, 1) ∪ (1, 2)` agrees with `(0, 2)` almost everywhere. -/
theorem Ioo_union_Ioo_ae_eq : (Ioo (0 : ℝ) 1 ∪ Ioo 1 2 : Set ℝ) =ᵐ[volume] Ioo 0 2 := by
  rw [Ioo_union_Ioo_eq_Ioo_sdiff_singleton zero_le_one one_le_two]
  exact sdiff_null_ae_eq_self (measure_singleton 1)

/-- The essential boundary of `(0, 1) ∪ (1, 2)` is `{0, 2}`. -/
theorem essentialBoundary_Ioo_union_Ioo :
    essentialBoundary volume (Ioo (0 : ℝ) 1 ∪ Ioo 1 2) = {0, 2} := by
  have hball : ball (1 : ℝ) 1 = Ioo 0 2 := by
    rw [Real.ball_eq_Ioo]
    norm_num
  rw [essentialBoundary_congr_ae Ioo_union_Ioo_ae_eq, ← hball, essentialBoundary_ball one_ne_zero]
  ext x
  simp only [mem_sphere, Real.dist_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · intro h
    rcases (abs_eq (zero_le_one' ℝ)).1 h with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- **`P_γ((0, 1) ∪ (1, 2)) = φ(0) + φ(2)`.** -/
theorem gaussianPerimeter_Ioo_union_Ioo :
    gaussianPerimeter (Ioo (0 : ℝ) 1 ∪ Ioo 1 2) =
      ENNReal.ofReal (gaussianPDFReal 0 1 0) + ENNReal.ofReal (gaussianPDFReal 0 1 2) := by
  rw [gaussianPerimeter_eq_tsum_essentialBoundary
      (measurableSet_Ioo.union measurableSet_Ioo).nullMeasurableSet,
    essentialBoundary_Ioo_union_Ioo,
    show ({0, 2} : Set ℝ) = ((({0, 2} : Finset ℝ)) : Set ℝ) by simp]
  exact (Finset.tsum_subtype' ({0, 2} : Finset ℝ)
    fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)).trans (Finset.sum_pair (by norm_num))

/-- The rationals have empty essential boundary in `ℝ`. -/
theorem essentialBoundary_rat : essentialBoundary volume (range ((↑) : ℚ → ℝ)) = ∅ := by
  rw [essentialBoundary_congr_ae (ae_eq_empty.2 ((countable_range _).measure_zero volume))]
  exact subset_empty_iff.1 (essentialBoundary_subset_frontier.trans (by simp))

/-- **`P_γ(ℚ) = 0`.** -/
theorem gaussianPerimeter_rat : gaussianPerimeter (range ((↑) : ℚ → ℝ)) = 0 := by
  rw [gaussianPerimeter_congr_ae (ae_eq_empty.2 ((countable_range _).measure_zero volume)),
    gaussianPerimeter_empty]

end TauCeti.Examples.GaussianLine
