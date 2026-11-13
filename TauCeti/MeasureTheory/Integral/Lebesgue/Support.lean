/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Positive integrals and non-concentration on zero sets

For a zero or probability measure, a function with positive lower Lebesgue integral
has a zero set of mass strictly less than one. In particular, no zero of the function
can carry all the mass. No measurability assumption on the function is needed.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsZeroOrProbabilityMeasure μ]

/-- A function with positive lower Lebesgue integral has a zero set of mass less than one. -/
theorem measure_compl_support_lt_one_of_lintegral_pos {f : α → ℝ≥0∞}
    (h : 0 < ∫⁻ u, f u ∂μ) : μ (Function.support f)ᶜ < 1 := by
  obtain ⟨g, hg, hgf, hfg⟩ := exists_measurable_le_lintegral_eq μ f
  have hpos := (lintegral_pos_iff_support hg).1 (hfg ▸ h)
  refine lt_of_le_of_lt (measure_mono ?_) (by
    simpa using prob_compl_lt_one_sub_of_lt_prob hpos (measurableSet_support hg))
  intro x hx
  simp only [Set.mem_compl_iff, Function.mem_support, not_not] at hx ⊢
  exact le_antisymm ((hgf x).trans_eq hx) bot_le

/-- A zero of a function with positive lower Lebesgue integral has mass less than one. -/
theorem measure_singleton_lt_one_of_lintegral_pos {f : α → ℝ≥0∞} {a : α}
    (ha : f a = 0) (h : 0 < ∫⁻ u, f u ∂μ) : μ {a} < 1 := by
  refine lt_of_le_of_lt (measure_mono ?_) (μ.measure_compl_support_lt_one_of_lintegral_pos h)
  simpa [Function.support] using ha

end MeasureTheory.Measure
