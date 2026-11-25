/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Lower integrals of functions controlled on their support

This file collects lower Lebesgue integral facts about a function in terms of its support.

## Positive integrals and non-concentration on zero sets

For a zero or probability measure, a function with positive lower Lebesgue integral
has a zero set of mass strictly less than one. In particular, no zero of the function
can carry all the mass. No measurability assumption on the function is needed.

## Norm-bounded functions supported in a set

A function supported in a measurable set `s` and bounded in norm by `ε` has lower integral of its
norm at most `ε μ(s)` (`MeasureTheory.lintegral_enorm_le_ofReal_mul_measure`).
-/

public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsZeroOrProbabilityMeasure μ]

/-- For a zero or probability measure, a function with positive lower Lebesgue integral
has a zero set of mass less than one. -/
theorem measure_compl_support_lt_one_of_lintegral_pos {f : α → ℝ≥0∞}
    (h : 0 < ∫⁻ u, f u ∂μ) : μ (Function.support f)ᶜ < 1 := by
  obtain ⟨g, hg, hgf, hfg⟩ := exists_measurable_le_lintegral_eq μ f
  have hpos := (lintegral_pos_iff_support hg).1 (hfg ▸ h)
  refine lt_of_le_of_lt (measure_mono ?_) (by
    simpa using prob_compl_lt_one_sub_of_lt_prob hpos (measurableSet_support hg))
  intro x hx
  simp only [Set.mem_compl_iff, Function.mem_support, not_not] at hx ⊢
  exact le_antisymm ((hgf x).trans_eq hx) bot_le

/-- For a zero or probability measure, a zero of a function with positive lower Lebesgue integral
has mass less than one. -/
theorem measure_singleton_lt_one_of_lintegral_pos {f : α → ℝ≥0∞} {a : α}
    (ha : f a = 0) (h : 0 < ∫⁻ u, f u ∂μ) : μ {a} < 1 := by
  refine lt_of_le_of_lt (measure_mono ?_) (μ.measure_compl_support_lt_one_of_lintegral_pos h)
  simpa [Function.support] using ha

end MeasureTheory.Measure

namespace MeasureTheory

/-- A function supported in a measurable set `s` and bounded in norm by `ε` has
`∫⁻ ‖f‖ₑ ∂μ ≤ ε μ(s)`. -/
theorem lintegral_enorm_le_ofReal_mul_measure {α G : Type*} [MeasurableSpace α]
    [NormedAddCommGroup G] (μ : Measure α) {f : α → G} {s : Set α} (hs : MeasurableSet s)
    (hfs : Function.support f ⊆ s) {ε : ℝ} (hf : ∀ x, ‖f x‖ ≤ ε) :
    ∫⁻ x, ‖f x‖ₑ ∂μ ≤ ENNReal.ofReal ε * μ s := by
  rw [← lintegral_indicator_const hs]
  refine lintegral_mono fun x => ?_
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hf x)
  · rw [Function.notMem_support.1 fun h => hx (hfs h), ← ofReal_norm, norm_zero,
      ENNReal.ofReal_zero]
    exact zero_le

end MeasureTheory
