/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Lebesgue integrals of counting functions

For a countable family of measurable predicates `P k` on a measure space, the number of indices
`k` with `P k x` is a function of `x` with values in `ℕ∞`. Its Lebesgue integral is the sum of the
measures of the sets `{x | P k x}`, by exchanging the sum and the integral.

## Main statements

* `MeasureTheory.lintegral_encard_setOf_eq_tsum`: `∫⁻ x, #{k | P k x} ∂μ = ∑' k, μ {x | P k x}`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

/-- The mean number of indices `k` with `P k x` is `∑' k, μ {x | P k x}`. -/
theorem lintegral_encard_setOf_eq_tsum {ι β : Type*} [Countable ι] [MeasurableSpace β]
    (μ : Measure β) {P : ι → β → Prop} (hP : ∀ k, MeasurableSet {x | P k x}) :
    ∫⁻ x, ({k | P k x}.encard : ℝ≥0∞) ∂μ = ∑' k, μ {x | P k x} := by
  have hcount : ∀ x, ({k | P k x}.encard : ℝ≥0∞) = ∑' k, {x | P k x}.indicator (fun _ => 1) x :=
    fun x => by
    rw [← ENNReal.tsum_indicator_one]
    exact tsum_congr fun k => by simp only [Set.indicator, Set.mem_ofPred_eq]
  simp_rw [hcount]
  rw [lintegral_tsum fun k => (measurable_const.indicator (hP k)).aemeasurable]
  simp_rw [lintegral_indicator_const (hP _), one_mul]

end MeasureTheory
