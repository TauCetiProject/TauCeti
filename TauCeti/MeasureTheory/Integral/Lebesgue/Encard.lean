/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import TauCeti.Topology.Algebra.InfiniteSum.ENNReal
import TauCeti.Data.Set.Card

/-!
# Lebesgue integrals of counting functions

For a countable family of measurable predicates `P k` on a measure space, the number of indices
`k` with `P k x` is a function of `x` with values in `ℕ∞`. Its Lebesgue integral is the sum of the
measures of the sets `{x | P k x}`, by exchanging the sum and the integral.

## Main statements

* `MeasureTheory.lintegral_encard_setOf_eq_tsum`: `∫⁻ x, #{k | P k x} ∂μ = ∑' k, μ {x | P k x}`.
* `MeasureTheory.lintegral_enat_eq_tsum`: `∫⁻ x, (f x : ℝ≥0∞) ∂μ = ∑' k, μ {x | (k : ℕ∞) < f x}`.
* `MeasureTheory.lintegral_enat_le_tsum`: `∫⁻ x, (f x : ℝ≥0∞) ∂μ ≤ ∑' k, μ {x | (k : ℕ∞) < f x}`,
  for arbitrary (not necessarily measurable) `f : β → ℕ∞`.
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

/-- **Tail-sum formula for `ℕ∞`-valued functions.** The Lebesgue integral of an `ℕ∞`-valued
function whose strict superlevel sets are measurable is `∑' k : ℕ, μ {x | (k : ℕ∞) < f x}`. -/
theorem lintegral_enat_eq_tsum {β : Type*} [MeasurableSpace β] (μ : Measure β)
    {f : β → ℕ∞} (hf : ∀ k : ℕ, MeasurableSet {x | (k : ℕ∞) < f x}) :
    ∫⁻ x, (f x : ℝ≥0∞) ∂μ = ∑' k : ℕ, μ {x | (k : ℕ∞) < f x} :=
  (lintegral_congr fun _ => by simp).trans (lintegral_encard_setOf_eq_tsum μ hf)

/-- **Outer-measure tail-sum bound for `ℕ∞`-valued functions.** For any (not necessarily
measurable) `f : β → ℕ∞`, the lower Lebesgue integral of `f` is bounded above by the sum of the
outer measures `μ {x | (k : ℕ∞) < f x}`. -/
theorem lintegral_enat_le_tsum {β : Type*} [MeasurableSpace β] (μ : Measure β) (f : β → ℕ∞) :
    ∫⁻ x, (f x : ℝ≥0∞) ∂μ ≤ ∑' k : ℕ, μ {x | (k : ℕ∞) < f x} := by
  let M : ℕ → Set β := fun k => toMeasurable μ {x | (k : ℕ∞) < f x}
  have hM : ∀ k : ℕ, MeasurableSet {x | x ∈ M k} := fun k => measurableSet_toMeasurable μ _
  calc
    ∫⁻ x, (f x : ℝ≥0∞) ∂μ ≤ ∫⁻ x, ({k : ℕ | x ∈ M k}.encard : ℝ≥0∞) ∂μ :=
      lintegral_mono fun x => by
        rw [← Set.encard_setOf_natCast_lt (f x)]
        exact ENat.toENNReal_mono
          (Set.encard_le_encard fun k hk => subset_toMeasurable μ _ hk)
    _ = ∑' k : ℕ, μ (M k) := lintegral_encard_setOf_eq_tsum μ hM
    _ = ∑' k : ℕ, μ {x | (k : ℕ∞) < f x} :=
      tsum_congr fun k => measure_toMeasurable _

end MeasureTheory
