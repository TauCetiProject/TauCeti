/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Lebesgue integrals of counting functions

For a countable family of measurable predicates `P k` on a measure space, the number of indices
`k` with `P k x` is a function of `x` with values in `ℕ∞`. Its Lebesgue integral is the sum of the
measures of the sets `{x | P k x}`, by exchanging the sum and the integral. For a finite family
of arbitrary sets, Markov's inequality bounds the outer measure of points in more than `k` sets
by the sum of their outer measures divided by `k + 1`.

## Main statements

* `MeasureTheory.lintegral_encard_setOf_eq_tsum`: `∫⁻ x, #{k | P k x} ∂μ = ∑' k, μ {x | P k x}`.
* `MeasureTheory.lintegral_enat_eq_tsum`: `∫⁻ x, (f x : ℝ≥0∞) ∂μ = ∑' k, μ {x | (k : ℕ∞) < f x}`.
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
    ∫⁻ x, (f x : ℝ≥0∞) ∂μ = ∑' k : ℕ, μ {x | (k : ℕ∞) < f x} := by
  have hcount : ∀ x, (f x : ℝ≥0∞) = ({k : ℕ | (k : ℕ∞) < f x}.encard : ℝ≥0∞) := fun x => by
    induction f x using ENat.recTopCoe with
    | top => simp
    | coe n =>
      have hr : {k : ℕ | (k : ℕ∞) < (n : ℕ∞)} = ↑(Finset.range n) := by ext k; simp
      rw [hr, Set.encard_coe_eq_coe_finsetCard, Finset.card_range, ENat.toENNReal_coe]
  simp_rw [hcount]
  exact lintegral_encard_setOf_eq_tsum μ hf

open scoped Classical in
/-- The outer measure of points lying in more than `k` sets of a finite family is at most
the sum of their outer measures divided by `k + 1`. The sets need not be measurable. -/
theorem measure_lt_card_filter_le {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} (s : ι → Set Ω) (k : ℕ) :
    P {ω | k < (Finset.univ.filter fun i ↦ ω ∈ s i).card} ≤
      (∑ i, P (s i)) / (k + 1 : ℝ≥0∞) := by
  classical
  let f (ω : Ω) : ℝ≥0∞ := ∑ i, (toMeasurable P (s i)).indicator (fun _ ↦ 1) ω
  have hi (i : ι) : Measurable ((toMeasurable P (s i)).indicator (fun _ ↦ (1 : ℝ≥0∞))) :=
    measurable_const.indicator (measurableSet_toMeasurable P (s i))
  have hf : Measurable f := Finset.measurable_sum _ fun i _ ↦ hi i
  have hfi : ∫⁻ ω, f ω ∂P = ∑ i, P (s i) := by
    rw [lintegral_finsetSum _ fun i _ ↦ hi i]
    apply Finset.sum_congr rfl
    intro i _
    rw [lintegral_indicator_const (measurableSet_toMeasurable P (s i)), one_mul,
      measure_toMeasurable]
  have hsub : {ω | k < (Finset.univ.filter fun i ↦ ω ∈ s i).card} ⊆
      {ω | (k + 1 : ℝ≥0∞) ≤ f ω} := by
    intro ω hcard
    have hcount : ((Finset.univ.filter fun i ↦ ω ∈ s i).card : ℝ≥0∞) ≤ f ω := by
      dsimp only [f]
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : ω ∈ s i
      · simp [hi, Set.indicator_of_mem (subset_toMeasurable P (s i) hi)]
      · simp [hi]
    have hcard' : (k + 1 : ℝ≥0∞) ≤ (Finset.univ.filter fun i ↦ ω ∈ s i).card := by
      exact_mod_cast Nat.succ_le_of_lt hcard
    exact hcard'.trans hcount
  exact (measure_mono hsub).trans <|
    (meas_ge_le_lintegral_div hf.aemeasurable (by positivity) (by finiteness)).trans_eq
      (by rw [hfi])

end MeasureTheory
