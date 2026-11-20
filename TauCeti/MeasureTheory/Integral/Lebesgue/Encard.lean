/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Lebesgue integrals of counting functions

For a countable family of measurable predicates `P k` on a measure space, the number of indices
`k` with `P k x` is a function of `x` with values in `ℕ∞`. Its Lebesgue integral is the sum of the
measures of the sets `{x | P k x}`, by exchanging the sum and the integral. For a countable family
of arbitrary sets, Markov's inequality bounds the outer measure of points in more than `k` sets
by the sum of their outer measures divided by `k + 1`.

## Main statements

* `MeasureTheory.lintegral_encard_setOf_eq_tsum`: `∫⁻ x, #{k | P k x} ∂μ = ∑' k, μ {x | P k x}`.
* `MeasureTheory.measure_lt_encard_setOf_le`: the outer measure of points in more than `k` sets
  of a countable family is at most the sum of their outer measures divided by `k + 1`.
* `MeasureTheory.measure_lt_card_filter_le`: the finite-family version using `Finset.filter`.
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

/-- The outer measure of points lying in more than `k` sets of a countable family is at most
the sum of their outer measures divided by `k + 1`. The sets need not be measurable. -/
theorem measure_lt_encard_setOf_le {ι Ω : Type*} [Countable ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (s : ι → Set Ω) (k : ℕ) :
    μ {ω | (k : ℕ∞) < {i | ω ∈ s i}.encard} ≤
      (∑' i, μ (s i)) / (k + 1 : ℝ≥0∞) := by
  let f (ω : Ω) : ℝ≥0∞ := {i | ω ∈ toMeasurable μ (s i)}.encard
  have hf : Measurable f := (Measurable.of_discrete (f := ENat.toENNReal)).comp <|
    measurable_encard.comp <| Measurable.of_mem fun i ↦
      (measurableSet_toMeasurable μ (s i)).mem
  have hfi : ∫⁻ ω, f ω ∂μ = ∑' i, μ (s i) := by
    simpa only [f, Set.ofPred_mem_eq, measure_toMeasurable] using
      lintegral_encard_setOf_eq_tsum μ
        (P := fun i ω ↦ ω ∈ toMeasurable μ (s i))
        (fun i ↦ measurableSet_toMeasurable μ (s i))
  have hsub : {ω | (k : ℕ∞) < {i | ω ∈ s i}.encard} ⊆
      {ω | (k + 1 : ℝ≥0∞) ≤ f ω} := by
    intro ω hω
    have hcount : {i | ω ∈ s i}.encard ≤ {i | ω ∈ toMeasurable μ (s i)}.encard :=
      Set.encard_mono fun i hi ↦ subset_toMeasurable μ (s i) hi
    have hge := ENat.natCast_add_one_le_iff.mpr (hω.trans_le hcount)
    simpa [f] using ENat.toENNReal_mono hge
  exact (measure_mono hsub).trans <|
    (meas_ge_le_lintegral_div hf.aemeasurable (by positivity) (by finiteness)).trans_eq
      (by rw [hfi])

/-- The outer measure of points lying in more than `k` sets of a finite family is at most
the sum of their outer measures divided by `k + 1`. The sets need not be measurable. -/
theorem measure_lt_card_filter_le {ι Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (I : Finset ι) (s : ι → Set Ω) [∀ ω i, Decidable (ω ∈ s i)] (k : ℕ) :
    P {ω | k < (I.filter fun i ↦ ω ∈ s i).card} ≤
      (∑ i ∈ I, P (s i)) / (k + 1 : ℝ≥0∞) := by
  have hcount (ω : Ω) : {i : I | ω ∈ s i}.encard =
      ((I.filter fun i ↦ ω ∈ s i).card : ℕ∞) := by
    rw [← Subtype.val_injective.encard_image]
    have himage : Subtype.val '' {i : I | ω ∈ s i} = ↑(I.filter fun i ↦ ω ∈ s i) := by
      ext i
      simp [and_comm]
    rw [himage, Set.encard_coe_eq_coe_finsetCard]
  simpa only [hcount, ENat.natCast_lt_natCast, I.tsum_subtype (fun i ↦ P (s i))]
    using measure_lt_encard_setOf_le P (fun i : I ↦ s i) k

end MeasureTheory
