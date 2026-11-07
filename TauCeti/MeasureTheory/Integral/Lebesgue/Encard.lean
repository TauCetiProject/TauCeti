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
* `MeasureTheory.lintegral_enat_eq_tsum`: `∫⁻ x, (f x : ℝ≥0∞) ∂μ = ∑' k, μ {x | (k : ℕ∞) < f x}`.
* `MeasureTheory.lintegral_withTop_nat_eq_tsum`: the corresponding tail-sum formula for
  `WithTop ℕ`-valued functions.
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

/-- **Tail-sum formula for `WithTop ℕ`-valued functions.** The Lebesgue integral of a
`WithTop ℕ`-valued function, mapping `⊤` to `∞` and `n : ℕ` to `(n : ℝ≥0∞)`, is
`∑' k : ℕ, μ {x | (k : WithTop ℕ) < f x}` whenever those strict superlevel sets are measurable. -/
theorem lintegral_withTop_nat_eq_tsum {β : Type*} [MeasurableSpace β] (μ : Measure β)
    {f : β → WithTop ℕ} (hf : ∀ k : ℕ, MeasurableSet {x | (k : WithTop ℕ) < f x}) :
    ∫⁻ x, (f x).recTopCoe ⊤ Nat.cast ∂μ = ∑' k : ℕ, μ {x | (k : WithTop ℕ) < f x} := by
  have hcount : ∀ x, (f x).recTopCoe ⊤ Nat.cast =
      ({k : ℕ | (k : WithTop ℕ) < f x}.encard : ℝ≥0∞) := fun x => by
    induction f x using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      have hr : {k : ℕ | (k : WithTop ℕ) < WithTop.some n} = ↑(Finset.range n) := by
        ext k
        exact WithTop.coe_lt_coe.trans Finset.mem_range.symm
      rw [WithTop.recTopCoe_coe, hr, Set.encard_coe_eq_coe_finsetCard, Finset.card_range,
        ENat.toENNReal_coe]
  simp_rw [hcount]
  exact lintegral_encard_setOf_eq_tsum μ hf

end MeasureTheory
