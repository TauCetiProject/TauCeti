/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import TauCeti.Data.Fin.Tuple.OrderStatistic
public import TauCeti.Probability.Distributions.PoissonBinomial.Count

/-!
# Order statistics of independent, non-identically distributed variables

For independent real coordinates with distribution functions `Fᵢ`, the number of coordinates
at most `t` has Poisson-binomial success probabilities `Fᵢ(t)`. The order statistic at position
`k`, counted from zero, is at most `t` exactly when this count exceeds `k`. Thus its cdf is a
Poisson-binomial tail, equivalently a finite sum over success sets of cardinality greater than
`k`. At the extreme indices `0` and `Fin.last n`, this Poisson-binomial tail collapses to
`1 - ∏ i, (1 - Fᵢ(t))` and `∏ i, Fᵢ(t)`, recovering the sample minimum and maximum formulas.
These formulas retain repeated values and atoms, and allow probabilities zero and one.

## Main results

* `TauCeti.Probability.cdf_map_orderStatistic_pi_eq_poissonBinomial`,
  `TauCeti.Probability.cdf_map_orderStatistic_pi_eq_sum`,
  `TauCeti.Probability.measureReal_setOf_orderStatistic_le_indep` — Poisson-binomial tail and sum
  formulas for general non-iid order statistics;
* `TauCeti.Probability.cdf_map_orderStatistic_zero_pi`,
  `TauCeti.Probability.cdf_map_orderStatistic_last_pi`,
  `TauCeti.Probability.measureReal_setOf_orderStatistic_zero_le_indep`,
  `TauCeti.Probability.measureReal_setOf_orderStatistic_last_le_indep` — closed-form endpoint CDFs
  at `0` and `Fin.last n`, atoms included.

## References

* H. A. David and H. N. Nagaraja, *Order Statistics*, 3rd ed., Wiley, 2003, Chapter 5
  (order statistics from independent non-identically distributed variables).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

namespace TauCeti.Probability

section General

variable {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]

/-- The cdf of an order statistic of independent real coordinates is the tail of the
Poisson-binomial count with success probabilities equal to their cdfs at the threshold.
No continuity or identical-distribution hypothesis is needed. -/
theorem cdf_map_orderStatistic_pi_eq_poissonBinomial (k : Fin n) (t : ℝ) :
    cdf ((Measure.pi μ).map (orderStatistic k)) t =
      (poissonBinomialMeasure fun i ↦ ⟨cdf (μ i) t, cdf_nonneg _ _, cdf_le_one _ _⟩).real
        (Ioi (k : ℕ)) := by
  rw [cdf_eq_real, map_measureReal_apply (measurable_orderStatistic k) measurableSet_Iic,
    preimage_orderStatistic_Iic]
  simpa only [cdf_eq_real, Set.mem_Iic, Set.Ioi] using
    (hasLaw_card_filter_mem_pi μ (fun _ ↦ measurableSet_Iic (a := t))).measureReal_eq
      (p := fun j ↦ (k : ℕ) < j) measurableSet_Ioi

open Classical in
/-- The cdf of an order statistic is the sum of the probabilities of success sets with more
than `k` coordinates at most the threshold. The success-set weights use the individual cdfs. -/
theorem cdf_map_orderStatistic_pi_eq_sum (k : Fin n) (t : ℝ) :
    cdf ((Measure.pi μ).map (orderStatistic k)) t =
      ∑ s : Finset (Fin n) with (k : ℕ) < s.card,
        (poissonBinomialWeight
          (fun i ↦ ⟨cdf (μ i) t, cdf_nonneg _ _, cdf_le_one _ _⟩) s : ℝ) := by
  rw [cdf_map_orderStatistic_pi_eq_poissonBinomial, measureReal_def,
    poissonBinomialMeasure_apply, ENNReal.toReal_sum]
  · simp only [Set.mem_Ioi, ENNReal.coe_toReal]
  · intros
    simp

/-- For an independent family with possibly different laws, the probability that the order
statistic at position `k` is at most `t` is the corresponding Poisson-binomial tail.
Positions are counted from zero, and ties are included. -/
theorem measureReal_setOf_orderStatistic_le_indep
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Fin n → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) (k : Fin n) (t : ℝ) :
    P.real {ω | orderStatistic k (fun i ↦ X i ω) ≤ t} =
      (poissonBinomialMeasure fun i ↦ ⟨cdf (μ i) t, cdf_nonneg _ _, cdf_le_one _ _⟩).real
        (Ioi (k : ℕ)) := by
  rw [← cdf_map_orderStatistic_pi_eq_poissonBinomial, cdf_eq_real,
    map_measureReal_apply (measurable_orderStatistic k) measurableSet_Iic]
  exact (hindep.hasLaw_pi hX).measureReal_eq (measurable_orderStatistic k measurableSet_Iic)

end General

section Endpoints

variable {n : ℕ}

/-- At index `0`, the Poisson-binomial order-statistic cumulative distribution function of
independent (not necessarily identically distributed) real coordinates collapses to
`1 - ∏ i, (1 - cdf (μ i) t)`, recovering the sample minimum formula even for atomic laws. -/
@[simp]
theorem cdf_map_orderStatistic_zero_pi [NeZero n] (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (t : ℝ) :
    cdf ((Measure.pi μ).map (orderStatistic 0)) t = 1 - ∏ i, (1 - cdf (μ i) t) := by
  rw [cdf_map_orderStatistic_pi_eq_poissonBinomial, Fin.val_zero,
    poissonBinomialMeasure_real_Ioi_zero]

/-- At index `Fin.last n`, the Poisson-binomial order-statistic cumulative distribution function of
independent (not necessarily identically distributed) real coordinates collapses to
`∏ i, cdf (μ i) t`, recovering the sample maximum formula even for atomic laws. -/
@[simp]
theorem cdf_map_orderStatistic_last_pi (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (t : ℝ) :
    cdf ((Measure.pi μ).map (orderStatistic (Fin.last n))) t = ∏ i, cdf (μ i) t := by
  simpa [cdf_map_orderStatistic_pi_eq_poissonBinomial] using
    poissonBinomialMeasure_real_Ioi_card_sub_one
      (fun i : Fin (n + 1) ↦ ⟨cdf (μ i) t, cdf_nonneg _ _, cdf_le_one _ _⟩)

/-- For an independent family of real random variables with laws `μ i`, the least order statistic is
at most `t` with probability `1 - ∏ i, (1 - cdf (μ i) t)`. -/
theorem measureReal_setOf_orderStatistic_zero_le_indep {Ω : Type*} {_ : MeasurableSpace Ω}
    [NeZero n] {P : Measure Ω} {μ : Fin n → Measure ℝ} {X : Fin n → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) (t : ℝ) :
    P.real {ω | orderStatistic 0 (fun i ↦ X i ω) ≤ t} = 1 - ∏ i, (1 - cdf (μ i) t) := by
  have := hindep.isProbabilityMeasure
  have _ (i : Fin n) : IsProbabilityMeasure (μ i) := (hX i).isProbabilityMeasure_iff.1 this
  rw [measureReal_setOf_orderStatistic_le_indep μ hindep hX 0 t, Fin.val_zero,
    poissonBinomialMeasure_real_Ioi_zero]

/-- For an independent family of real random variables with laws `μ i`, the greatest order statistic
is at most `t` with probability `∏ i, cdf (μ i) t`. -/
theorem measureReal_setOf_orderStatistic_last_le_indep {Ω : Type*} {_ : MeasurableSpace Ω}
    {P : Measure Ω} {μ : Fin (n + 1) → Measure ℝ} {X : Fin (n + 1) → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) (t : ℝ) :
    P.real {ω | orderStatistic (Fin.last n) (fun i ↦ X i ω) ≤ t} = ∏ i, cdf (μ i) t := by
  have := hindep.isProbabilityMeasure
  have _ (i : Fin (n + 1)) : IsProbabilityMeasure (μ i) := (hX i).isProbabilityMeasure_iff.1 this
  rw [measureReal_setOf_orderStatistic_le_indep μ hindep hX (Fin.last n) t]
  simpa using poissonBinomialMeasure_real_Ioi_card_sub_one
    (fun i : Fin (n + 1) ↦ ⟨cdf (μ i) t, cdf_nonneg _ _, cdf_le_one _ _⟩)

end Endpoints

end TauCeti.Probability
