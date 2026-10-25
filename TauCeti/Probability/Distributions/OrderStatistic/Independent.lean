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
`k`. These formulas retain repeated values and atoms, and allow probabilities zero and one.

## References

* H. A. David and H. N. Nagaraja, *Order Statistics*, 3rd ed., Wiley, 2003, Chapter 5
  (order statistics from independent non-identically distributed variables).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

namespace TauCeti.Probability

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

end TauCeti.Probability
