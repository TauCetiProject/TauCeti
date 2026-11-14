/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import TauCeti.Data.Fin.Tuple.OrderStatistic
public import TauCeti.Probability.Distributions.PoissonBinomial.Count
import TauCeti.Probability.Independence.Lattice

/-!
# Order statistics of independent, non-identically distributed variables

For any linear order, pushing a tuple measure forward along `orderStatistic 0` or
`orderStatistic (Fin.last n)` coincides with pushing it forward along the coordinatewise minimum or
maximum, and for independent coordinates in a measurable semilattice the extreme order statistics
have those product-pushforward laws.

For independent real coordinates with distribution functions `Fᵢ`, the number of coordinates
at most `t` has Poisson-binomial success probabilities `Fᵢ(t)`. The order statistic at position
`k`, counted from zero, is at most `t` exactly when this count exceeds `k`. Thus its cdf is a
Poisson-binomial tail, equivalently a finite sum over success sets of cardinality greater than
`k`. At the extreme indices `0` and `Fin.last n`, this Poisson-binomial tail collapses to
`1 - ∏ i, (1 - Fᵢ(t))` and `∏ i, Fᵢ(t)`, recovering the sample minimum and maximum formulas.
These formulas retain repeated values and atoms, and allow probabilities zero and one.

## Main results

* `TauCeti.Probability.map_orderStatistic_zero`, `TauCeti.Probability.map_orderStatistic_last`,
  `TauCeti.Probability.hasLaw_orderStatistic_zero_indep`,
  `TauCeti.Probability.hasLaw_orderStatistic_last_indep` — pushforward and `HasLaw` bridges between
  `orderStatistic 0` / `orderStatistic (Fin.last n)` and finite sample minima / maxima;
* `TauCeti.Probability.cdf_map_orderStatistic_pi_eq_poissonBinomial`,
  `TauCeti.Probability.cdf_map_orderStatistic_pi_eq_sum`,
  `TauCeti.Probability.measureReal_setOf_orderStatistic_le_indep` — Poisson-binomial tail and sum
  formulas for general non-iid order statistics;
* `TauCeti.Probability.cdf_map_orderStatistic_zero_pi`,
  `TauCeti.Probability.cdf_map_orderStatistic_last_pi` — closed-form endpoint product-measure CDFs
  at `0` and `Fin.last n`, atoms included.

## References

* H. A. David and H. N. Nagaraja, *Order Statistics*, 3rd ed., Wiley, 2003, Chapter 5
  (order statistics from independent non-identically distributed variables).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

namespace TauCeti.Probability

section LinearOrder

variable {α : Type*} [LinearOrder α] [MeasurableSpace α] {n : ℕ}

/-- Pushing any tuple measure forward along `orderStatistic 0` coincides with pushing it forward
along the tuple minimum. No measurability assumption on the order operations is needed because the
two maps are pointwise equal. -/
theorem map_orderStatistic_zero [NeZero n] (ρ : Measure (Fin n → α)) :
    ρ.map (orderStatistic 0) = ρ.map (fun x ↦ Finset.univ.inf' Finset.univ_nonempty x) :=
  congrArg ρ.map (funext orderStatistic_zero)

/-- Pushing any tuple measure forward along `orderStatistic (Fin.last n)` coincides with pushing it
forward along the tuple maximum. -/
theorem map_orderStatistic_last (ρ : Measure (Fin (n + 1) → α)) :
    ρ.map (orderStatistic (Fin.last n)) =
      ρ.map (fun x ↦ Finset.univ.sup' Finset.univ_nonempty x) :=
  congrArg ρ.map (funext orderStatistic_last)

/-- The least order statistic of independent coordinates has the pushforward of the product measure
along `orderStatistic 0`. Only `MeasurableInf₂ α` is needed because `orderStatistic 0` is the
sample minimum. -/
theorem hasLaw_orderStatistic_zero_indep {Ω : Type*} {_ : MeasurableSpace Ω} [MeasurableInf₂ α]
    [NeZero n] {P : Measure Ω} {μ : Fin n → Measure α} {X : Fin n → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω ↦ orderStatistic 0 fun i ↦ X i ω)
      ((Measure.pi μ).map (orderStatistic 0)) P := by
  simp_rw [orderStatistic_zero, map_orderStatistic_zero]
  exact hindep.hasLaw_inf' hX

/-- The greatest order statistic of independent coordinates has the pushforward of the product
measure along `orderStatistic (Fin.last n)`. Only `MeasurableSup₂ α` is needed because
`orderStatistic (Fin.last n)` is the sample maximum. -/
theorem hasLaw_orderStatistic_last_indep {Ω : Type*} {_ : MeasurableSpace Ω} [MeasurableSup₂ α]
    {P : Measure Ω} {μ : Fin (n + 1) → Measure α} {X : Fin (n + 1) → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω ↦ orderStatistic (Fin.last n) fun i ↦ X i ω)
      ((Measure.pi μ).map (orderStatistic (Fin.last n))) P := by
  simp_rw [orderStatistic_last, map_orderStatistic_last]
  exact hindep.hasLaw_sup' hX

end LinearOrder

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

end General

/-- For an independent family with possibly different laws, the probability that the order
statistic at position `k` is at most `t` is the corresponding Poisson-binomial tail.
Positions are counted from zero, and ties are included. -/
theorem measureReal_setOf_orderStatistic_le_indep
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Fin n → Measure ℝ} {X : Fin n → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) (k : Fin n) (t : ℝ) :
    P.real {ω | orderStatistic k (fun i ↦ X i ω) ≤ t} =
      (poissonBinomialMeasure fun i ↦ ⟨cdf (μ i) t, cdf_nonneg _ _, cdf_le_one _ _⟩).real
        (Ioi (k : ℕ)) := by
  have := hindep.isProbabilityMeasure
  have _ (i : Fin n) : IsProbabilityMeasure (μ i) := (hX i).isProbabilityMeasure_iff.1 this
  rw [← cdf_map_orderStatistic_pi_eq_poissonBinomial, cdf_eq_real,
    map_measureReal_apply (measurable_orderStatistic k) measurableSet_Iic]
  exact (hindep.hasLaw_pi hX).measureReal_eq (measurable_orderStatistic k measurableSet_Iic)

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

end Endpoints

end TauCeti.Probability
