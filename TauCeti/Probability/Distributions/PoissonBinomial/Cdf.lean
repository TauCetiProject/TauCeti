/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.PoissonBinomial.Basic
public import TauCeti.Probability.Cdf

/-!
# Cumulative probabilities of Poisson-binomial laws

The cumulative probability of a Poisson-binomial count is the sum of the weights of success
sets whose cardinalities do not exceed the cutoff. The cdf of its real cast uses the natural
floor only at nonnegative cutoffs and vanishes below zero.

The effective lower endpoint counts certain successes, while the upper endpoint counts trials
with nonzero success probability. The cumulative mass is zero below the former and one at or
above the latter. These endpoints account for deterministic trials and empty families.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

open Classical in
/-- The native cumulative mass sums the weights of all success sets of cardinality at most `k`. -/
theorem poissonBinomialMeasure_real_Iic (p : ι → unitInterval) (k : ℕ) :
    (poissonBinomialMeasure p).real (Iic k) =
      ∑ s : Finset ι with s.card ≤ k, (poissonBinomialWeight p s : ℝ) := by
  rw [measureReal_def, poissonBinomialMeasure_apply, ENNReal.toReal_sum]
  · simp
  · intro s hs
    simp

open Classical in
/-- The cdf at a nonnegative cutoff is the finite cumulative sum through its natural floor. -/
theorem cdf_map_cast_poissonBinomialMeasure (p : ι → unitInterval) {x : ℝ} (hx : 0 ≤ x) :
    cdf ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)) x =
      ∑ s : Finset ι with s.card ≤ ⌊x⌋₊, (poissonBinomialWeight p s : ℝ) := by
  rw [Measure.cdf_map_natCast _ hx, poissonBinomialMeasure_real_Iic]

/-- The cdf of a real-cast Poisson-binomial count vanishes at negative cutoffs. -/
theorem cdf_map_cast_poissonBinomialMeasure_of_neg (p : ι → unitInterval) {x : ℝ} (hx : x < 0) :
    cdf ((poissonBinomialMeasure p).map (Nat.cast : ℕ → ℝ)) x = 0 :=
  Measure.cdf_map_natCast_of_neg _ hx

open Classical in
/-- No count below the number of certain successes has positive cumulative mass. -/
theorem poissonBinomialMeasure_real_Iic_eq_zero_of_lt_lower (p : ι → unitInterval) {k : ℕ}
    (hk : k < (Finset.univ.filter fun i ↦ p i = 1).card) :
    (poissonBinomialMeasure p).real (Iic k) = 0 := by
  rw [measureReal_eq_zero_iff, measure_eq_zero_iff_ae_notMem, ae_iff_of_countable]
  intro j hj hjk
  have hsupp := (poissonBinomialMeasure_singleton_ne_zero_iff p j).mp hj
  simp only [mem_Iic] at hjk
  omega

open Classical in
/-- At or above the number of trials with nonzero success probability, the cumulative mass
is one. -/
theorem poissonBinomialMeasure_real_Iic_eq_one_of_upper_le (p : ι → unitInterval) {k : ℕ}
    (hk : (Finset.univ.filter fun i ↦ p i ≠ 0).card ≤ k) :
    (poissonBinomialMeasure p).real (Iic k) = 1 := by
  rw [← probReal_univ (μ := poissonBinomialMeasure p)]
  apply measureReal_congr
  have hle : ∀ᵐ j ∂poissonBinomialMeasure p, j ≤ k := by
    rw [ae_iff_of_countable]
    intro j hj
    exact ((poissonBinomialMeasure_singleton_ne_zero_iff p j).mp hj).2.trans hk
  filter_upwards [hle] with j hj
  simp only [mem_Iic, mem_univ, hj]

end TauCeti.Probability
