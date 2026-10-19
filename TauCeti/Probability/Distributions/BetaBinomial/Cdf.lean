/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaBinomial.Basic
public import TauCeti.Probability.Cdf

/-!
# Cumulative probabilities of beta-binomial laws

Native cumulative masses are finite sums of the classical Beta-function weights. The cdf of
the real cast vanishes below zero and uses the natural floor at nonnegative cutoffs. The native
cumulative mass is one at and above the trial count, including zero trials.

These formulas connect the beta-binomial mass API to the natural-cast cdf bridge in
`TauCeti.Probability.Cdf` and provide the explicit crossings used by discrete quantiles.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- A beta-binomial cumulative mass is the finite sum of its Beta-function weights.
The binomial coefficient makes all terms above the trial count vanish. -/
theorem betaBinomialMeasure_real_Iic {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n k : ℕ) :
    (betaBinomialMeasure n a b).real (Iic k) =
      ∑ j ∈ Finset.Iic k,
        n.choose j * beta (a + j) (b + (n - j)) / beta a b := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb n
  simp_rw [← betaBinomialMeasure_real_singleton ha hb n]
  simp

/-- At nonnegative cutoffs, the real-cast beta-binomial cdf sums the masses through the natural
floor. -/
theorem cdf_map_cast_betaBinomialMeasure {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (hx : 0 ≤ x) :
    cdf ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) x =
      ∑ j ∈ Finset.Iic ⌊x⌋₊,
        n.choose j * beta (a + j) (b + (n - j)) / beta a b := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb n
  rw [Measure.cdf_map_natCast _ hx]
  exact betaBinomialMeasure_real_Iic ha hb n ⌊x⌋₊

/-- The real-cast beta-binomial cdf vanishes at negative cutoffs. -/
theorem cdf_map_cast_betaBinomialMeasure_of_neg {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (hx : x < 0) :
    cdf ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb n
  exact Measure.cdf_map_natCast_of_neg _ hx

/-- The native cumulative mass is one at or above the trial count. -/
theorem betaBinomialMeasure_real_Iic_eq_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {n k : ℕ} (hk : n ≤ k) : (betaBinomialMeasure n a b).real (Iic k) = 1 := by
  let _ := isProbabilityMeasure_betaBinomialMeasure ha hb n
  rw [← probReal_univ (μ := betaBinomialMeasure n a b)]
  apply measureReal_congr
  have hle : ∀ᵐ j ∂betaBinomialMeasure n a b, j ≤ k := by
    rw [ae_iff_of_countable]
    intro j hj
    exact ((betaBinomialMeasure_singleton_ne_zero_iff ha hb n j).mp hj).trans hk
  filter_upwards [hle] with j hj
  simp only [mem_Iic, mem_univ, hj]

end TauCeti.Probability
