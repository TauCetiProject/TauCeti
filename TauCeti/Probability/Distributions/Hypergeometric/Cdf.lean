/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Cdf
public import TauCeti.Probability.Distributions.Hypergeometric.Basic

/-!
# The real hypergeometric cumulative distribution function

The hypergeometric law counts marked objects in a sample drawn without replacement. Casting
this count to the reals gives a cumulative distribution function that vanishes at negative
cutoffs and sums the singleton masses through the natural floor at nonnegative cutoffs.

`cdf_map_cast_hypergeometricMeasure` gives this finite-sum formula at nonnegative cutoffs, and
`cdf_map_cast_hypergeometricMeasure_of_neg` gives zero at negative cutoffs, for every valid
population, marked count, and sample size, including a population of size zero.
They use the native cumulative-mass formula from
`TauCeti.Probability.Distributions.Hypergeometric.Basic` and the natural-cast cdf bridge from
`TauCeti.Probability.Cdf`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- At a nonnegative cutoff, the cdf of the real cast hypergeometric law is the finite sum
of its masses through the natural floor of the cutoff. The explicit sample-size
branch makes the formula valid even when the cutoff exceeds the support. -/
theorem cdf_map_cast_hypergeometricMeasure {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N)
    {x : ℝ} (hx : 0 ≤ x) :
    cdf ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) x =
      ∑ j ∈ Finset.Iic ⌊x⌋₊,
        if j ≤ n then
          (K.choose j : ℝ) * ((N - K).choose (n - j) : ℝ) / (N.choose n : ℝ)
        else 0 := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  rw [Measure.cdf_map_natCast _ hx, ← Set.Iic_def,
    hypergeometricMeasure_real_Iic_eq_sum hK hn]

/-- Below the origin, the cdf of the real cast hypergeometric law vanishes. -/
theorem cdf_map_cast_hypergeometricMeasure_of_neg {N K n : ℕ} (hK : K ≤ N) (hn : n ≤ N)
    {x : ℝ} (hx : x < 0) :
    cdf ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)) x = 0 := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  exact Measure.cdf_map_natCast_of_neg _ hx

/-- The cumulative mass below the lower endpoint of the hypergeometric support is zero. -/
theorem hypergeometricMeasure_real_Iic_eq_zero_of_lt_lower
    {N K n k : ℕ} (hK : K ≤ N) (hn : n ≤ N) (hk : k < n - (N - K)) :
    (hypergeometricMeasure N K n).real (Iic k) = 0 := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  rw [← Set.Iic_def, hypergeometricMeasure_real_Iic]
  apply Finset.sum_eq_zero
  intro j hj
  rw [measureReal_eq_zero_iff, hypergeometricMeasure_singleton hK hn]
  apply not_ne_iff.mp
  intro hjne
  have hsupp := (hypergeometricWeight_ne_zero_iff N K n j).mp hjne
  have hjk : j ≤ k := by simpa using hj
  omega

/-- The cumulative mass at or above the upper endpoint of the hypergeometric support is one. -/
theorem hypergeometricMeasure_real_Iic_eq_one_of_upper_le
    {N K n k : ℕ} (hK : K ≤ N) (hn : n ≤ N) (hk : min K n ≤ k) :
    (hypergeometricMeasure N K n).real (Iic k) = 1 := by
  let _ := isProbabilityMeasure_hypergeometricMeasure hK hn
  rw [← probReal_univ (μ := hypergeometricMeasure N K n)]
  apply measureReal_congr
  have hle : ∀ᵐ j ∂hypergeometricMeasure N K n, j ≤ k := by
    rw [ae_iff_of_countable (μ := hypergeometricMeasure N K n)]
    intro j hj
    have hweight : hypergeometricWeight N K n j ≠ 0 := by
      rwa [hypergeometricMeasure_singleton hK hn] at hj
    have hsupp := (hypergeometricWeight_ne_zero_iff N K n j).mp hweight
    omega
  filter_upwards [hle] with j hj
  apply propext
  simp only [mem_Iic, mem_univ, iff_true]
  exact hj

end TauCeti.Probability
