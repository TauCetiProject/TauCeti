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

open MeasureTheory ProbabilityTheory

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

end TauCeti.Probability
