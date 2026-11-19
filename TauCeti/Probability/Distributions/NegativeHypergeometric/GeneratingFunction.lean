/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NegativeHypergeometric.Basic
public import TauCeti.Probability.GeneratingFunction

/-!
# Probability-generating functions of negative hypergeometric laws

The number of failures before a prescribed success in sampling without replacement has finite
support. Its probability-generating function is therefore a finite polynomial at every real
argument, including arguments outside the unit interval. The coefficients below are the explicit
binomial-coefficient masses, with the zero-wait boundary included.

When the success count exceeds the population size, both the totalized law and the displayed
polynomial vanish: every coefficient has denominator `N.choose K = 0`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Section 6.2.2.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti.Probability

/-- The negative hypergeometric probability-generating function is the finite polynomial in its
binomial-coefficient masses, for every real argument. This includes waiting for zero successes
and populations with `N < K`, where the law and polynomial are both zero. -/
theorem pgf_negativeHypergeometricMeasure {N K r : ℕ} (hr : r ≤ K) (z : ℝ) :
    pgf id (negativeHypergeometricMeasure N K r) z =
      ∑ k ∈ Finset.range (N - K + 1),
        (((k + r - 1).choose k : ℝ) * ((N - r - k).choose (K - r) : ℝ) /
          (N.choose K : ℝ)) * z ^ k := by
  rw [pgf_def, integral_negativeHypergeometricMeasure _ hr]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk : k ≤ N - K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [negativeHypergeometricWeight_toReal, ite_eq_left hk, id_eq, smul_eq_mul]

end TauCeti.Probability
