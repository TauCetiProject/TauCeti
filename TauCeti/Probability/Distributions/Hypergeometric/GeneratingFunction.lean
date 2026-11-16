/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Basic
public import TauCeti.Probability.GeneratingFunction

/-!
# Probability-generating function of the hypergeometric law

The hypergeometric law has finite support, so its probability-generating function is a
polynomial at every real argument. The formula below also covers a sample larger than the
population: under the existing totalization, both the measure and every displayed mass vanish.

## Main result

* `TauCeti.Probability.pgf_hypergeometricMeasure`: the finite polynomial formula.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- The hypergeometric probability-generating function is the finite polynomial of its masses,
at every real argument. This includes an oversized sample, whose totalized law is zero. -/
theorem pgf_hypergeometricMeasure {N K n : ℕ} (hK : K ≤ N) (z : ℝ) :
    pgf id (hypergeometricMeasure N K n) z =
      ∑ k ∈ Finset.range (n + 1),
        ((K.choose k : ℝ) * ((N - K).choose (n - k) : ℝ) / (N.choose n : ℝ)) * z ^ k := by
  rw [pgf_def, integral_hypergeometricMeasure (fun k ↦ z ^ id k) hK]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hypergeometricWeight_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
    ENNReal.toReal_div, ENNReal.toReal_mul]
  norm_cast

end TauCeti.Probability
