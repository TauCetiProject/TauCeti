/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Binomial.Tail
public import TauCeti.Probability.Cdf

/-!
# The cumulative distribution function of the real binomial law

The real-valued binomial law `Bin(ℝ, n, p)` has a step-function cdf. It vanishes below zero,
equals one at and above `n`, and between those endpoints is the regularized incomplete beta
value `I_{1-p}(n - ⌊x⌋₊, ⌊x⌋₊ + 1)`. The formula includes zero trials and both endpoint
success probabilities. In particular, no positive-parameter beta identity is applied to an
atomic boundary law.

This connects the native cumulative-mass formula to the usual real cdf, so real-valued
binomial variables can use the same cdf API as continuous distributions.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed.,
  Wiley, 2005, §3.4.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The cdf of a real binomial law is the regularized incomplete beta value at the natural
floor of the cutoff inside its support, zero below the support, and one above it. -/
theorem cdf_map_cast_binomial (n : ℕ) (p : unitInterval) (x : ℝ) :
    cdf Bin(ℝ, n, p) x =
      if x < 0 then 0 else if (n : ℝ) ≤ x then 1 else
        regularizedIncompleteBeta ((n : ℝ) - ⌊x⌋₊) ((⌊x⌋₊ : ℝ) + 1) (1 - (p : ℝ)) := by
  by_cases hx : x < 0
  · simp only [ite_eq_left hx]
    exact Measure.cdf_map_natCast_of_neg _ hx
  · simp only [ite_eq_right hx]
    have hx0 : 0 ≤ x := le_of_not_gt hx
    rw [Measure.cdf_map_natCast _ hx0]
    by_cases hn : (n : ℝ) ≤ x
    · simp only [ite_eq_left hn]
      have hnfloor : n ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 hn
      have hfull : Iic ⌊x⌋₊ =ᵐ[Bin(n, p)] (univ : Set ℕ) := by
        filter_upwards [ae_le_of_hasLaw_binomial (P := Bin(n, p)) HasLaw.id] with k hk
        apply propext
        simp only [mem_Iic, mem_univ, iff_true]
        exact hk.trans hnfloor
      rw [measureReal_congr hfull, probReal_univ]
    · simp only [ite_eq_right hn]
      have hfloor : ⌊x⌋₊ ≤ n := by
        exact_mod_cast (Nat.floor_le hx0).trans (le_of_not_ge hn)
      exact binomial_cumulative_eq_regularizedIncompleteBeta hfloor p

end TauCeti.Probability
