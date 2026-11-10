/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.BetaBinomial.Basic

/-!
# Topological support of beta-binomial laws

At positive shape parameters, a beta-binomial count with `n` trials has topological support
exactly the natural numbers from zero through `n`. Invalid shape parameters give the zero
measure and therefore have empty support.

Casting transports the finite native support exactly. Thus the support of a real-cast law is
the finite set of integer points, rather than the real interval between zero and `n`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The native support of a beta-binomial law is all counts through the trial count when both
shape parameters are positive, and is empty otherwise. -/
@[simp]
theorem support_betaBinomialMeasure (n : ℕ) (a b : ℝ) :
    (betaBinomialMeasure n a b).support = if 0 < a ∧ 0 < b then Iic n else ∅ := by
  by_cases h : 0 < a ∧ 0 < b
  · rw [ite_eq_left h, Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    exact betaBinomialMeasure_singleton_ne_zero_iff h.1 h.2 n k
  · simp [h]

/-- The support of a cast beta-binomial law is the finite image of its possible native counts
when both shape parameters are positive, and is empty otherwise. -/
@[simp]
theorem support_map_cast_betaBinomialMeasure {R : Type*} [AddMonoidWithOne R]
    [TopologicalSpace R] [T1Space R] [MeasurableSpace R] [BorelSpace R]
    (n : ℕ) (a b : ℝ) :
    ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → R)).support =
      if 0 < a ∧ 0 < b then (Nat.cast : ℕ → R) '' Iic n else ∅ := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae
    continuous_of_discreteTopology, support_betaBinomialMeasure]
  split_ifs
  · exact ((Set.finite_Iic n).image _).isClosed.closure_eq
  · simp

end TauCeti.Probability
