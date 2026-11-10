/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.BetaBinomial.Basic

/-!
# Topological support of beta-binomial distributions

A beta-binomial law with positive shapes assigns positive mass to every count from zero to the
trial count. This file identifies its exact topological support, both on the natural-number
carrier and after casting to the reals. The latter is a finite set of integer points, not the
whole real interval between the endpoints. Invalid shapes give empty support; zero trials with
valid shapes give the singleton zero.

## Main results

* `TauCeti.Probability.support_betaBinomialMeasure` identifies the native support for all
  parameters.
* `TauCeti.Probability.support_map_cast_betaBinomialMeasure` identifies the real-cast support for
  all parameters.

## Reference

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The native support of a beta-binomial law with positive shapes consists of precisely the
counts at most the trial count. Invalid shapes give empty support. -/
@[simp]
theorem support_betaBinomialMeasure (n : ℕ) (a b : ℝ) :
    (betaBinomialMeasure n a b).support = if 0 < a ∧ 0 < b then Iic n else ∅ := by
  by_cases hvalid : 0 < a ∧ 0 < b
  · rw [ite_eq_left hvalid, Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    exact betaBinomialMeasure_singleton_ne_zero_iff hvalid.1 hvalid.2 n k
  · rw [ite_eq_right hvalid, betaBinomialMeasure_eq_zero_of_invalid hvalid,
      Measure.support_zero]

/-- The support of a real-cast beta-binomial law with positive shapes is the finite set of
natural counts from zero to the trial count, embedded in `ℝ`. Invalid shapes give empty support. -/
@[simp]
theorem support_map_cast_betaBinomialMeasure (n : ℕ) (a b : ℝ) :
    ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)).support =
      if 0 < a ∧ 0 < b then (Nat.cast : ℕ → ℝ) '' Iic n else ∅ := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    support_betaBinomialMeasure]
  by_cases hvalid : 0 < a ∧ 0 < b
  · simp only [ite_eq_left hvalid]
    exact (Nat.isClosedEmbedding_coe_real.isClosedMap _ isClosed_Iic).closure_eq
  · simp [hvalid]

end TauCeti.Probability
