/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.BetaNegativeBinomial.Basic

/-!
# Topological support of beta-negative-binomial distributions

This file identifies the exact topological support of beta-negative-binomial laws on their native
natural-number carrier and after casting to the reals. At positive negative-binomial shape, every
natural number has positive mass. At shape zero, the law is concentrated at zero. Invalid
parameters give the zero measure and hence empty support.

## Main results

* `TauCeti.Probability.support_betaNegativeBinomialMeasure` gives the support on `ℕ` for every
  parameter value.
* `TauCeti.Probability.support_map_cast_betaNegativeBinomialMeasure` gives the support of the
  real-cast law for every parameter value.

## Reference

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The native support of a beta-negative-binomial law is all of `ℕ` at positive shape, the
singleton zero at shape zero, and empty for invalid parameters. -/
@[simp]
theorem support_betaNegativeBinomialMeasure (r a b : ℝ) :
    (betaNegativeBinomialMeasure r a b).support =
      if 0 ≤ r ∧ 0 < a ∧ 0 < b then if r = 0 then {0} else Set.univ else ∅ := by
  by_cases hvalid : 0 ≤ r ∧ 0 < a ∧ 0 < b
  · rw [ite_eq_left hvalid, Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    rw [mem_ofPred_eq,
      betaNegativeBinomialMeasure_singleton_ne_zero_iff hvalid.1 hvalid.2.1 hvalid.2.2]
    by_cases hr : r = 0
    · simp [hr]
    · simp [hr, lt_of_le_of_ne hvalid.1 (Ne.symm hr)]
  · rw [ite_eq_right hvalid, betaNegativeBinomialMeasure_eq_zero_of_invalid hvalid,
      Measure.support_zero]

/-- The support of a real-cast beta-negative-binomial law is the set of nonnegative integers at
positive shape, the singleton zero at shape zero, and empty for invalid parameters. -/
@[simp]
theorem support_map_cast_betaNegativeBinomialMeasure (r a b : ℝ) :
    ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)).support =
      if 0 ≤ r ∧ 0 < a ∧ 0 < b then
        if r = 0 then {0} else Set.range (Nat.cast : ℕ → ℝ)
      else ∅ := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    support_betaNegativeBinomialMeasure]
  by_cases hvalid : 0 ≤ r ∧ 0 < a ∧ 0 < b
  · simp only [ite_eq_left hvalid]
    by_cases hr : r = 0
    · subst r
      simp
    · simp only [ite_eq_right hr]
      rw [image_univ,
        Nat.isClosedEmbedding_coe_real.isClosed_range.closure_eq]
  · simp [hvalid]

end TauCeti.Probability
