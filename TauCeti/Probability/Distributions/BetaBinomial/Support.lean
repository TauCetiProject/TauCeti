/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaBinomial.Basic
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of beta-binomial laws

For positive Beta shape parameters, the beta-binomial law with `n` trials has positive mass at
every count from zero through `n`. Its native topological support is therefore `Set.Iic n`.
Invalid shape parameters give the zero measure and hence have empty support.

Applying arbitrary labels transports this finite support exactly, even when different counts
have the same label. In particular, the real-cast support consists of the integer points between
zero and `n`, rather than the whole interval.

## Main results

* `TauCeti.Probability.support_betaBinomialMeasure` identifies the native support for every
  parameter value.
* `TauCeti.Probability.support_map_betaBinomialMeasure` identifies the support after applying
  arbitrary labels in a T₁ Borel space.
* `TauCeti.Probability.support_map_cast_betaBinomialMeasure` gives the real-cast specialization.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The native support of a beta-binomial law is all counts through the trial count when both
shape parameters are positive, and is empty when either shape is invalid. -/
@[simp]
theorem support_betaBinomialMeasure (n : ℕ) (a b : ℝ) :
    (betaBinomialMeasure n a b).support =
      if 0 < a ∧ 0 < b then Iic n else ∅ := by
  by_cases h : 0 < a ∧ 0 < b
  · rw [ite_eq_left h, Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    simp only [mem_ofPred_eq, mem_Iic,
      betaBinomialMeasure_singleton_ne_zero_iff h.1 h.2]
  · rw [ite_eq_right h, betaBinomialMeasure_eq_zero_of_invalid h, Measure.support_zero]

/-- Applying labels to a beta-binomial count transports its finite support exactly. Labels need
not be injective, and invalid shape parameters give empty support. -/
@[simp]
theorem support_map_betaBinomialMeasure {E : Type*} [TopologicalSpace E] [T1Space E]
    [MeasurableSpace E] [BorelSpace E] (n : ℕ) (a b : ℝ) (f : ℕ → E) :
    ((betaBinomialMeasure n a b).map f).support =
      if 0 < a ∧ 0 < b then f '' Iic n else ∅ := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae
    continuous_of_discreteTopology, support_betaBinomialMeasure]
  by_cases h : 0 < a ∧ 0 < b
  · rw [ite_eq_left h, ite_eq_left h,
      ((Set.toFinite (Iic n)).image f).isClosed.closure_eq]
  · simp [h]

/-- The real-cast beta-binomial law is supported on the integer counts from zero through the
trial count. Invalid shape parameters give empty support. -/
theorem support_map_cast_betaBinomialMeasure (n : ℕ) (a b : ℝ) :
    ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)).support =
      if 0 < a ∧ 0 < b then (Nat.cast : ℕ → ℝ) '' Iic n else ∅ :=
  support_map_betaBinomialMeasure n a b Nat.cast

end TauCeti.Probability
