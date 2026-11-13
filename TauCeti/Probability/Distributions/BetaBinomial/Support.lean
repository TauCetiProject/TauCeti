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

Applying arbitrary labels transports this finite support exactly, even when labels are not
injective. In particular, the support of a real-cast law is the finite set of integer points,
rather than the real interval between zero and `n`.

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

/-- Applying labels to a beta-binomial count transports its finite support exactly. Labels need
not be injective, and invalid shape parameters give empty support. Taking `f := Nat.cast` gives
the support of a cast law. -/
@[simp]
theorem support_map_betaBinomialMeasure {E : Type*} [TopologicalSpace E] [T1Space E]
    [MeasurableSpace E] [MeasurableSingletonClass E] (n : ℕ) (a b : ℝ) (f : ℕ → E) :
    ((betaBinomialMeasure n a b).map f).support =
      if 0 < a ∧ 0 < b then f '' Iic n else ∅ := by
  have hfin := (Set.finite_Iic n).image f
  split_ifs with h
  · refine Set.Subset.antisymm (Measure.support_subset_of_isClosed hfin.isClosed ?_) ?_
    · exact (ae_map_iff (Measurable.of_discrete).aemeasurable hfin.measurableSet).2 <|
        (ae_le_betaBinomialMeasure n a b).mono fun k hk ↦ mem_image_of_mem f hk
    · rintro _ ⟨k, hk, rfl⟩
      exact Measure.mem_support_map_of_continuousAt (Measurable.of_discrete).aemeasurable
        continuous_of_discreteTopology.continuousAt (by simpa [h] using hk)
  · simp [betaBinomialMeasure_eq_zero_of_invalid h]

end TauCeti.Probability
