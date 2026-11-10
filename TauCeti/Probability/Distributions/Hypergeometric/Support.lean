/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.Hypergeometric.Basic

/-!
# Topological support of hypergeometric laws

For valid population, marked-count, and sample-size parameters, the support of the
hypergeometric law is the interval of feasible marked counts. Its lower endpoint is the number
of marked objects forced into the sample, while its upper endpoint is the smaller of the marked
population and the sample size. Invalid parameters give the empty support because the totalized
law is zero.

Applying arbitrary labels transports this finite support exactly, even when distinct counts have
the same label. In particular, the real-cast support is the finite set of feasible integer points,
not the whole real interval between its endpoints.

## Main results

* `TauCeti.Probability.support_hypergeometricMeasure` identifies the native support.
* `TauCeti.Probability.support_map_hypergeometricMeasure` identifies the support after applying
  arbitrary labels in a T₁ Borel space.
* `TauCeti.Probability.support_map_cast_hypergeometricMeasure` specializes to the real cast law.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

open MeasureTheory Set

namespace TauCeti.Probability

/-- The support of a valid native hypergeometric law is the interval of feasible marked counts.
Invalid population or sample parameters give empty support. -/
@[simp]
theorem support_hypergeometricMeasure (N K n : ℕ) :
    (hypergeometricMeasure N K n).support =
      if K ≤ N ∧ n ≤ N then Icc (n - (N - K)) (min K n) else ∅ := by
  by_cases h : K ≤ N ∧ n ≤ N
  · rw [ite_eq_left h, Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    rw [mem_ofPred_eq, hypergeometricMeasure_singleton_ne_zero_iff h.1]
    simp only [mem_Icc]
    omega
  · rw [ite_eq_right h, hypergeometricMeasure_eq_zero_of_invalid h, Measure.support_zero]

/-- Applying labels to a hypergeometric law sends its finite native support to the image of the
feasible count interval. The formula does not require the labels to be injective. -/
theorem support_map_hypergeometricMeasure {E : Type*} [TopologicalSpace E] [T1Space E]
    [MeasurableSpace E] [BorelSpace E] (N K n : ℕ) (f : ℕ → E) :
    ((hypergeometricMeasure N K n).map f).support =
      if K ≤ N ∧ n ≤ N then f '' Icc (n - (N - K)) (min K n) else ∅ := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae
    continuous_of_discreteTopology, support_hypergeometricMeasure]
  split_ifs
  · exact ((Set.finite_Icc _ _).image f).isClosed.closure_eq
  · rw [image_empty, closure_empty]

/-- The support of the real-cast hypergeometric law is the finite set of feasible integer
counts, including all valid deterministic boundary cases. -/
@[simp]
theorem support_map_cast_hypergeometricMeasure (N K n : ℕ) :
    ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → ℝ)).support =
      if K ≤ N ∧ n ≤ N then
        (Nat.cast : ℕ → ℝ) '' Icc (n - (N - K)) (min K n)
      else ∅ :=
  support_map_hypergeometricMeasure N K n Nat.cast

end TauCeti.Probability
