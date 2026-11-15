/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Basic
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological supports of hypergeometric laws

The support of a valid hypergeometric law is the integer interval from `n - (N - K)` to
`min K n`. The lower endpoint counts marked objects forced into the sample; the upper endpoint
is the largest possible marked count. Invalid parameters give empty support.

Applying arbitrary labels transports this finite support exactly, even when distinct counts have
the same label. In particular, the real-cast support is a finite set of integers, not the real
interval between its endpoints. Both formulas include zero populations and deterministic samples.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

open MeasureTheory Set Topology

namespace TauCeti.Probability

/-- The native hypergeometric support is the interval of possible marked counts, or empty for
invalid parameters. -/
@[simp]
theorem support_hypergeometricMeasure (N K n : ℕ) :
    (hypergeometricMeasure N K n).support =
      if K ≤ N ∧ n ≤ N then Icc (n - (N - K)) (min K n) else ∅ := by
  split_ifs with h
  · rw [Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    rw [mem_ofPred_eq, hypergeometricMeasure_singleton_ne_zero_iff h.1]
    simp only [mem_Icc, le_min_iff]
    omega
  · simp [hypergeometricMeasure_eq_zero_of_invalid h]

/-- Applying labels to a hypergeometric law sends its finite native support to the image of the
feasible count interval. The formula does not require the labels to be injective. -/
theorem support_map_hypergeometricMeasure {E : Type*} [TopologicalSpace E] [T1Space E]
    [MeasurableSpace E] [BorelSpace E] (N K n : ℕ) (f : ℕ → E) :
    ((hypergeometricMeasure N K n).map f).support =
      if K ≤ N ∧ n ≤ N then f '' Icc (n - (N - K)) (min K n) else ∅ := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae
    continuous_of_discreteTopology, support_hypergeometricMeasure]
  split_ifs
  · exact ((finite_Icc _ _).image f).isClosed.closure_eq
  · simp

/-- The support after natural-number casting is the image of the finite interval of possible
counts. No injectivity of the cast is required. In particular, real casting retains precisely
the supported integer counts. -/
@[simp]
theorem support_map_cast_hypergeometricMeasure {R : Type*} [AddMonoidWithOne R]
    [TopologicalSpace R] [T1Space R] [MeasurableSpace R] [BorelSpace R] (N K n : ℕ) :
    ((hypergeometricMeasure N K n).map (Nat.cast : ℕ → R)).support =
      if K ≤ N ∧ n ≤ N then
        (Nat.cast : ℕ → R) '' Icc (n - (N - K)) (min K n) else ∅ :=
  support_map_hypergeometricMeasure N K n Nat.cast

end TauCeti.Probability
