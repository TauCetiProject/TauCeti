/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.PoissonBinomial.Basic
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of Poisson-binomial laws

The native support is the interval of natural counts from the number of certain successes
to the number of trials with nonzero success probability. Every count in this interval has
positive mass. This includes empty families and probabilities equal to zero or one.

Casting transports this finite support exactly. In particular, the real-cast support consists
of the integer points in the interval, which can be used to decide whether every neighbourhood
of a real cutoff has positive probability. The cast need not be injective, so the formula also
applies to targets of positive characteristic.

## References

* Y. H. Wang, “On the number of successes in independent trials”, *Statistica Sinica* 3 (1993),
  295–312.
-/

public section

open MeasureTheory Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

open Classical in
/-- The support of the native Poisson-binomial law is precisely the interval from the number
of certain successes to the number of possible successes, including deterministic trials. -/
@[simp]
theorem support_poissonBinomialMeasure (p : ι → unitInterval) :
    (poissonBinomialMeasure p).support =
      Icc (Finset.univ.filter fun i ↦ p i = 1).card
        (Finset.univ.filter fun i ↦ p i ≠ 0).card := by
  rw [Measure.support_eq_setOf_singleton_ne_zero]
  ext k
  exact poissonBinomialMeasure_singleton_ne_zero_iff p k

open Classical in
/-- The support of a cast Poisson-binomial law is the image of its finite interval of possible
native counts. No injectivity of the cast is required. -/
@[simp]
theorem support_map_cast_poissonBinomialMeasure {R : Type*} [AddMonoidWithOne R]
    [TopologicalSpace R] [T1Space R] [MeasurableSpace R] [BorelSpace R]
    (p : ι → unitInterval) :
    ((poissonBinomialMeasure p).map (Nat.cast : ℕ → R)).support =
      (Nat.cast : ℕ → R) ''
        Icc (Finset.univ.filter fun i ↦ p i = 1).card
          (Finset.univ.filter fun i ↦ p i ≠ 0).card := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae
    continuous_of_discreteTopology, support_poissonBinomialMeasure,
    ((Set.finite_Icc _ _).image _).isClosed.closure_eq]

end TauCeti.Probability
