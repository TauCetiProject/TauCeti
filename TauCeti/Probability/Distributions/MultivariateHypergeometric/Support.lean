/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MultivariateHypergeometric.Basic
public import TauCeti.Probability.Distributions.Multinomial.Basic
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological supports of multivariate hypergeometric laws

The topological support of sampling without replacement consists exactly of the count vectors
with the requested total that overdraw no category. This finite set also determines the support
of any labelled observation, including the usual Euclidean cast of the count vector. Labels need
not be injective: counts with the same label contribute to the same support point.

All statements include empty category types, zero-sized categories, empty and full samples, and
sample sizes exceeding the population. In the last case the admissible set and the support are
both empty.

## Main results

* `TauCeti.Probability.support_multivariateHypergeometricMeasure`: exact native support.
* `TauCeti.Probability.support_map_multivariateHypergeometricMeasure`: exact support under
  arbitrary labels in a T₁ Borel space.
* `TauCeti.Probability.support_map_multinomialToEuclidean_multivariateHypergeometricMeasure`:
  exact support of the Euclidean count law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 39.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- A multivariate hypergeometric count vector lies in the topological support exactly when its
counts total the sample size and do not exceed the category populations. -/
@[simp]
theorem support_multivariateHypergeometricMeasure (K : ι → ℕ) (n : ℕ) :
    (multivariateHypergeometricMeasure K n).support =
      {k | ∑ i, k i = n ∧ ∀ i, k i ≤ K i} := by
  ext k
  simp only [Measure.support_eq_setOf_singleton_ne_zero, mem_ofPred_eq,
    multivariateHypergeometricMeasure_singleton_ne_zero_iff]

/-- Arbitrary labels of a multivariate hypergeometric sample have support equal to the labels of
admissible count vectors. No injectivity of the labels or validity of the sample size is needed. -/
theorem support_map_multivariateHypergeometricMeasure {E : Type*} [TopologicalSpace E]
    [T1Space E] [MeasurableSpace E] [BorelSpace E] (K : ι → ℕ) (n : ℕ)
    (f : (ι → ℕ) → E) :
    ((multivariateHypergeometricMeasure K n).map f).support =
      f '' {k | ∑ i, k i = n ∧ ∀ i, k i ≤ K i} := by
  classical
  have hfinite : Set.Finite {k : ι → ℕ | ∑ i, k i = n ∧ ∀ i, k i ≤ K i} :=
    (Finset.piAntidiag Finset.univ n).finite_toSet.subset fun k hk ↦ by
      simpa [Finset.mem_piAntidiag] using hk.1
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae continuous_of_discreteTopology,
    support_multivariateHypergeometricMeasure, (hfinite.image f).isClosed.closure_eq]

/-- The Euclidean multivariate hypergeometric law is supported exactly on the cast admissible
integer count vectors, not on their convex hull. -/
theorem support_map_multinomialToEuclidean_multivariateHypergeometricMeasure
    (K : ι → ℕ) (n : ℕ) :
    ((multivariateHypergeometricMeasure K n).map multinomialToEuclidean).support =
      multinomialToEuclidean '' {k | ∑ i, k i = n ∧ ∀ i, k i ≤ K i} :=
  support_map_multivariateHypergeometricMeasure K n multinomialToEuclidean

end TauCeti.Probability
