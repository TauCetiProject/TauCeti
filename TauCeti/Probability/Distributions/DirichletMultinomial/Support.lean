/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.DirichletMultinomial.Basic
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of Dirichlet-multinomial laws

For positive concentration parameters, every count vector with the prescribed total has
positive Dirichlet-multinomial mass. Thus the native support is the full count antidiagonal,
independently of the concentration values. Invalid concentration parameters give the zero
measure and hence empty support.

The count antidiagonal is finite. Consequently, applying arbitrary labels into a T₁ Borel
space transports the support exactly, even when several count vectors have the same label.
In particular, the Euclidean count law is supported on the cast integer vectors, rather than
on their convex hull.

## Main results

* `TauCeti.Probability.support_dirichletMultinomialMeasure`: exact native support, including
  invalid concentration parameters.
* `TauCeti.Probability.support_map_dirichletMultinomialMeasure`: exact support after applying
  arbitrary labels.
* `TauCeti.Probability.support_map_multinomialToEuclidean_dirichletMultinomialMeasure`: exact
  support of the Euclidean count law.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 40.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- With positive concentrations, the support is the count antidiagonal of total `n`.
If any concentration is nonpositive, the measure and its support are both zero. -/
@[simp]
theorem support_dirichletMultinomialMeasure (n : ℕ) (a : ι → ℝ) :
    (dirichletMultinomialMeasure n a).support =
      if ∀ i, 0 < a i then {k | ∑ i, k i = n} else ∅ := by
  classical
  by_cases ha : ∀ i, 0 < a i
  · rw [ite_eq_left ha, Measure.support_eq_setOf_singleton_ne_zero]
    ext k
    simp only [mem_ofPred_eq, dirichletMultinomialMeasure_singleton_ne_zero_iff ha]
  · rw [ite_eq_right ha, dirichletMultinomialMeasure_eq_zero_of_invalid ha]
    exact Measure.support_zero

/-- Arbitrary labels of a Dirichlet-multinomial count vector have support equal to the labels
of the count antidiagonal for valid concentrations, and empty support otherwise. Labels need
not be injective. -/
theorem support_map_dirichletMultinomialMeasure {E : Type*} [TopologicalSpace E]
    [T1Space E] [MeasurableSpace E] [BorelSpace E]
    (n : ℕ) (a : ι → ℝ) (f : (ι → ℕ) → E) :
    ((dirichletMultinomialMeasure n a).map f).support =
      if ∀ i, 0 < a i then f '' {k | ∑ i, k i = n} else ∅ := by
  classical
  have hfinite : Set.Finite {k : ι → ℕ | ∑ i, k i = n} :=
    (Finset.piAntidiag Finset.univ n).finite_toSet.subset fun k hk ↦ by
      simpa [Finset.mem_piAntidiag] using hk
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae
    continuous_of_discreteTopology, support_dirichletMultinomialMeasure]
  by_cases ha : ∀ i, 0 < a i
  · rw [ite_eq_left ha, ite_eq_left ha, (hfinite.image f).isClosed.closure_eq]
  · rw [ite_eq_right ha, ite_eq_right ha, image_empty, closure_empty]

/-- The Euclidean Dirichlet-multinomial law is supported exactly on the cast count vectors
whose coordinates total `n`. -/
theorem support_map_multinomialToEuclidean_dirichletMultinomialMeasure
    (n : ℕ) (a : ι → ℝ) :
    ((dirichletMultinomialMeasure n a).map multinomialToEuclidean).support =
      if ∀ i, 0 < a i then multinomialToEuclidean '' {k | ∑ i, k i = n} else ∅ :=
  support_map_dirichletMultinomialMeasure n a multinomialToEuclidean

end TauCeti.Probability
