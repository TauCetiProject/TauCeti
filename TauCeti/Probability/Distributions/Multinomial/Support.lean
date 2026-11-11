/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Multinomial.Basic
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of multinomial laws

The multinomial law is supported precisely on count vectors with the prescribed total that
avoid zero-weight cells. Its continuous images have finite support, so their support is the
image of this set without taking a closure. In particular, the Euclidean cast is supported on
these integer count vectors, not on their convex hull.

The formulas include zero trials and probability vectors on simplex faces.

## Main results

* `TauCeti.Probability.support_multinomialMeasure`: exact native support.
* `TauCeti.Probability.support_map_multinomialMeasure`: support after applying arbitrary labels
  in a T₁ Borel space; labels need not be injective.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

open Convexity MeasureTheory Set
open scoped Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The support consists of count vectors with total `n` that assign no counts to zero-weight
cells. This includes the singleton zero vector when there are no trials. -/
@[simp]
theorem support_multinomialMeasure (n : ℕ) (p : StdSimplex NNReal ι) :
    (multinomialMeasure n p).support =
      {k | (∑ i, k i = n) ∧ ∀ i, k i ≠ 0 → p.weights i ≠ 0} := by
  rw [Measure.support_eq_setOf_singleton_ne_zero]
  simp only [multinomialMeasure_singleton_ne_zero_iff]

/-- Applying labels to multinomial counts transports their finite support exactly, even when
several count vectors have the same label. No closure of the image is needed.
Taking `f := multinomialToEuclidean` gives the exact support of the Euclidean cast law. -/
@[simp]
theorem support_map_multinomialMeasure {E : Type*} [TopologicalSpace E] [T1Space E]
    [MeasurableSpace E] [BorelSpace E] (n : ℕ) (p : StdSimplex NNReal ι)
    (f : (ι → ℕ) → E) :
    ((multinomialMeasure n p).map f).support =
      f '' {k | (∑ i, k i = n) ∧ ∀ i, k i ≠ 0 → p.weights i ≠ 0} := by
  classical
  have hfinite : ({k : ι → ℕ | (∑ i, k i = n) ∧
      ∀ i, k i ≠ 0 → p.weights i ≠ 0} : Set (ι → ℕ)).Finite := by
    refine (Finset.piAntidiag Finset.univ n).finite_toSet.subset ?_
    intro k hk
    simp only [Finset.mem_coe, Finset.mem_piAntidiag]
    exact ⟨hk.1, by simp⟩
  rw [Measure.support_map_eq_closure_image _ (multinomialMeasure n p).support_mem_ae
    continuous_of_discreteTopology, support_multinomialMeasure,
    (hfinite.image f).isClosed.closure_eq]

end TauCeti.Probability
