/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Categorical.Basic
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of categorical laws

The topological support of a categorical law consists exactly of its positive-weight
categories. After applying labels, its support is the image of those categories, including
when distinct categories receive the same label. These equalities strengthen the finite
almost-sure carrying-set statement in `Categorical.Basic`.

## Main results

* `Convexity.StdSimplex.support_categoricalMeasure` identifies the support on a discrete
  category space.
* `Convexity.StdSimplex.support_map_categoricalMeasure` identifies the support after applying
  labels in a T₁ space.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open MeasureTheory Set TauCeti.Probability
open scoped NNReal

namespace Convexity.StdSimplex

variable {I β : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- The support of a categorical law on a discrete category space is exactly the set of
positive-weight categories. This includes probability vectors on proper simplex faces. -/
@[simp]
theorem support_categoricalMeasure [TopologicalSpace I] [DiscreteTopology I]
    (p : StdSimplex ℝ≥0 I) :
    (categoricalMeasure p).support = p.weights.support := by
  rw [Measure.support_eq_setOf_singleton_ne_zero]
  ext i
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finsupp.mem_support_iff,
    categoricalMeasure_singleton, ENNReal.coe_ne_zero]

open Classical in
/-- Applying labels to a categorical law sends its support to the finite image of its
positive-weight categories. Distinct categories may have the same label. -/
@[simp]
theorem support_map_categoricalMeasure [TopologicalSpace β] [T1Space β]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : StdSimplex ℝ≥0 I) (f : I → β) :
    ((categoricalMeasure p).map f).support = p.weights.support.image f := by
  apply Set.Subset.antisymm
  · exact Measure.support_subset_of_isClosed
      (p.weights.support.image f).finite_toSet.isClosed
      (ae_mem_image_support_map_categoricalMeasure p f)
  · intro x hx
    rw [Measure.mem_support_iff_forall]
    intro U hU
    exact (pos_iff_ne_zero.mpr (map_categoricalMeasure_singleton_ne_zero p f hx)).trans_le
      (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

end Convexity.StdSimplex
