/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measures on a product of charted spaces

A measure on a product `M × N` of second countable charted spaces is the product of two
`σ`-finite measures on the factors as soon as it agrees with the product measure on products
`s ×ˢ t` of measurable subsets of chart sources (`TauCeti.eq_prod_of_apply_prod_chart_source`):
countably many product chart sources cover `M × N`, and on each of them the two measures agree by
`MeasureTheory.Measure.prod_eq`. This is the localization step behind product formulas for
measures defined chart by chart, such as the measure of a top form or the Riemannian volume.

## Main results

* `TauCeti.eq_prod_of_apply_prod_chart_source`: a measure on `M × N` that agrees with `ν₁ ⊗ ν₂` on
  products of measurable subsets of chart sources is `ν₁ ⊗ ν₂`.
-/

public section

open MeasureTheory Set
open scoped Manifold

namespace TauCeti

section Measure

variable {H G M N : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace M]
  [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [MeasurableSpace M]
  [OpensMeasurableSpace M] [MeasurableSpace N] [OpensMeasurableSpace N]
  [SecondCountableTopology M] [SecondCountableTopology N]

/-- **A product measure is determined on products of chart pieces.** Let `ν₁` and `ν₂` be
`σ`-finite measures on second countable charted spaces `M` and `N`. A measure `μ` on `M × N` with
`μ (s ×ˢ t) = ν₁ s * ν₂ t` for all measurable subsets `s` and `t` of chart sources is the product
measure `ν₁ ⊗ ν₂`. -/
theorem eq_prod_of_apply_prod_chart_source {μ : Measure (M × N)} {ν₁ : Measure M}
    {ν₂ : Measure N} [SigmaFinite ν₁] [SigmaFinite ν₂]
    (h : ∀ (α : M) (β : N) (s : Set M) (t : Set N), MeasurableSet s → MeasurableSet t →
      s ⊆ (chartAt H α).source → t ⊆ (chartAt G β).source → μ (s ×ˢ t) = ν₁ s * ν₂ t) :
    μ = ν₁.prod ν₂ := by
  -- Both measures are determined by their restrictions to countably many product chart sources.
  obtain ⟨T, hT, hcover⟩ := LindelofSpace.elim_nhds_subcover
    (fun q : M × N ↦ (chartAt H q.1).source ×ˢ (chartAt G q.2).source) fun q ↦
      prod_mem_nhds (chart_source_mem_nhds H q.1) (chart_source_mem_nhds G q.2)
  refine Measure.ext_of_biUnion_eq_univ hT hcover fun q _ ↦ ?_
  have hU := (chartAt H q.1).open_source.measurableSet
  have hV := (chartAt G q.2).open_source.measurableSet
  rw [← Measure.prod_restrict]
  refine (Measure.prod_eq fun s t hs ht ↦ ?_).symm
  rw [Measure.restrict_apply (hs.prod ht), prod_inter_prod, Measure.restrict_apply hs,
    Measure.restrict_apply ht]
  exact h q.1 q.2 _ _ (hs.inter hU) (ht.inter hV) inter_subset_right inter_subset_right

end Measure

end TauCeti
