/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Pullbacks of measures to subtypes

For a subset `s : Set α` (or any predicate `p : α → Prop`), the pullback
`μ.comap ((↑) : s → α)` views the ambient measure `μ` as a measure on the subtype `s` itself rather
than on `α` via `μ.restrict s`. Working on the subtype `s` is essential when `s` carries structure
of its own — for instance when `s` is an open subgroup `H` of a topological group `G`, so that `H`
is a topological group in its own right and `μ.comap (↑)` is a Haar measure on `H`.

This file records the basic functoriality, finiteness, σ-finiteness, and inner-regularity properties
of `μ.comap (↑)`:

* For any measurable map `f`, `(μ.comap f) (f ⁻¹' v) ≤ μ v` with no measurability assumption on `v`
  or injectivity assumption on `f` (`MeasureTheory.Measure.comap_preimage_le`).
* For nested measurable sets `s ⊆ t`, pulling back from `α` to `t` and then along
  `Set.inclusion hst` to `s` recovers the direct pullback to `s`.
* Local finiteness and finiteness on compact sets pass from `μ` to `μ.comap (Subtype.val)` for
  every subtype `Subtype p`, with no measurability or separation assumptions; in particular, if `s`
  is σ-compact and `μ` is finite on compacts, `μ.comap ((↑) : s → α)` is σ-finite
  (`IsSigmaCompact.sigmaFinite_comap`).
* Inner regularity for compact sets on sets of finite measure (`InnerRegularCompactLTTop`) passes
  from `μ` to `μ.comap ((↑) : s → α)` for every measurable set `s`.

## Main declarations

* `MeasurableSet.measurableEmbedding_inclusion`: `Set.inclusion hst : s → t` is a measurable
  embedding when `s` is measurable in `α`.
* `MeasureTheory.Measure.comap_preimage_le`: `(μ.comap f) (f ⁻¹' v) ≤ μ v` for measurable `f`.
* `MeasureTheory.Measure.comap_inclusion_comap_subtype_coe`: compatibility of `Measure.comap` along
  nested measurable subtypes `s ⊆ t`.
* `MeasureTheory.Measure.instIsLocallyFiniteMeasureComapSubtype`,
  `MeasureTheory.Measure.instIsFiniteMeasureOnCompactsComapSubtype`: local finiteness and finiteness
  on compact sets for `μ.comap (Subtype.val)`.
* `IsSigmaCompact.sigmaFinite_comap`: σ-finiteness of `μ.comap ((↑) : s → α)` on σ-compact `s`.
* `MeasureTheory.Measure.InnerRegularCompactLTTop.comap_subtype_coe`: compact inner regularity on
  finite-measure sets for `μ.comap ((↑) : s → α)` when `s` is measurable.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

/-- For a measurable set `s ⊆ t`, the inclusion `Set.inclusion hst : s → t` is a measurable
embedding. No measurability assumption on `t` is needed. -/
theorem MeasurableSet.measurableEmbedding_inclusion {α : Type*} [MeasurableSpace α]
    {s t : Set α} (hs : MeasurableSet s) (hst : s ⊆ t) :
    MeasurableEmbedding (Set.inclusion hst) :=
  ⟨Set.inclusion_injective hst, measurable_inclusion hst, fun _ hu ↦ hs.image_inclusion hst hu⟩

namespace MeasureTheory.Measure

section Measurable

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- For any measurable map `f`, the pullback measure of `f ⁻¹' v` is bounded by `μ v`, with no
measurability assumption on `v` or injectivity assumption on `f`. -/
theorem comap_preimage_le {f : α → β} (hf : Measurable f) (μ : Measure β) (v : Set β) :
    (μ.comap f) (f ⁻¹' v) ≤ μ v := by
  have hT : MeasurableSet (f ⁻¹' toMeasurable μ v) := hf (measurableSet_toMeasurable μ v)
  exact (measure_mono (preimage_mono (subset_toMeasurable μ v))).trans <|
    ((comap_apply_le f μ hT.nullMeasurableSet).trans
      (measure_mono (image_preimage_subset f _))).trans_eq (measure_toMeasurable v)

/-- Pulling `μ` back to a measurable subtype `t` and then along `Set.inclusion hst` to a measurable
subset `s ⊆ t` agrees with pulling `μ` back directly to `s`. -/
theorem comap_inclusion_comap_subtype_coe {s t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : s ⊆ t) (μ : Measure α) :
    (μ.comap ((↑) : t → α)).comap (Set.inclusion hst) = μ.comap ((↑) : s → α) :=
  comap_comap (hs.measurableEmbedding_inclusion hst).measurableSet_image' Subtype.coe_injective
    (MeasurableEmbedding.subtype_coe ht).measurableSet_image' μ

end Measurable

section Topological

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] {μ : Measure α}

/-- Pulling a locally finite measure back to any subtype yields a locally finite measure. -/
instance instIsLocallyFiniteMeasureComapSubtype (μ : Measure α) [IsLocallyFiniteMeasure μ]
    (p : α → Prop) : IsLocallyFiniteMeasure (μ.comap (Subtype.val : Subtype p → α)) where
  finiteAtNhds x := by
    obtain ⟨v, hv, hμv⟩ := μ.finiteAt_nhds (x : α)
    exact ⟨Subtype.val ⁻¹' v, continuous_subtype_val.continuousAt hv,
      (comap_preimage_le measurable_subtype_coe μ v).trans_lt hμv⟩

/-- Pulling a measure that is finite on compact sets back to any subtype yields a measure that is
finite on compact sets. -/
instance instIsFiniteMeasureOnCompactsComapSubtype (μ : Measure α) [IsFiniteMeasureOnCompacts μ]
    (p : α → Prop) : IsFiniteMeasureOnCompacts (μ.comap (Subtype.val : Subtype p → α)) where
  lt_top_of_isCompact K hK :=
    ((measure_mono (subset_preimage_image Subtype.val K)).trans
      (comap_preimage_le measurable_subtype_coe μ _)).trans_lt
      (hK.image continuous_subtype_val).measure_lt_top

/-- A measure that is finite on compact sets pulls back to a σ-finite measure on every σ-compact
set, with no separation or measurability assumptions on the ambient space. -/
theorem _root_.IsSigmaCompact.sigmaFinite_comap [IsFiniteMeasureOnCompacts μ] {s : Set α}
    (hs : IsSigmaCompact s) : SigmaFinite (μ.comap ((↑) : s → α)) := by
  have := isSigmaCompact_iff_sigmaCompactSpace.1 hs
  infer_instance

/-- Pulling a measure with `InnerRegularCompactLTTop` back to a measurable subtype preserves
`InnerRegularCompactLTTop`. -/
theorem InnerRegularCompactLTTop.comap_subtype_coe [μ.InnerRegularCompactLTTop] {s : Set α}
    (hs : MeasurableSet s) : (μ.comap ((↑) : s → α)).InnerRegularCompactLTTop := by
  refine ⟨InnerRegularCompactLTTop.innerRegular.comap (MeasurableEmbedding.subtype_coe hs)
    (fun U hU ↦ ⟨(MeasurableEmbedding.subtype_coe hs).measurableSet_image' hU.1, ?_⟩)
    (fun K hKrange hK ↦ IsInducing.subtypeVal.isCompact_preimage' hK hKrange)⟩
  rw [← comap_subtype_coe_apply hs]
  exact hU.2

end Topological

end MeasureTheory.Measure
