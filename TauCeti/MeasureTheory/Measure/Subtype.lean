/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

import TauCeti.MeasureTheory.Measure.Comap

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
* For `s ⊆ t` with `t` measurable, pulling back from `α` to `t` and then along
  `Set.inclusion hst` to `s` recovers the direct pullback to `s`.
* Pulling `μ` back to a measurable subtype of `μ`-mass `1` yields a probability measure
  (`MeasureTheory.Measure.isProbabilityMeasure_comap_subtype`).
* Local finiteness and finiteness on compact sets pass from `μ` to `μ.comap (Subtype.val)` for
  every subtype `Subtype p`, with no measurability or separation assumptions; in particular, if `s`
  is σ-compact and `μ` is finite on compacts, `μ.comap ((↑) : s → α)` is σ-finite
  (`IsSigmaCompact.sigmaFinite_comap`).
* Inner regularity for compact sets on sets of finite measure (`InnerRegularCompactLTTop`) passes
  from `μ` to `μ.comap ((↑) : s → α)` for every measurable set `s`.
* `μ.comap ((↑) : s → α)` is finite when `μ s` is, so a locally finite measure pulls back to a
  finite measure on every bounded interval, and a measure charging every nonempty open set pulls
  back to one on every open interval.
* For a measurable set `s`, `Prod.map id (↑)` carries `μ.prod (ν.comap (↑))` on `α × s` to the
  restriction of `μ.prod ν` to `univ ×ˢ s`.
* On a measurable conull set `s`, `μ.comap (↑)` gives each preimage `(↑) ⁻¹' B` the mass `μ B`, so
  a map between measurable conull sets preserving the pulled-back measures extends to a
  measure-preserving map of the whole spaces.

## Main declarations

* `MeasurableSet.measurableEmbedding_inclusion`: `Set.inclusion hst : s → t` is a measurable
  embedding when `s` is measurable in `α`.
* `MeasureTheory.Measure.comap_preimage_le`: `(μ.comap f) (f ⁻¹' v) ≤ μ v` for measurable `f`.
* `MeasureTheory.Measure.comap_inclusion_comap_subtype_coe`: compatibility of `Measure.comap` along
  nested subtypes `s ⊆ t` with `t` measurable.
* `MeasureTheory.Measure.isProbabilityMeasure_comap_subtype`: pulling `μ` back to a measurable
  subtype of `μ`-mass `1` yields a probability measure.
* `MeasureTheory.Measure.isFiniteMeasure_comap_subtype_coe`: finiteness of `μ.comap ((↑) : s → α)`
  when `μ s < ∞`.
* `MeasureTheory.Measure.instIsLocallyFiniteMeasureComapSubtype`,
  `MeasureTheory.Measure.instIsFiniteMeasureOnCompactsComapSubtype`: local finiteness and finiteness
  on compact sets for `μ.comap (Subtype.val)`.
* `IsSigmaCompact.sigmaFinite_comap`: σ-finiteness of `μ.comap ((↑) : s → α)` on σ-compact `s`.
* `MeasureTheory.Measure.InnerRegularCompactLTTop.comap_subtype_coe`: compact inner regularity on
  finite-measure sets for `μ.comap ((↑) : s → α)` when `s` is measurable.
* `MeasureTheory.Measure.instIsFiniteMeasureComapSubtypeIoo`, `...Ico`, `...Ioc`: finiteness of the
  pullback of a locally finite measure to a bounded interval (the closed case `[a, b]` follows from
  compactness and `instIsFiniteMeasureOnCompactsComapSubtype`).
* `MeasureTheory.Measure.instIsOpenPosMeasureComapSubtypeIoo`: the pullback to an open interval of
  a measure charging every nonempty open set charges every nonempty open set.
* `MeasureTheory.measurePreserving_prodMap_subtype_coe`: the inclusion `α × s → α × β` is
  measure preserving from `μ.prod (ν.comap (↑))` to `(μ.prod ν).restrict (univ ×ˢ s)`.
* `MeasureTheory.comap_subtypeVal_preimage_of_conull`: on a measurable conull set `s`,
  `μ.comap (↑) ((↑) ⁻¹' B) = μ B`.
* `MeasureTheory.MeasurePreserving.extend_subtypeVal`: extending a map between measurable conull
  sets that preserves the pulled-back measures gives a measure-preserving map of the whole spaces.
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

/-- Pulling `μ` back to a measurable subtype `t` and then along `Set.inclusion hst` to a subset
`s ⊆ t` agrees with pulling `μ` back directly to `s`. -/
theorem comap_inclusion_comap_subtype_coe {s t : Set α} (ht : MeasurableSet t) (hst : s ⊆ t)
    (μ : Measure α) :
    (μ.comap ((↑) : t → α)).comap (Set.inclusion hst) = μ.comap ((↑) : s → α) :=
  (MeasurableEmbedding.subtypeVal ht).comap_comap (Set.inclusion hst) μ

/-- Pulling a measure `μ` back to a measurable subtype `{x // p x}` of mass `1` yields a
probability measure. -/
theorem isProbabilityMeasure_comap_subtype {p : α → Prop} (hp : MeasurableSet {x | p x})
    (μ : Measure α) (hμ : μ {x | p x} = 1) :
    IsProbabilityMeasure (μ.comap (Subtype.val : Subtype p → α)) :=
  ⟨((MeasurableEmbedding.subtypeVal hp).comap_apply μ univ).trans
    (by rw [Subtype.coe_image_univ, hμ])⟩

/-- Pulling `μ` back to a subtype `s` of finite measure yields a finite measure, with no
measurability assumption on `s`. -/
theorem isFiniteMeasure_comap_subtype_coe (μ : Measure α) {s : Set α} (hs : μ s ≠ ∞) :
    IsFiniteMeasure (μ.comap ((↑) : s → α)) :=
  ⟨by
    convert (comap_preimage_le measurable_subtypeVal μ s).trans_lt hs.lt_top
    exact (eq_univ_of_forall Subtype.prop).symm⟩

end Measurable

section Topological

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] {μ : Measure α}

/-- Pulling a locally finite measure back to any subtype yields a locally finite measure. -/
instance instIsLocallyFiniteMeasureComapSubtype (μ : Measure α) [IsLocallyFiniteMeasure μ]
    (p : α → Prop) : IsLocallyFiniteMeasure (μ.comap (Subtype.val : Subtype p → α)) where
  finiteAtNhds x := by
    obtain ⟨v, hv, hμv⟩ := μ.finiteAt_nhds (x : α)
    exact ⟨Subtype.val ⁻¹' v, continuous_subtypeVal.continuousAt hv,
      (comap_preimage_le measurable_subtypeVal μ v).trans_lt hμv⟩

/-- Pulling a measure that is finite on compact sets back to any subtype yields a measure that is
finite on compact sets. -/
instance instIsFiniteMeasureOnCompactsComapSubtype (μ : Measure α) [IsFiniteMeasureOnCompacts μ]
    (p : α → Prop) : IsFiniteMeasureOnCompacts (μ.comap (Subtype.val : Subtype p → α)) where
  lt_top_of_isCompact K hK :=
    ((measure_mono (subset_preimage_image Subtype.val K)).trans
      (comap_preimage_le measurable_subtypeVal μ _)).trans_lt
      (hK.image continuous_subtypeVal).measure_lt_top

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
  refine ⟨InnerRegularCompactLTTop.innerRegular.comap (MeasurableEmbedding.subtypeVal hs)
    (fun U hU ↦ ⟨(MeasurableEmbedding.subtypeVal hs).measurableSet_image' hU.1, ?_⟩)
    (fun K hKrange hK ↦ IsInducing.subtypeVal.isCompact_preimage' hK hKrange)⟩
  rw [← comap_subtypeVal_apply hs]
  exact hU.2

end Topological

section Interval

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [Preorder α] (μ : Measure α)
  (a b : α)

/-- Pulling a locally finite measure back to a bounded open interval yields a finite measure. -/
instance instIsFiniteMeasureComapSubtypeIoo [CompactIccSpace α] [IsLocallyFiniteMeasure μ] :
    IsFiniteMeasure (μ.comap ((↑) : Ioo a b → α)) :=
  isFiniteMeasure_comap_subtype_coe μ measure_Ioo_lt_top.ne

/-- Pulling a locally finite measure back to a bounded half-open interval `[a, b)` yields a finite
measure. -/
instance instIsFiniteMeasureComapSubtypeIco [CompactIccSpace α] [IsLocallyFiniteMeasure μ] :
    IsFiniteMeasure (μ.comap ((↑) : Ico a b → α)) :=
  isFiniteMeasure_comap_subtype_coe μ measure_Ico_lt_top.ne

/-- Pulling a locally finite measure back to a bounded half-open interval `(a, b]` yields a finite
measure. -/
instance instIsFiniteMeasureComapSubtypeIoc [CompactIccSpace α] [IsLocallyFiniteMeasure μ] :
    IsFiniteMeasure (μ.comap ((↑) : Ioc a b → α)) :=
  isFiniteMeasure_comap_subtype_coe μ measure_Ioc_lt_top.ne

/-- Pulling a measure that charges every nonempty open set back to an open interval yields a
measure that charges every nonempty open set. -/
instance instIsOpenPosMeasureComapSubtypeIoo {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    [LinearOrder α] [OrderClosedTopology α] [BorelSpace α] (μ : Measure α) [IsOpenPosMeasure μ]
    (a b : α) : (μ.comap ((↑) : Ioo a b → α)).IsOpenPosMeasure :=
  .comap μ isOpen_Ioo.isOpenEmbedding_subtypeVal

end Interval

end MeasureTheory.Measure

namespace MeasureTheory

/-- For a measurable set `s`, the inclusion `Prod.map id (↑) : α × s → α × β` carries the product
of `μ` with the pullback of `ν` to `s` to the restriction of `μ.prod ν` to `univ ×ˢ s`. -/
theorem measurePreserving_prodMap_subtype_coe {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] {s : Set β}
    (hs : MeasurableSet s) :
    MeasurePreserving (Prod.map id ((↑) : s → β)) (μ.prod (ν.comap (↑)))
      ((μ.prod ν).restrict (univ ×ˢ s)) := by
  have := (MeasurePreserving.id μ).prod (measurePreserving_subtypeVal (μa := ν) hs)
  rwa [← Measure.prod_restrict, Measure.restrict_univ]

section Conull

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {s : Set α} {t : Set β}

/-- On a measurable conull set `s`, the pullback of `μ` to `s` gives the preimage of any set `B` the
mass `μ B`. -/
theorem comap_subtypeVal_preimage_of_conull (hs : MeasurableSet s) (hμs : μ sᶜ = 0) (B : Set α) :
    μ.comap ((↑) : s → α) ((↑) ⁻¹' B) = μ B := by
  rw [comap_subtypeVal_apply hs, Subtype.image_preimage_coe, inter_comm, measure_inter_conull hμs]

/-- Extending a map between measurable conull sets that preserves the pulled-back measures by a
measurable map off the source gives a measure-preserving map of the whole spaces. -/
theorem MeasurePreserving.extend_subtypeVal {g : s → t}
    (hg : MeasurePreserving g (μ.comap (↑)) (ν.comap (↑))) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hμs : μ sᶜ = 0) (hνt : ν tᶜ = 0) {j : α → β} (hj : Measurable j) :
    MeasurePreserving (Function.extend (↑) (fun x ↦ (g x : β)) j) μ ν := by
  set F : α → β := Function.extend (↑) (fun x ↦ (g x : β)) j
  have hF : Measurable F := (MeasurableEmbedding.subtypeVal hs).measurable_extend
    (measurable_subtypeVal.comp hg.measurable) hj
  refine ⟨hF, Measure.ext fun B hB ↦ ?_⟩
  have hFg : ((↑) : s → α) ⁻¹' (F ⁻¹' B) = g ⁻¹' ((↑) ⁻¹' B) := by
    rw [← preimage_comp, Function.extend_comp Subtype.val_injective]
    rfl
  rw [Measure.map_apply hF hB, ← comap_subtypeVal_preimage_of_conull hs hμs, hFg,
    hg.measure_preimage (measurable_subtypeVal hB).nullMeasurableSet,
    comap_subtypeVal_preimage_of_conull ht hνt]

end Conull

end MeasureTheory
