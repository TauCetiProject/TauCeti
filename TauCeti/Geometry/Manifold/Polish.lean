/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# The Lusin–Souslin theorem on charted spaces

Mathlib's Lusin–Souslin theorem says that a map which is continuous and injective on a measurable
subset of a Polish space has measurable image. Reading a map in charts, this file extends it to
maps out of a charted space `M` modelled on a Polish space, with its Borel measurable space, into
a charted space `N` modelled on a Hausdorff space, in which open sets are measurable: within a
chart source, and, when `M` is a Lindelöf space, globally.

## Main results

* `MeasurableSet.image_of_continuousOn_injOn_chartAt`: a map continuous and injective on a
  measurable subset of a chart source, with image in a chart source, has measurable image.
* `MeasurableSet.image_of_continuousOn_injOn_chartedSpace`: a map out of a Lindelöf charted space
  which is continuous and injective on a measurable set has measurable image.
-/

public section

variable {H : Type*} [TopologicalSpace H] [PolishSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M]
  {H' : Type*} [TopologicalSpace H'] [T2Space H'] {N : Type*}
  [TopologicalSpace N] [ChartedSpace H' N] [MeasurableSpace N] [OpensMeasurableSpace N]

/-- **Lusin–Souslin theorem in charts.** Let `M` be a charted space modelled on a Polish space, with
its Borel measurable space, and let `N` be a charted space modelled on a Hausdorff space, in which
open sets are measurable. A map `M → N` which is continuous and injective on a measurable subset
`s` of the chart source at `α`, and maps `s` into the chart source at `β`, sends `s` to a measurable
set. -/
theorem MeasurableSet.image_of_continuousOn_injOn_chartAt {Φ : M → N} {α : M} {β : N}
    {s : Set M} (hs : MeasurableSet s) (hcont : ContinuousOn Φ s) (hinj : Set.InjOn Φ s)
    (hsα : s ⊆ (chartAt H α).source) (hsβ : Set.MapsTo Φ s (chartAt H' β).source) :
    MeasurableSet (Φ '' s) := by
  -- Work with the Borel measurable spaces of the two models and of `N`.
  let : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace H' := borel H'
  have : BorelSpace H' := ⟨rfl⟩
  refine OpensMeasurableSpace.borel_le _ ?_
  let : MeasurableSpace N := borel N
  have : BorelSpace N := ⟨rfl⟩
  set e := chartAt H α
  set e' := chartAt H' β
  -- Read `Φ` in the two charts: `g` is continuous and injective on the coordinate image of `s`,
  -- which is measurable, so its image, the coordinate image of `Φ '' s`, is measurable.
  let g := e' ∘ Φ ∘ e.symm
  have hmaps : Set.MapsTo e.symm (e '' s) s := by
    rintro _ ⟨x, hx, rfl⟩
    rwa [e.left_inv (hsα hx)]
  have htarget : e '' s ⊆ e.target := (Set.image_mono hsα).trans e.image_source_eq_target.subset
  have hes : MeasurableSet (e '' s) := by
    rw [← Set.inter_eq_left.mpr hsα, ← Set.image_domRestrict]
    exact e.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image'
      (measurable_subtype_coe hs)
  have himage : g '' (e '' s) = e' '' (Φ '' s) := by
    simp only [g, Set.image_image]
    exact Set.image_congr fun x hx ↦ by simp only [Function.comp_apply, e.left_inv (hsα hx)]
  have hgs : MeasurableSet (e' '' (Φ '' s)) := himage ▸ hes.image_of_continuousOn_injOn
    (e'.continuousOn.comp (hcont.comp (e.continuousOn_symm.mono htarget) hmaps) (hsβ.comp hmaps))
    ((e'.injOn.comp hinj hsβ).comp (e.symm.injOn.mono htarget) hmaps)
  -- Carry it back to `N` along the inverse chart at `β`.
  have htarget' : e' '' (Φ '' s) ⊆ e'.symm.source :=
    (Set.image_mono hsβ.image_subset).trans e'.image_source_eq_target.subset
  have hback : e'.symm '' (e' '' (Φ '' s)) = Φ '' s :=
    e'.symm_image_image_of_subset_source hsβ.image_subset
  rw [← hback, ← Set.inter_eq_left.mpr htarget', ← Set.image_domRestrict]
  exact e'.symm.isOpenEmbedding_restrict.measurableEmbedding.measurableSet_image'
    (measurable_subtype_coe hgs)

variable (H H') in
include H H' in
/-- **Lusin–Souslin theorem on charted spaces.** Let `M` be a Lindelöf charted space modelled on a
Polish space, with its Borel measurable space, and let `N` be a charted space modelled on a
Hausdorff space, in which open sets are measurable. A map `M → N` which is continuous and injective
on a measurable set `s` sends `s` to a measurable set. The models only serve to read the map in
charts, so they are explicit arguments. -/
theorem MeasurableSet.image_of_continuousOn_injOn_chartedSpace [LindelofSpace M]
    {Φ : M → N} {s : Set M} (hs : MeasurableSet s) (hcont : ContinuousOn Φ s)
    (hinj : Set.InjOn Φ s) : MeasurableSet (Φ '' s) := by
  -- `M` is second countable, so countably many open sets `U x`, each in the chart source at
  -- `x ∈ s` and mapped by `Φ` (on `s`) into the chart source at `Φ x`, cover `s`; apply the
  -- theorem in charts on each piece.
  have := ChartedSpace.secondCountable_of_lindelof H M
  have h (x : M) (hx : x ∈ s) :
      ∃ u, IsOpen u ∧ x ∈ u ∧ u ∩ s ⊆ Φ ⁻¹' (chartAt H' (Φ x)).source :=
    mem_nhdsWithin.1 ((hcont x hx).preimage_mem_nhdsWithin (chart_source_mem_nhds H' (Φ x)))
  choose! u hu hxu hus using h
  let U (x : M) : Set M := (chartAt H x).source ∩ u x
  obtain ⟨T, hTc, hTs, hcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_nhds_subcover U
    fun x hx ↦ ((chartAt H x).open_source.inter (hu x hx)).mem_nhds ⟨mem_chart_source H x, hxu x hx⟩
  rw [← Set.inter_eq_left.2 hcover, Set.inter_iUnion₂, Set.image_iUnion₂]
  exact .biUnion hTc fun x hx ↦ (hs.inter ((chartAt H x).open_source.inter
    (hu x (hTs x hx))).measurableSet).image_of_continuousOn_injOn_chartAt (α := x) (β := Φ x)
    (hcont.mono Set.inter_subset_left) (hinj.mono Set.inter_subset_left)
    (Set.inter_subset_right.trans Set.inter_subset_left) fun y hy ↦ hus x (hTs x hx) ⟨hy.2.2, hy.1⟩
