/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Sobolev.LocalMap
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Locality of local Sobolev maps from a Riemann surface

The class `TauCeti.MemWkpLocMapOn I p k u s` of local Sobolev maps from a Riemann surface `X`
into a manifold `M` has the sheaf property in the set `s ⊆ X`: it holds on `s` exactly when every
point of `s` has a relative neighbourhood in `s` on which it holds, and on a union of open sets
exactly when it holds on each of them.

## Main results

* `TauCeti.memWkpLocMapOn_iff_locally`: the class is local on the surface.
* `TauCeti.memWkpLocMapOn_iSup_iff`: the sheaf property for open covers.

## Implementation notes

Continuity glues by `continuousOn_of_locally_continuousOn`. For a holomorphic chart `φ` and a
chart `ψ` of `M`, the coordinate domain over `s` is covered by the coordinate domains over the
relative neighbourhoods, which are relative neighbourhoods of its points
(`OpenPartialHomeomorph.target_inter_preimage_symm_mem_nhdsWithin`); the planar class glues
by `TauCeti.memWkpLoc_iff_locally`. The target space `F` of the charts of `M` is assumed complete,
as for the planar locality theorem.
-/

public section

open Set Filter TopologicalSpace
open scoped Manifold Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {p : ENNReal} {k : ℕ} {u : X → M} {s : Set X}

/-- **Locality.** A map is a local Sobolev map on `s` exactly when every point of `s` has a
neighbourhood within `s` on which it is one. -/
theorem memWkpLocMapOn_iff_locally :
    MemWkpLocMapOn I p k u s ↔ ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, MemWkpLocMapOn I p k u t := by
  refine ⟨fun h _ _ ↦ ⟨s, self_mem_nhdsWithin, h⟩,
    fun h ↦ memWkpLocMapOn_iff.2 ⟨?_, fun φ hφ ψ hψ ↦ ?_⟩⟩
  · refine continuousOn_of_locally_continuousOn fun x hx ↦ ?_
    obtain ⟨t, ht, hut⟩ := h x hx
    obtain ⟨O, hO, hxO, hOt⟩ := mem_nhdsWithin.1 ht
    exact ⟨O, hO, hxO, hut.continuousOn.mono fun y hy ↦ hOt ⟨hy.2, hy.1⟩⟩
  · refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
    obtain ⟨t, ht, hut⟩ := h _ hz.2.1
    exact ⟨_, φ.target_inter_preimage_symm_mem_nhdsWithin hz ht, hut.memWkpLoc_chart hφ hψ⟩

/-- **The sheaf property.** A map is a local Sobolev map on a union of open sets exactly when it
is one on each of them. -/
theorem memWkpLocMapOn_iSup_iff {ι : Type*} (W : ι → Opens X) :
    MemWkpLocMapOn I p k u (⨆ i, W i : Opens X) ↔ ∀ i, MemWkpLocMapOn I p k u (W i) := by
  refine ⟨fun h i ↦ h.mono (SetLike.coe_subset_coe.2 (le_iSup W i)), fun h ↦ ?_⟩
  refine memWkpLocMapOn_iff_locally.2 fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := mem_iUnion.1 (by simpa only [Opens.coe_iSup] using hx)
  exact ⟨W i, mem_nhdsWithin_of_mem_nhds ((W i).isOpen.mem_nhds hi), h i⟩

end TauCeti
