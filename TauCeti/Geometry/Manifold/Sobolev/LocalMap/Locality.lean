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
exactly when it holds on each of them. This is what allows membership to be checked near each
point, for instance in a single pair of charts around it, and local solutions of equations on
Sobolev maps, such as the weak pseudoholomorphic equation, to be glued along open covers.

## Main results

* `TauCeti.memWkpLocMapOn_iff_locally`, `TauCeti.memWkpLocMap_iff_locally`: the class is local on
  the surface.
* `TauCeti.memWkpLocMapOn_iSup_iff`: the sheaf property for open covers.

## Implementation notes

The model vector space `F` of `I : ModelWithCorners ℝ F H`, in which the coordinate expressions
`ψ.extend I ∘ u ∘ φ⁻¹` take values, is assumed complete, as for the planar locality theorem
`TauCeti.memWkpLoc_iff_locally`.
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
  · intro x hx
    obtain ⟨t, ht, hut⟩ := h x hx
    exact (hut.continuousOn x (mem_of_mem_nhdsWithin hx ht)).mono_of_mem_nhdsWithin ht
  · refine memWkpLoc_iff_locally.2 fun z hz ↦ ?_
    obtain ⟨t, ht, hut⟩ := h _ hz.2.1
    exact ⟨_, φ.target_inter_preimage_symm_mem_nhdsWithin hz.1 ht, hut.memWkpLoc_chart hφ hψ⟩

/-- **Locality on the whole surface.** A map is a local Sobolev map exactly when every point
has a neighbourhood on which it is one. -/
theorem memWkpLocMap_iff_locally :
    MemWkpLocMap I p k u ↔ ∀ x, ∃ t ∈ 𝓝 x, MemWkpLocMapOn I p k u t := by
  simp [← memWkpLocMapOnGroupoid_univ, memWkpLocMapOn_iff_locally (s := univ)]

/-- **The sheaf property.** A map is a local Sobolev map on a union of open sets exactly when it
is one on each of them. -/
theorem memWkpLocMapOn_iSup_iff {ι : Type*} (W : ι → Opens X) :
    MemWkpLocMapOn I p k u (⨆ i, W i : Opens X) ↔ ∀ i, MemWkpLocMapOn I p k u (W i) := by
  refine ⟨fun h i ↦ h.mono (SetLike.coe_subset_coe.2 (le_iSup W i)), fun h ↦ ?_⟩
  refine memWkpLocMapOn_iff_locally.2 fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := mem_iUnion.1 (by simpa only [Opens.coe_iSup] using hx)
  exact ⟨W i, mem_nhdsWithin_of_mem_nhds ((W i).isOpen.mem_nhds hi), h i⟩

end TauCeti
