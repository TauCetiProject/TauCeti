/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Components
import TauCeti.Topology.LocallyConnected

/-!
# Connected neighborhoods in locally semialgebraic sets

A set semialgebraic near one of its points has arbitrarily small connected semialgebraic
relative open neighborhoods of that point. Consequently every locally semialgebraic set,
with its subspace topology, is locally connected. Neither closedness nor local compactness
of the set is assumed.

The neighborhoods are components of semialgebraic local restrictions, not intersections
with global components: those intersections need not be connected. Their finiteness makes
each local component relatively open. This supplies connected neighborhood bases even at
points on lower-dimensional or singular parts of a set.

## References

* J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Springer, 1998,
  Section 2.4 (topology of semialgebraic sets).
-/

public section

open Filter Set Topology

namespace TauCeti

variable {σ : Type*} [Finite σ] {s V : Set (σ → ℝ)} {x : σ → ℝ}

/-- Near a point of a locally semialgebraic set, any relative neighborhood contains a
connected semialgebraic neighborhood that is open in the set. Only semialgebraicity at
the center is needed. -/
theorem SemialgebraicAt.exists_isConnected_mem_nhdsWithin (hs : SemialgebraicAt s x)
    (hx : x ∈ s) (hV : V ∈ 𝓝[s] x) :
    ∃ C, C ∈ 𝓝[s] x ∧ C ⊆ s ∩ V ∧ IsConnected C ∧ IsSemialgebraic C ∧
      IsOpen ((Subtype.val : s → (σ → ℝ)) ⁻¹' C) := by
  obtain ⟨W, hW, hWV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hV
  obtain ⟨U, hUo, hxU, hUW, _, hsU⟩ := hs.exists_subset hW
  have hfin := hsU.finite_image_connectedComponentIn
  have hCT := connectedComponentIn_subset (s ∩ U) x
  exact ⟨connectedComponentIn (s ∩ U) x,
    hfin.connectedComponentIn_inter_mem_nhdsWithin hx (hUo.mem_nhds hxU),
    fun y hy ↦ ⟨(hCT hy).1, hWV ⟨hUW (hCT hy).2, (hCT hy).1⟩⟩,
    isConnected_connectedComponentIn_iff.2 ⟨hx, hxU⟩,
    hsU.connectedComponentIn x,
    hfin.isOpen_preimage_connectedComponentIn_inter hUo x⟩

/-- The relative neighborhood filter at a semialgebraic point of a set has a basis of
connected semialgebraic sets open in the subspace. -/
theorem SemialgebraicAt.nhdsWithin_hasBasis_isConnected (hs : SemialgebraicAt s x)
    (hx : x ∈ s) :
    (𝓝[s] x).HasBasis
      (fun C : Set (σ → ℝ) ↦ x ∈ C ∧ C ⊆ s ∧ IsConnected C ∧ IsSemialgebraic C ∧
        IsOpen ((Subtype.val : s → (σ → ℝ)) ⁻¹' C)) id := by
  refine ⟨fun V ↦ ⟨fun hV ↦ ?_, ?_⟩⟩
  · obtain ⟨C, hCn, hCV, hc, hsa, ho⟩ := hs.exists_isConnected_mem_nhdsWithin hx hV
    exact ⟨C, ⟨mem_of_mem_nhdsWithin hx hCn, hCV.trans inter_subset_left, hc, hsa, ho⟩,
      hCV.trans inter_subset_right⟩
  · rintro ⟨C, ⟨hxC, _, _, _, ho⟩, hCV⟩
    have hn : (Subtype.val : s → (σ → ℝ)) ⁻¹' C ∈ 𝓝 (⟨x, hx⟩ : s) :=
      ho.mem_nhds hxC
    have hCn : C ∈ 𝓝[s] x := by
      rw [← map_nhds_subtypeVal (⟨x, hx⟩ : s)]
      exact hn
    exact mem_of_superset hCn hCV

/-- Every locally semialgebraic set is locally connected in its subspace topology.
This includes the empty set and finite coordinate spaces of dimension zero. -/
theorem IsLocallySemialgebraic.locallyConnectedSpace (hs : IsLocallySemialgebraic s) :
    LocallyConnectedSpace s :=
  locallyConnectedSpace_subtype_iff_nhdsWithin.2 fun x hx _ hV ↦ by
    obtain ⟨C, hCn, hCV, hc, _, _⟩ :=
      (hs.semialgebraicAt x).exists_isConnected_mem_nhdsWithin hx hV
    exact ⟨C, hCn, hCV, hc.isPreconnected⟩

end TauCeti
