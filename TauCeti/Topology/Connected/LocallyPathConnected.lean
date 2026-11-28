/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Separation.Regular

/-!
# Compact connected sets in locally path-connected spaces; locality and retracts

In a locally compact, locally path-connected R1 space (for instance a Hausdorff one), a compact
subset `K` of a preconnected open set `U` is enclosed by a compact preconnected `L` with
`K ⊆ interior L` and `L ⊆ U`. This is the connected refinement of Mathlib's
`exists_compact_between`.

Plane separation arguments use it to replace finitely many points, or a compact set, of a
connected open region by a single compact connected set inside the region: gluing continuous
logarithms along that set needs exactly its connectedness, and gluing along closed sets needs
its compactness.

Local path-connectedness is a local property: a space in which every point has a neighbourhood
that is locally path-connected as a subspace is locally path-connected. It also passes to
retracts, since a retraction with a continuous section is a quotient map.

## Main results

* `TauCeti.exists_isCompact_isPreconnected_between` — a compact preconnected set between a
  compact set and a preconnected open set containing it.
* `LocallyPathConnectedSpace.of_forall_exists_mem_nhds` — local path-connectedness is local.
* `Function.LeftInverse.locallyPathConnectedSpace` — a retract of a locally path-connected space
  is locally path-connected.
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- **A compact connected set between a compact set and a connected open set.** In a locally
compact, locally path-connected R1 space, if the compact set `K` lies in the preconnected
open set `U`, then some compact preconnected `L` satisfies `K ⊆ interior L` and `L ⊆ U`. -/
theorem exists_isCompact_isPreconnected_between [R1Space X] [LocallyCompactSpace X]
    [LocallyPathConnectedSpace X] {K U : Set X} (hK : IsCompact K) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hKU : K ⊆ U) :
    ∃ L, IsCompact L ∧ IsPreconnected L ∧ K ⊆ interior L ∧ L ⊆ U := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨∅, isCompact_empty, isPreconnected_empty, empty_subset _, empty_subset _⟩
  -- `L` is a finite union of closures of path components of `interior M`, for a compact closed
  -- `M` between `K` and `U`, each joined to `x₀` by a path in `U`
  obtain ⟨M, hM, hMc, hKM, hMU⟩ := exists_compact_closed_between hK hU hKU
  have hUp : IsPathConnected U :=
    hU.isConnected_iff_isPathConnected.mp ⟨⟨x₀, hKU hx₀⟩, hUc⟩
  -- every point of `K` is joined to `x₀` by a compact connected set inside `U`
  have hjoin : ∀ x ∈ K, ∃ S : Set X, IsCompact S ∧ IsPreconnected S ∧ x₀ ∈ S ∧ x ∈ S ∧ S ⊆ U :=
    fun x hx =>
      let γ := (hUp.joinedIn _ (hKU hx₀) _ (hKU hx)).somePath
      ⟨range γ, isCompact_range γ.continuous, isPreconnected_range γ.continuous,
        ⟨0, γ.source⟩, ⟨1, γ.target⟩, range_subset_iff.mpr (JoinedIn.somePath_mem _)⟩
  choose! S hSc hSp hS₀ hSx hSU using hjoin
  -- the path components of `interior M` through the points of `K` are open, so finitely many
  -- of them cover `K`
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun x => pathComponentIn (interior M) x)
    fun x hx => (isOpen_interior.pathComponentIn x).mem_nhds (mem_pathComponentIn_self (hKM hx))
  have hclM : ∀ x, closure (pathComponentIn (interior M) x) ⊆ M := fun x =>
    closure_minimal (pathComponentIn_subset.trans interior_subset) hMc
  set piece : X → Set X := fun x => closure (pathComponentIn (interior M) x) ∪ S x
  refine ⟨⋃₀ (piece '' t), ?_, ?_, ?_, ?_⟩
  · refine (t.finite_toSet.image piece).isCompact_sUnion ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (hM.of_isClosed_subset isClosed_closure (hclM x)).union (hSc x (htK x hx))
  · refine isPreconnected_sUnion x₀ _ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact Or.inr (hS₀ x (htK x hx))
    · rintro _ ⟨x, hx, rfl⟩
      have hxM : x ∈ interior M := hKM (htK x hx)
      exact (isPathConnected_pathComponentIn hxM).isConnected.isPreconnected.closure.union x
        (subset_closure (mem_pathComponentIn_self hxM)) (hSx x (htK x hx)) (hSp x (htK x hx))
  · intro z hz
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hcover hz)
    refine interior_mono ?_ ((isOpen_interior.pathComponentIn x).interior_eq.symm ▸ hzx)
    exact (subset_closure.trans subset_union_left).trans
      (subset_sUnion_of_mem (mem_image_of_mem piece hx))
  · rintro z ⟨_, ⟨x, hx, rfl⟩, hz⟩
    exact hz.elim (fun hz => hMU (hclM x hz)) fun hz => hSU x (htK x hx) hz

end TauCeti

section Locality

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Local path-connectedness is local.** A space in which every point has a neighbourhood that
is locally path-connected as a subspace is locally path-connected. -/
theorem LocallyPathConnectedSpace.of_forall_exists_mem_nhds
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, LocallyPathConnectedSpace U) : LocallyPathConnectedSpace X where
  path_connected_basis x := by
    obtain ⟨U, hU, _⟩ := h x
    rw [Filter.hasBasis_self]
    intro t ht
    obtain ⟨s, ⟨hs, hsc⟩, hst : s ⊆ _⟩ := (path_connected_basis
      (⟨x, mem_of_mem_nhds hU⟩ : U)).mem_iff.1
      (continuous_subtypeVal.continuousAt.preimage_mem_nhds ht)
    exact ⟨(↑) '' s, map_nhds_subtypeVal_eq_nhds (mem_of_mem_nhds hU) hU ▸ Filter.image_mem_map hs,
      hsc.image continuous_subtypeVal, image_subset_iff.2 hst⟩

/-- **A retract of a locally path-connected space is locally path-connected.** The retraction
`r` has the continuous section `s`, so it is a quotient map. -/
theorem Function.LeftInverse.locallyPathConnectedSpace [LocallyPathConnectedSpace Y] {s : X → Y}
    {r : Y → X} (h : Function.LeftInverse r s) (hr : Continuous r) (hs : Continuous s) :
    LocallyPathConnectedSpace X :=
  (IsQuotientMap.of_inverse hs hr h).locallyPathConnectedSpace

end Locality
