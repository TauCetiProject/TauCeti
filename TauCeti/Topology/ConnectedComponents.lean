/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Irreducible
public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.Topology.PathComponent
public import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Connected components

This file records general topological properties of connected components, and of the quotient of a
space by them.

## Main declarations

* `Homeomorph.image_connectedComponent`: a homeomorphism maps a connected component onto
  the connected component of the image point.
* `TauCeti.frontier_connectedComponentIn_subset_compl`: in a locally connected space, a connected
  component of an open set has its frontier in the complement of that set.
* `TauCeti.connectedComponentIn_eq_of_lt`: a preconnected set on which a function stays on one
  side of a value it never takes is a connected component.
* `TauCeti.isPreconnected_compl_of_isPreconnected_frontier`: in a preconnected, locally connected
  space, an open set with preconnected frontier has preconnected complement.
* `TauCeti.instT1SpaceConnectedComponents`: the connected-components quotient of any topological
  space is a T1 space.
* `TauCeti.connectedComponentsSigmaHomeomorph`: a locally connected space is homeomorphic
  to the disjoint union of its connected components.
* `TauCeti.finite_connectedComponents_of_finite_irreducibleComponents`: finiteness of the
  irreducible components implies finiteness of the connected components.
* `TauCeti.natCard_connectedComponents_eq_of_iUnion_eq_univ`: a space covered by finitely many
  pairwise disjoint closed connected sets has exactly as many connected components as sets.
-/

public section

open Function Set Topology

universe u

variable {X : Type u} [TopologicalSpace X]

namespace Homeomorph

/-- A homeomorphism maps a connected component onto the connected component of the image point. -/
@[simp]
theorem image_connectedComponent {Y : Type*} [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    e '' connectedComponent x = connectedComponent (e x) := by
  simpa only [connectedComponentIn_univ, _root_.Set.image_univ_of_surjective e.surjective] using
    e.image_connectedComponentIn (s := _root_.Set.univ) (x := x) (_root_.Set.mem_univ x)

end Homeomorph

namespace TauCeti

/-- **The frontier of a connected component of an open set misses the set.** Equivalently,
`frontier (connectedComponentIn F x) ∩ F = ∅`: the component is clopen in `F`. -/
theorem frontier_connectedComponentIn_subset_compl [LocallyConnectedSpace X] {F : Set X}
    (hF : IsOpen F) (x : X) : frontier (connectedComponentIn F x) ⊆ Fᶜ := by
  intro y hy hyF
  have hC : IsOpen (connectedComponentIn F x) := hF.connectedComponentIn
  obtain ⟨z, hzy, hzx⟩ :=
    mem_closure_iff.mp hy.1 _ hF.connectedComponentIn (mem_connectedComponentIn hyF)
  have hyC : y ∈ connectedComponentIn F x := by
    rw [connectedComponentIn_eq hzx, ← connectedComponentIn_eq hzy]
    exact mem_connectedComponentIn hyF
  exact hy.2 (by rwa [hC.interior_eq])

/-- **A strict superlevel set cuts out a connected component.** Let `φ` be continuous on `D` and
never equal to `c` there. A preconnected subset `H ⊆ D` containing every point of `D` where `φ`
exceeds `c` is the connected component in `D` of any of its points `z` with `c < φ z`: by the
intermediate value theorem, that component cannot reach a point where `φ` is below `c`. -/
theorem connectedComponentIn_eq_of_lt {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] {D H : Set X} {z : X} {φ : X → α} {c : α} (hH : IsPreconnected H)
    (hHD : H ⊆ D) (hz : z ∈ H) (hzc : c < φ z) (hφ : ContinuousOn φ D)
    (hDne : ∀ q ∈ D, φ q ≠ c) (hmem : ∀ q ∈ D, c < φ q → q ∈ H) :
    connectedComponentIn D z = H := by
  apply Subset.antisymm
  · intro q hq
    have hqD : q ∈ D := connectedComponentIn_subset D z hq
    apply hmem q hqD
    rcases lt_or_gt_of_ne (hDne q hqD) with hqlt | hqgt
    · have hzC : z ∈ connectedComponentIn D z := mem_connectedComponentIn (hHD hz)
      obtain ⟨p, hpC, hpc⟩ := isPreconnected_connectedComponentIn.intermediate_value hq hzC
        (hφ.mono (connectedComponentIn_subset D z)) ⟨hqlt.le, hzc.le⟩
      exact (hDne p (connectedComponentIn_subset D z hpC) hpc).elim
    · exact hqgt
  · exact hH.subset_connectedComponentIn hz hHD

/-- **An open set with preconnected frontier has preconnected complement**, in a preconnected,
locally connected space.

Openness is needed: in `ℝ` the frontier of `{0}` is `{0}`, while `{0}ᶜ` is disconnected. -/
theorem isPreconnected_compl_of_isPreconnected_frontier [LocallyConnectedSpace X]
    [PreconnectedSpace X] {U : Set X} (hU : IsOpen U) (hf : IsPreconnected (frontier U)) :
    IsPreconnected Uᶜ := by
  -- If `frontier U` is nonempty, each nonempty component `D` of the exterior `(closure U)ᶜ`
  -- reaches `frontier U` through its own frontier: a frontier point of `D` lies in `closure U`
  -- but, being a limit of exterior points, not in the open set `U`. So `frontier U ∪ D` is
  -- preconnected, and `Uᶜ` is the union of these sets, all of which contain `frontier U`.
  rcases (frontier U).eq_empty_or_nonempty with h | ⟨p, hp⟩
  · rcases frontier_eq_empty_iff.mp h with rfl | rfl
    · simpa using isPreconnected_univ
    · simpa using isPreconnected_empty
  have hpiece : ∀ y, IsPreconnected (frontier U ∪ connectedComponentIn (closure U)ᶜ y) := by
    intro y
    set D := connectedComponentIn (closure U)ᶜ y
    rcases D.eq_empty_or_nonempty with hD | hD
    · simpa [hD] using hf
    have hDu : D ≠ univ := fun h =>
      connectedComponentIn_subset _ _ (h ▸ mem_univ p : p ∈ D) hp.1
    obtain ⟨q, hq⟩ := nonempty_frontier_iff.mpr ⟨hD, hDu⟩
    have hqU : q ∈ frontier U := by
      refine ⟨?_, ?_⟩
      · simpa using frontier_connectedComponentIn_subset_compl isClosed_closure.isOpen_compl y hq
      · rw [hU.interior_eq]
        intro hqU
        obtain ⟨z, hzU, hzD⟩ := mem_closure_iff.mp hq.1 U hU hqU
        exact connectedComponentIn_subset _ _ hzD (subset_closure hzU)
    have hins : IsPreconnected (insert q D) :=
      isPreconnected_connectedComponentIn.subset_closure (subset_insert q D)
        (insert_subset hq.1 subset_closure)
    have := hf.union' ⟨q, hqU, mem_insert q D⟩ hins
    rwa [union_insert, insert_eq_of_mem (mem_union_left D hqU)] at this
  have hcover : Uᶜ = ⋃ y, frontier U ∪ connectedComponentIn (closure U)ᶜ y := by
    refine Subset.antisymm (fun x hx => mem_iUnion.mpr ⟨x, ?_⟩) (iUnion_subset fun y => ?_)
    · by_cases hxc : x ∈ closure U
      · exact Or.inl (hU.frontier_eq ▸ ⟨hxc, hx⟩)
      · exact Or.inr (mem_connectedComponentIn hxc)
    · refine union_subset (hU.frontier_eq ▸ fun x hx => hx.2) fun x hx hxU => ?_
      exact connectedComponentIn_subset _ _ hx (subset_closure hxU)
  rw [hcover]
  exact isPreconnected_iUnion ⟨p, mem_iInter.mpr fun _ => Or.inl hp⟩ hpiece

/-- The quotient of a topological space by its connected components is a T1 space. -/
instance instT1SpaceConnectedComponents : T1Space (ConnectedComponents X) :=
  ⟨fun c => by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [← ConnectedComponents.isQuotientMap_coe.isClosed_preimage,
      connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent⟩

/-- A fibre of the quotient to connected components is path-connected when the ambient space is
locally path-connected. -/
instance instPathConnectedSpaceConnectedComponentsFiber [LocallyPathConnectedSpace X]
    (C : ConnectedComponents X) :
    PathConnectedSpace (ConnectedComponents.mk ⁻¹' {C} : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [connectedComponents_preimage_singleton, ← pathComponent_eq_connectedComponent]
  infer_instance

/-- A fibre of the quotient to connected components is locally path-connected when the ambient
space is locally path-connected. -/
instance instLocallyPathConnectedSpaceConnectedComponentsFiber [LocallyPathConnectedSpace X]
    (C : ConnectedComponents X) :
    LocallyPathConnectedSpace (ConnectedComponents.mk ⁻¹' {C} : Set X) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe C
  rw [connectedComponents_preimage_singleton, ← pathComponent_eq_connectedComponent]
  infer_instance

/-- **A locally connected space is the disjoint union of its connected components.**

The summand indexed by `C : ConnectedComponents X` is the fibre of the canonical quotient map
over `C`, so this decomposition does not require choosing representatives. -/
noncomputable def connectedComponentsSigmaHomeomorph [LocallyConnectedSpace X] :
    (Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) ≃ₜ X := by
  let e : (Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) ≃ X :=
    Equiv.sigmaPreimageEquiv ConnectedComponents.mk
  exact e.toHomeomorphOfContinuousOpen
    (continuous_sigma fun _ ↦ continuous_subtype_val)
    (isOpenMap_sigma.mpr fun C ↦
      ((isOpen_discrete {C}).preimage ConnectedComponents.continuous_coe).isOpenMap_subtype_val)

@[simp]
theorem connectedComponentsSigmaHomeomorph_apply [LocallyConnectedSpace X]
    (z : Σ C : ConnectedComponents X, (ConnectedComponents.mk ⁻¹' {C} : Set X)) :
    connectedComponentsSigmaHomeomorph z = z.2 :=
  (rfl)

@[simp]
theorem connectedComponentsSigmaHomeomorph_symm_apply [LocallyConnectedSpace X] (x : X) :
    connectedComponentsSigmaHomeomorph.symm x =
      ⟨ConnectedComponents.mk x, ⟨x, Set.mem_singleton _⟩⟩ :=
  (rfl)

/-- A space with finitely many irreducible components has finitely many connected components. -/
theorem finite_connectedComponents_of_finite_irreducibleComponents
    (h : (irreducibleComponents X).Finite) : Finite (ConnectedComponents X) := by
  let C : Set (ConnectedComponents X) :=
    ⋃ Z ∈ irreducibleComponents X, ConnectedComponents.mk '' Z
  have hC : C.Finite := h.biUnion fun Z hZ =>
    Set.Subsingleton.finite <| by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [ConnectedComponents.coe_eq_coe']
      exact hZ.1.isConnected.isPreconnected.subset_connectedComponent hy hx
  apply Finite.of_finite_univ
  rw [← Set.eq_univ_of_forall]
  · exact hC
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact Set.mem_biUnion (irreducibleComponent_mem_irreducibleComponents x)
      ⟨x, mem_irreducibleComponent, rfl⟩

/-- A space covered by finitely many pairwise disjoint closed connected sets has exactly as many
connected components as sets: the sets are its connected components. -/
theorem natCard_connectedComponents_eq_of_iUnion_eq_univ {ι : Type*} [Finite ι] {U : ι → Set X}
    (hclosed : ∀ i, IsClosed (U i)) (hdisj : Pairwise (Disjoint on U))
    (hunion : ⋃ i, U i = univ) (hconn : ∀ i, IsConnected (U i)) :
    Nat.card (ConnectedComponents X) = Nat.card ι := by
  -- Each set is open, its complement being the finite union of the other sets.
  have hclopen (i : ι) : IsClopen (U i) := by
    refine ⟨hclosed i, ?_⟩
    have : (U i)ᶜ = ⋃ j : {j // j ≠ i}, U j := by
      ext x
      obtain ⟨k, hk⟩ := mem_iUnion.1 (hunion ▸ mem_univ x)
      simp only [mem_compl_iff, mem_iUnion, Subtype.exists, exists_prop]
      refine ⟨fun hx ↦ ⟨k, fun h ↦ hx (h ▸ hk), hk⟩, ?_⟩
      rintro ⟨j, hji, hj⟩ hi
      exact disjoint_left.1 (hdisj hji) hj hi
    rw [← isClosed_compl_iff, this]
    exact isClosed_iUnion_of_finite fun j ↦ hclosed j
  have (i : ι) : Unique (ConnectedComponents (U i)) :=
    have := isPreconnected_iff_preconnectedSpace.1 (hconn i).isPreconnected
    have := (hconn i).nonempty.to_subtype
    uniqueOfSubsingleton (ConnectedComponents.mk (Classical.arbitrary _))
  exact Nat.card_congr ((ConnectedComponents.equivOfIsClopen hclopen hdisj hunion).trans
    (Equiv.sigmaUnique ι _))

end TauCeti
