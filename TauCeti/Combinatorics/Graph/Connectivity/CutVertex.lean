/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Component

import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.Combinatorics.Graph.Connectivity.Walk.Decomposition
import TauCeti.Combinatorics.Graph.Connectivity.Walk.Maps

/-!
# Cut vertices of multigraphs

A vertex of a multigraph is a cut vertex when deleting it separates two other vertices that were
previously reachable.  This definition is insensitive to loops and parallel edges, but is phrased
in the native walk-based connectivity API for `Graph`.

The map `Graph.deleteVertexComponentMap` sends each component after deleting a vertex to its
original component.  A vertex is a cut vertex exactly when this map is not injective.  With the
relevant component types finite, this gives the component-count characterization
`Graph.isCutVertex_iff_componentCount_lt_componentCount_deleteVerts`: deleting a cut vertex
increases the number of connected components, while deleting a non-cut vertex does not increase
it.

The definition follows R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173,
Springer, 2017, Section 1.4; the other characterizations are proved here.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G : Graph α β} {u v w : α}

/-! ### Definition and component map -/

/-- A vertex is a cut vertex if deleting it separates two other vertices that were reachable in
the original graph. -/
def IsCutVertex (G : Graph α β) (v : α) : Prop :=
  ∃ u w, u ≠ v ∧ w ≠ v ∧ G.Reachable u w ∧ ¬(G.deleteVerts {v}).Reachable u w

/-- The reachability characterization of a cut vertex. -/
theorem isCutVertex_def : G.IsCutVertex v ↔
    ∃ u w, u ≠ v ∧ w ≠ v ∧ G.Reachable u w ∧ ¬(G.deleteVerts {v}).Reachable u w :=
  Iff.rfl

/-- The map from components after deleting `v` to components of the original graph. -/
noncomputable def deleteVertexComponentMap (G : Graph α β) (v : α) :
    (G.deleteVerts {v}).ConnectedComponent → G.ConnectedComponent :=
  ConnectedComponent.mapOfLE deleteVerts_le

/-- The component of a vertex after deletion maps to its component in the original graph. -/
@[simp]
theorem deleteVertexComponentMap_connectedComponentOf (G : Graph α β) (v x : α)
    (hx : x ∈ V(G.deleteVerts {v})) :
    G.deleteVertexComponentMap v ((G.deleteVerts {v}).connectedComponentOf x hx) =
      G.connectedComponentOf x (deleteVerts_le.vertexSet_mono hx) :=
  ConnectedComponent.mapOfLE_connectedComponentOf deleteVerts_le hx

/-- A vertex is a cut vertex exactly when two components created by its deletion map to the same
original component. -/
theorem isCutVertex_iff_not_injective_deleteVertexComponentMap :
    G.IsCutVertex v ↔ ¬Function.Injective (G.deleteVertexComponentMap v) := by
  constructor
  · rintro ⟨u, w, huv, hwv, huw, hdel⟩ hinj
    have hu' : u ∈ V(G.deleteVerts {v}) := by simp [huv, huw.left_mem]
    have hw' : w ∈ V(G.deleteVerts {v}) := by simp [hwv, huw.right_mem]
    have hmap : G.deleteVertexComponentMap v
        ((G.deleteVerts {v}).connectedComponentOf u hu') =
        G.deleteVertexComponentMap v
          ((G.deleteVerts {v}).connectedComponentOf w hw') := by
      rw [deleteVertexComponentMap_connectedComponentOf,
        deleteVertexComponentMap_connectedComponentOf,
        connectedComponentOf_eq_connectedComponentOf_iff]
      exact huw
    have hcomp := hinj hmap
    exact hdel ((connectedComponentOf_eq_connectedComponentOf_iff hu' hw').mp hcomp)
  · intro hninj
    obtain ⟨C, D, hmap, hCD⟩ := Function.not_injective_iff.mp hninj
    obtain ⟨u, huC⟩ := C.property.nonempty
    obtain ⟨w, hwD⟩ := D.property.nonempty
    have hu' : u ∈ V(G.deleteVerts {v}) := C.property.le.vertexSet_mono huC
    have hw' : w ∈ V(G.deleteVerts {v}) := D.property.le.vertexSet_mono hwD
    have hu := C.eq_connectedComponentOf huC
    have hw := D.eq_connectedComponentOf hwD
    refine ⟨u, w, ?_, ?_, ?_, ?_⟩
    · have h : u ∈ V(G) ∧ u ≠ v := by
        simpa only [vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff] using hu'
      exact h.2
    · have h : w ∈ V(G) ∧ w ≠ v := by
        simpa only [vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff] using hw'
      exact h.2
    · rw [hu, hw, deleteVertexComponentMap_connectedComponentOf,
        deleteVertexComponentMap_connectedComponentOf,
        connectedComponentOf_eq_connectedComponentOf_iff] at hmap
      exact hmap
    · intro huw
      apply hCD
      rw [hu, hw, connectedComponentOf_eq_connectedComponentOf_iff]
      exact huw

/-- The component map after deleting `v` is surjective if another vertex is reachable from
`v`. -/
theorem deleteVertexComponentMap_surjective
    (h : ∃ u, u ≠ v ∧ G.Reachable u v) :
    Function.Surjective (G.deleteVertexComponentMap v) := by
  obtain ⟨u, huv, huvReach⟩ := h
  intro C
  obtain ⟨z, hzC⟩ := C.property.nonempty
  have hzG : z ∈ V(G) := C.property.le.vertexSet_mono hzC
  by_cases hzv : z = v
  · subst z
    have hu' : u ∈ V(G.deleteVerts {v}) := by simp [huv, huvReach.left_mem]
    refine ⟨(G.deleteVerts {v}).connectedComponentOf u hu', ?_⟩
    rw [deleteVertexComponentMap_connectedComponentOf]
    apply ConnectedComponent.eq_of_mem_of_mem
    · rw [mem_vertexSet_connectedComponentOf_iff]
      exact huvReach
    · exact hzC
  · have hz' : z ∈ V(G.deleteVerts {v}) := by simp [hzv, hzG]
    refine ⟨(G.deleteVerts {v}).connectedComponentOf z hz', ?_⟩
    rw [deleteVertexComponentMap_connectedComponentOf]
    exact ConnectedComponent.eq_of_mem_of_mem
      (mem_vertexSet_connectedComponentOf_self hzG) hzC

/-- A cut vertex is reachable from one of the two vertices it separates. -/
theorem IsCutVertex.exists_ne_and_reachable (h : G.IsCutVertex v) :
    ∃ u, u ≠ v ∧ G.Reachable u v := by
  obtain ⟨u, w, huv, -, huw, hdel⟩ := h
  refine huw.elim fun p ↦ ?_
  have hvp : v ∈ p.support := by
    by_contra hvp
    apply hdel
    exact reachable_deleteVerts_iff_exists_walk.mpr
      ⟨p, huw.left_mem, fun z hz hzv ↦ hvp (hzv ▸ hz)⟩
  obtain ⟨q, r, hp⟩ := Walk.mem_support_iff_exists_append.mp hvp
  exact ⟨u, huv, q.reachable huw.left_mem⟩

/-- A cut vertex is an actual vertex of the graph. -/
theorem IsCutVertex.mem_vertexSet (h : G.IsCutVertex v) : v ∈ V(G) :=
  h.exists_ne_and_reachable.choose_spec.2.right_mem

/-! ### Component counts -/

private theorem finite_connectedComponent_of_finite_deleteVerts_singleton
    [Finite (G.deleteVerts {v}).ConnectedComponent] : Finite G.ConnectedComponent := by
  classical
  by_cases hv : v ∈ V(G)
  · let f : Option (G.deleteVerts {v}).ConnectedComponent → G.ConnectedComponent
      | none => G.connectedComponentOf v hv
      | some C => G.deleteVertexComponentMap v C
    apply Finite.of_surjective f
    intro C
    obtain ⟨z, hzC⟩ := C.property.nonempty
    have hzG : z ∈ V(G) := C.property.le.vertexSet_mono hzC
    by_cases hzv : z = v
    · subst z
      refine ⟨none, ?_⟩
      exact ConnectedComponent.eq_of_mem_of_mem
        (mem_vertexSet_connectedComponentOf_self hv) hzC
    · have hz' : z ∈ V(G.deleteVerts {v}) := by simp [hzG, hzv]
      refine ⟨some ((G.deleteVerts {v}).connectedComponentOf z hz'), ?_⟩
      change G.deleteVertexComponentMap v
        ((G.deleteVerts {v}).connectedComponentOf z hz') = C
      rw [deleteVertexComponentMap_connectedComponentOf]
      exact ConnectedComponent.eq_of_mem_of_mem
        (mem_vertexSet_connectedComponentOf_self hzG) hzC
  · apply Finite.of_surjective (G.deleteVertexComponentMap v)
    intro C
    obtain ⟨z, hzC⟩ := C.property.nonempty
    have hzG : z ∈ V(G) := C.property.le.vertexSet_mono hzC
    have hzv : z ≠ v := fun hzv ↦ hv (hzv ▸ hzG)
    have hz' : z ∈ V(G.deleteVerts {v}) := by simp [hzG, hzv]
    refine ⟨(G.deleteVerts {v}).connectedComponentOf z hz', ?_⟩
    rw [deleteVertexComponentMap_connectedComponentOf]
    exact ConnectedComponent.eq_of_mem_of_mem
      (mem_vertexSet_connectedComponentOf_self hzG) hzC

/-- **Cut vertices by component counts.** If deletion leaves finitely many components, a vertex is
a cut vertex exactly when deleting it strictly increases the number of connected components. -/
theorem isCutVertex_iff_componentCount_lt_componentCount_deleteVerts
    [Finite (G.deleteVerts {v}).ConnectedComponent] :
    G.IsCutVertex v ↔ G.componentCount < (G.deleteVerts {v}).componentCount := by
  let _ : Finite G.ConnectedComponent :=
    finite_connectedComponent_of_finite_deleteVerts_singleton (G := G) (v := v)
  rw [isCutVertex_iff_not_injective_deleteVertexComponentMap, componentCount_def,
    componentCount_def]
  let f := G.deleteVertexComponentMap v
  constructor
  · intro hninj
    have hcut := isCutVertex_iff_not_injective_deleteVertexComponentMap.mpr hninj
    have hsurj : Function.Surjective f :=
      deleteVertexComponentMap_surjective hcut.exists_ne_and_reachable
    have hle := Nat.card_le_card_of_surjective f hsurj
    exact lt_of_le_of_ne hle fun hcard ↦
      hninj ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hcard.symm⟩).1
  · intro hlt hinj
    exact (not_le_of_gt hlt) (Nat.card_le_card_of_injective f hinj)

/-- Deleting a non-cut vertex cannot increase the number of connected components. -/
theorem componentCount_deleteVerts_singleton_le_of_not_isCutVertex
    [Finite G.ConnectedComponent]
    (h : ¬G.IsCutVertex v) :
    (G.deleteVerts {v}).componentCount ≤ G.componentCount := by
  rw [componentCount_def, componentCount_def]
  have hinj : Function.Injective (G.deleteVertexComponentMap v) := by
    by_contra hninj
    exact h (isCutVertex_iff_not_injective_deleteVertexComponentMap.mpr hninj)
  let _ : Finite (G.deleteVerts {v}).ConnectedComponent :=
    Finite.of_injective (G.deleteVertexComponentMap v) hinj
  exact Nat.card_le_card_of_injective (G.deleteVertexComponentMap v) hinj

end Graph
