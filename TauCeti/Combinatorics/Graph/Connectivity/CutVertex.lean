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
original component.  A vertex is a cut vertex exactly when this map is not injective.  When the
actual vertex set is finite, this gives the component-count characterization
`Graph.isCutVertex_iff_componentCount_lt`: deleting a cut vertex increases the number of connected
components, while deleting a non-cut vertex does not increase it.

These are the standard equivalent definitions of an articulation vertex; see R. Diestel,
*Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017, Section 3.1.
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
def deleteVertexComponentMap (G : Graph α β) (v : α) :
    (G.deleteVerts {v}).toSimpleGraph.ConnectedComponent →
      G.toSimpleGraph.ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map (toSimpleGraphHomOfLE deleteVerts_le)

/-- The component of a vertex after deletion maps to its component in the original graph. -/
@[simp]
theorem deleteVertexComponentMap_connectedComponentMk (G : Graph α β) (v : α)
    (z : V(G.deleteVerts {v})) :
    G.deleteVertexComponentMap v ((G.deleteVerts {v}).toSimpleGraph.connectedComponentMk z) =
      G.toSimpleGraph.connectedComponentMk
        ⟨z, deleteVerts_le.vertexSet_mono z.2⟩ := by
  rw [deleteVertexComponentMap, SimpleGraph.ConnectedComponent.map_mk,
    toSimpleGraph_connectedComponentMk_eq_iff]
  simpa only [coe_toSimpleGraphHomOfLE_apply] using
    Reachable.refl (deleteVerts_le.vertexSet_mono z.2)

/-- A vertex is a cut vertex exactly when two components created by its deletion map to the same
original component. -/
theorem isCutVertex_iff_not_injective_deleteVertexComponentMap :
    G.IsCutVertex v ↔ ¬Function.Injective (G.deleteVertexComponentMap v) := by
  constructor
  · rintro ⟨u, w, huv, hwv, huw, hdel⟩ hinj
    let u' : V(G.deleteVerts {v}) := ⟨u, by simp [huv, huw.left_mem]⟩
    let w' : V(G.deleteVerts {v}) := ⟨w, by simp [hwv, huw.right_mem]⟩
    have hmap : G.deleteVertexComponentMap v
        ((G.deleteVerts {v}).toSimpleGraph.connectedComponentMk u') =
        G.deleteVertexComponentMap v
          ((G.deleteVerts {v}).toSimpleGraph.connectedComponentMk w') := by
      rw [deleteVertexComponentMap_connectedComponentMk,
        deleteVertexComponentMap_connectedComponentMk,
        toSimpleGraph_connectedComponentMk_eq_iff]
      exact huw
    have hcomp := hinj hmap
    exact hdel (toSimpleGraph_connectedComponentMk_eq_iff.mp hcomp)
  · intro hninj
    obtain ⟨C, D, hmap, hCD⟩ := Function.not_injective_iff.mp hninj
    induction C using SimpleGraph.ConnectedComponent.ind with | h u' => ?_
    induction D using SimpleGraph.ConnectedComponent.ind with | h w' => ?_
    refine ⟨u', w', ?_, ?_, ?_, ?_⟩
    · have hu : (u' : α) ∈ V(G) ∧ (u' : α) ≠ v := by
        simpa only [vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff] using u'.2
      exact hu.2
    · have hw : (w' : α) ∈ V(G) ∧ (w' : α) ≠ v := by
        simpa only [vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff] using w'.2
      exact hw.2
    · exact (map_toSimpleGraphHomOfLE_connectedComponentMk_eq_map_iff deleteVerts_le).mp hmap
    · intro huw
      exact hCD (toSimpleGraph_connectedComponentMk_eq_iff.mpr huw)

/-- A cut vertex is reachable from one of the two vertices it separates. -/
theorem IsCutVertex.exists_ne_and_reachable (h : G.IsCutVertex v) :
    ∃ u, u ≠ v ∧ G.Reachable u v := by
  obtain ⟨u, w, huv, -, huw, hdel⟩ := h
  refine huw.elim fun p ↦ ?_
  have hvp : v ∈ p.support := by
    by_contra hvp
    apply hdel
    refine (p.transfer deleteVerts_le ?_).reachable (by simp [huw.left_mem, huv])
    intro e he
    obtain ⟨a, b, hab, q, r, rfl⟩ := Walk.mem_edges_iff_exists_append.mp he
    rw [edgeSet_deleteVerts]
    refine ⟨a, b, hab, ?_, ?_⟩
    · intro hav
      apply hvp
      subst a
      rw [Walk.support_append]
      exact List.mem_append_left _ q.end_mem_support
    · intro hbv
      apply hvp
      subst b
      rw [Walk.support_append]
      exact List.mem_append_right _ (by simp)
  obtain ⟨q, r, hp⟩ := Walk.mem_support_iff_exists_append.mp hvp
  exact ⟨u, huv, q.reachable huw.left_mem⟩

/-- A cut vertex is an actual vertex of the graph. -/
theorem IsCutVertex.mem_vertexSet (h : G.IsCutVertex v) : v ∈ V(G) :=
  h.exists_ne_and_reachable.choose_spec.2.right_mem

/-! ### Finite component counts -/

/-- **Cut vertices by component counts.** If the actual vertex set is finite, a vertex is a cut
vertex exactly when deleting it strictly increases the number of connected components. -/
theorem isCutVertex_iff_componentCount_lt [Finite V(G)] :
    G.IsCutVertex v ↔ G.componentCount < (G.deleteVerts {v}).componentCount := by
  rw [isCutVertex_iff_not_injective_deleteVertexComponentMap,
    componentCount_eq_natCard_toSimpleGraph, componentCount_eq_natCard_toSimpleGraph]
  let f := G.deleteVertexComponentMap v
  have : Finite V(G.deleteVerts {v}) :=
    Finite.of_injective (fun z : V(G.deleteVerts {v}) ↦
      (⟨z, deleteVerts_le.vertexSet_mono z.2⟩ : V(G))) fun _ _ h ↦ Subtype.ext (Subtype.mk.inj h)
  constructor
  · intro hninj
    have hcut := isCutVertex_iff_not_injective_deleteVertexComponentMap.mpr hninj
    obtain ⟨u, huv, huvReach⟩ := hcut.exists_ne_and_reachable
    have hsurj : Function.Surjective f := by
      intro C
      induction C using SimpleGraph.ConnectedComponent.ind with | h z => ?_
      by_cases hzv : (z : α) = v
      · let u' : V(G.deleteVerts {v}) := ⟨u, by simp [huv, huvReach.left_mem]⟩
        refine ⟨(G.deleteVerts {v}).toSimpleGraph.connectedComponentMk u', ?_⟩
        dsimp only [f]
        rw [deleteVertexComponentMap_connectedComponentMk,
          toSimpleGraph_connectedComponentMk_eq_iff]
        simpa only [hzv] using huvReach
      · let z' : V(G.deleteVerts {v}) := ⟨z, by simp [hzv, z.2]⟩
        refine ⟨(G.deleteVerts {v}).toSimpleGraph.connectedComponentMk z', ?_⟩
        dsimp only [f]
        rw [deleteVertexComponentMap_connectedComponentMk,
          toSimpleGraph_connectedComponentMk_eq_iff]
        exact Reachable.refl z.2
    have hle := Nat.card_le_card_of_surjective f hsurj
    exact lt_of_le_of_ne hle fun hcard ↦
      hninj ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hsurj, hcard.symm⟩).1
  · intro hlt hinj
    exact (not_le_of_gt hlt) (Nat.card_le_card_of_injective f hinj)

/-- Deleting a non-cut vertex cannot increase the number of connected components. -/
theorem componentCount_deleteVerts_singleton_le_of_not_isCutVertex [Finite V(G)]
    (h : ¬G.IsCutVertex v) :
    (G.deleteVerts {v}).componentCount ≤ G.componentCount := by
  rw [← not_lt, ← isCutVertex_iff_componentCount_lt]
  exact h

end Graph
