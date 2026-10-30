/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.CutVertex

import TauCeti.Combinatorics.Graph.Connectivity.Walk.Maps

/-!
# Cut vertices of simple graphs

A vertex of a simple graph is a cut vertex when deleting it separates two vertices that were
previously connected. The predicate is defined through the native multigraph cut-vertex API for
`Graph.ofSimpleGraph`, and `SimpleGraph.isCutVertex_iff_exists_forall_walk_mem_support` restates it
with walks of the simple graph itself: a cut vertex lies on every walk between two other mutually
reachable vertices.
-/

public section

open Set

universe u

namespace SimpleGraph

variable {V : Type u}

/-- A vertex of a simple graph is a cut vertex when deleting it separates two vertices that were
previously connected. -/
def IsCutVertex (G : SimpleGraph V) (v : V) : Prop :=
  (Graph.ofSimpleGraph G).IsCutVertex v

/-- The cut-vertex predicate for a simple graph is the native multigraph predicate after applying
`Graph.ofSimpleGraph`. -/
theorem isCutVertex_def (G : SimpleGraph V) (v : V) :
    G.IsCutVertex v ↔ (Graph.ofSimpleGraph G).IsCutVertex v :=
  Iff.rfl

/-- A vertex is a cut vertex exactly when it lies on every walk between some two other vertices
that are reachable from each other. -/
theorem isCutVertex_iff_exists_forall_walk_mem_support {G : SimpleGraph V} {v : V} :
    G.IsCutVertex v ↔
      ∃ u w, u ≠ v ∧ w ≠ v ∧ G.Reachable u w ∧ ∀ p : G.Walk u w, v ∈ p.support := by
  rw [isCutVertex_def, Graph.isCutVertex_def]
  simp only [reachable_ofSimpleGraph_iff, Graph.reachable_deleteVerts_iff_exists_walk,
    Set.mem_singleton_iff, not_exists, not_and, not_forall, not_not]
  refine exists₂_congr fun u w ↦ and_congr_right fun _ ↦ and_congr_right fun _ ↦
    and_congr_right fun _ ↦ ⟨fun h p ↦ ?_, fun h p _ ↦ ?_⟩
  · obtain ⟨z, hz, rfl⟩ := h p.toGraph (by simp)
    simpa using hz
  · exact ⟨v, by simpa using h p.toSimpleGraph, rfl⟩

/-- A graph induced on a singleton has no cut vertex. -/
theorem not_isCutVertex_induce_singleton (G : SimpleGraph V) (v : V)
    (w : ↑({v} : Set V)) :
    ¬(G.induce {v}).IsCutVertex w := by
  apply Graph.not_isCutVertex_of_compl_subsingleton
  intro x hx y hy
  apply Subtype.ext
  have hxv := x.property
  have hyv := y.property
  simp only [Set.mem_singleton_iff] at hxv hyv
  exact hxv.trans hyv.symm

/-- A graph induced on a pair of vertices has no cut vertex. -/
@[simp]
theorem not_isCutVertex_induce_pair (G : SimpleGraph V) (u v : V)
    (w : ↑({u, v} : Set V)) :
    ¬(G.induce {u, v}).IsCutVertex w := by
  apply Graph.not_isCutVertex_of_compl_subsingleton
  rintro ⟨x, hx⟩ ⟨-, hxw⟩ ⟨y, hy⟩ ⟨-, hyw⟩
  apply Subtype.ext
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · rcases w.property with hw | hw
    · exact (hxw (Set.mem_singleton_iff.mpr (Subtype.ext hw.symm))).elim
    · exact (hyw (Set.mem_singleton_iff.mpr (Subtype.ext hw.symm))).elim
  · rcases w.property with hw | hw
    · exact (hyw (Set.mem_singleton_iff.mpr (Subtype.ext hw.symm))).elim
    · exact (hxw (Set.mem_singleton_iff.mpr (Subtype.ext hw.symm))).elim
  · rfl

end SimpleGraph
