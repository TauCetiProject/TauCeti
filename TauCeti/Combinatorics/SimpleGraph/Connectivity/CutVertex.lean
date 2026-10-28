/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import TauCeti.Combinatorics.Graph.Connectivity.CutVertex

/-!
# Cut vertices of simple graphs

A vertex of a simple graph is a cut vertex when deleting it separates two vertices that were
previously connected. The predicate is defined through the native multigraph cut-vertex API for
`Graph.ofSimpleGraph`.
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
