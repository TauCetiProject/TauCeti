/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Connectivity.Bond
public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.Basic
public import TauCeti.Combinatorics.Graph.Union
public import Mathlib.Tactic.FinCases

/-!
# A two-edge bond and a singleton bond in one multigraph

Two parallel edges, labelled `0` and `1`, join vertices `0` and `1`; a pendant edge,
labelled `2`, joins vertices `1` and `2`. The parallel pair is a bond, as is the
singleton pendant edge. In both cases we check connectivity of the two induced sides
and apply `Graph.Connected.isBond_edgeCut_iff`.

The cut at the middle vertex contains all three edges but is not a bond: its other
side is disconnected. The two-edge bond is not a minimum-cardinality nonempty cut,
so this example distinguishes inclusion minimality from cardinality minimality.
-/

public section

open Graph Set

namespace TauCeti.Examples.Bond

private theorem compatible :
    (Graph.banana (0 : Fin 3) 1 ({0, 1} : Set (Fin 3))).Compatible
      (Graph.banana 1 2 {2}) :=
  Graph.Compatible.of_disjoint_edgeSet (by simp)

/-- A pair of parallel edges followed by a pendant edge. -/
def graph : Graph (Fin 3) (Fin 3) := compatible.union

@[simp]
theorem vertexSet_graph : V(graph) = Set.univ := by
  ext x
  fin_cases x <;> simp [graph]

@[simp]
theorem edgeSet_graph : E(graph) = Set.univ := by
  ext e
  fin_cases e <;> simp [graph]

/-- The edge labels `0,1` have ends `0,1`, and edge `2` has ends `1,2`. -/
@[simp]
theorem graph_isLink (e x y : Fin 3) :
    graph.IsLink e x y ↔
      (e = 0 ∨ e = 1) ∧ s(x, y) = s(0, 1) ∨ e = 2 ∧ s(x, y) = s(1, 2) := by
  simp [graph]

private theorem reachable_one {S : Set (Fin 3)} (hS : 1 ∈ S) {x : Fin 3} (hx : x ∈ S) :
    (graph.induce S).Reachable x 1 := by
  fin_cases x <;> dsimp at hx
  · apply Graph.IsLink.reachable (e := 0)
    simp [hx, hS]
  · exact Graph.Reachable.refl hS
  · apply Graph.IsLink.reachable (e := 2)
    simp [hx, hS, Sym2.eq_swap]

private theorem connected_induce_of_one_mem {S : Set (Fin 3)} (hS : 1 ∈ S) :
    (graph.induce S).Connected := by
  refine Graph.connected_iff_forall_reachable.mpr ⟨⟨1, hS⟩, ?_⟩
  intro x y hx hy
  exact (reachable_one hS hx).trans (reachable_one hS hy).symm

/-- The whole graph is connected, including across the pendant edge. -/
theorem connected_graph : graph.Connected := by
  have h := connected_induce_of_one_mem (S := V(graph)) (by simp)
  simpa only [Graph.induce_vertexSet] using h

/-- The cut isolating vertex `0` consists of the parallel pair. -/
@[simp]
theorem edgeCut_zero : graph.edgeCut {0} = {0, 1} := by
  ext e
  simp only [Graph.mem_edgeCut_iff, graph_isLink]
  fin_cases e <;> decide

/-- The cut isolating vertex `2` consists of the pendant edge. -/
@[simp]
theorem edgeCut_two : graph.edgeCut {2} = {2} := by
  ext e
  simp only [Graph.mem_edgeCut_iff, graph_isLink]
  fin_cases e <;> decide

/-- The cut isolating the middle vertex contains every edge. -/
@[simp]
theorem edgeCut_one : graph.edgeCut {1} = Set.univ := by
  ext e
  simp only [Graph.mem_edgeCut_iff, graph_isLink]
  fin_cases e <;> decide

/-- The two sides of the parallel-pair cut are connected induced subgraphs. -/
theorem connected_sides_zero :
    (graph.induce {0}).Connected ∧ (graph.induce (V(graph) \ {0})).Connected := by
  exact ⟨Graph.connected_of_vertexSet_eq_singleton (Graph.vertexSet_induce _ _),
    connected_induce_of_one_mem (by simp)⟩

/-- The two sides of the pendant-edge cut are connected induced subgraphs. -/
theorem connected_sides_two :
    (graph.induce {2}).Connected ∧ (graph.induce (V(graph) \ {2})).Connected := by
  exact ⟨Graph.connected_of_vertexSet_eq_singleton (Graph.vertexSet_induce _ _),
    connected_induce_of_one_mem (by simp)⟩

/-- Both parallel edges together form an inclusion-minimal nonempty cut. -/
theorem isBond_parallel_pair : graph.IsBond {0, 1} := by
  rw [← edgeCut_zero]
  exact (connected_graph.isBond_edgeCut_iff (by simp)).mpr connected_sides_zero

/-- The pendant edge by itself forms an inclusion-minimal nonempty cut. -/
theorem isBond_pendant : graph.IsBond {2} := by
  rw [← edgeCut_two]
  exact (connected_graph.isBond_edgeCut_iff (by simp)).mpr connected_sides_two

/-- The pendant edge is a bridge, via the singleton-bond characterization. -/
theorem isBridge_pendant : graph.IsBridge 2 :=
  Graph.isBond_singleton_iff_isBridge.mp isBond_pendant

/-- Neither edge of the parallel pair is itself a bridge. -/
theorem not_isBridge_of_ne_two {e : Fin 3} (he : e ≠ 2) : ¬graph.IsBridge e := by
  fin_cases e
  · exact Graph.IsLink.not_isBridge_of_isLink_of_ne (f := 1) (x := 0) (y := 1)
      (by simp) (by simp) (by decide)
  · exact Graph.IsLink.not_isBridge_of_isLink_of_ne (f := 0) (x := 0) (y := 1)
      (by simp) (by simp) (by decide)
  · exact (he rfl).elim

/-- All three edges form a cut, but not a bond: they properly contain the pendant bond. -/
theorem not_isBond_all : ¬graph.IsBond Set.univ := by
  intro h
  have hsub : (Set.univ : Set (Fin 3)) ⊆ {2} :=
    h.le_of_le ⟨isBond_pendant.isEdgeCut, by simp⟩ (by simp)
  have h0 := hsub (Set.mem_univ (0 : Fin 3))
  simp at h0

/-- Removing the middle vertex leaves a disconnected induced graph. -/
theorem not_connected_complement_one : ¬(graph.induce (V(graph) \ {1})).Connected := by
  intro h
  have hsides := (connected_graph.isBond_edgeCut_iff (S := {1}) (by simp)).mpr
    ⟨Graph.connected_of_vertexSet_eq_singleton (Graph.vertexSet_induce _ _), h⟩
  exact not_isBond_all (by simpa using hsides)

/-- The two-edge bond is larger than another nonempty cut in the same connected graph. -/
theorem card_pendant_lt_card_parallel_pair :
    (graph.edgeCut {2}).ncard < (graph.edgeCut {0}).ncard := by
  simp

end TauCeti.Examples.Bond
