/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.Union

/-!
# Counting parallel edges and loops in a union

Two parallel edges between `0` and `1` are combined with a loop at `0`. The vertex `0` belongs
to both input graphs, but their edge identities are disjoint. The incidence count there is three,
whereas the nonloop incidence count is two and the loop count is one.

Selecting only vertex `0` gives one internal edge but three incident edges. Selecting both
endpoints makes all three edges internal, without counting any edge identity twice. An ambient
vertex outside the graph contributes nothing.

Both ambient types are `ℕ`. Thus the example also checks that finiteness of the actual vertex
and edge sets, rather than the ambient types, suffices for the counting API.
-/

public section

open Set
open scoped Graph

namespace TauCeti.Examples.IncidenceUnion

private abbrev parallel : Graph ℕ ℕ := Graph.banana 0 1 {0, 1}
private abbrev loop : Graph ℕ ℕ := Graph.bouquet 0 {2}

private instance : Finite E(parallel) := Set.finite_coe_iff.mpr (by simp)
private instance : Finite E(loop) := Set.finite_coe_iff.mpr (by simp)

private theorem disjoint_edges : Disjoint E(parallel) E(loop) := by
  simp

private theorem compatible : parallel.Compatible loop :=
  Graph.Compatible.of_disjoint_edgeSet disjoint_edges

/-- Two parallel edges with a loop at their common left endpoint. -/
def graph : Graph ℕ ℕ := compatible.union

/-- The example has two actual vertices, despite its infinite ambient vertex type. -/
@[simp]
theorem vertexSet_graph : V(graph) = {0, 1} := by
  ext x
  simp [graph]

/-- The example retains three different actual edge identities. -/
@[simp]
theorem edgeSet_graph : E(graph) = {0, 1, 2} := by
  ext e
  simp [graph]
  tauto

/-- Only the actual vertices need to be finite. -/
instance : Finite V(graph) := Set.finite_coe_iff.mpr (by simp)

/-- Only the actual edges need to be finite. -/
instance : Finite E(graph) := Set.finite_coe_iff.mpr (by simp)

/-- At the shared vertex the incidence counts add: two parallel edges plus one loop. -/
@[simp]
theorem incidenceCount_zero : graph.incidenceCount 0 = 3 := by
  have h := compatible.incidenceCount_union disjoint_edges 0
    (parallel.finite_incidenceSet 0) (loop.finite_incidenceSet 0)
  simpa [graph, Graph.incidenceCount_bouquet] using h

/-- Excluding loops, only the two parallel edge identities are counted at the shared vertex. -/
@[simp]
theorem nonloopIncidenceCount_zero : graph.nonloopIncidenceCount 0 = 2 := by
  have h := compatible.nonloopIncidenceCount_union disjoint_edges 0
    (parallel.finite_incidenceSet 0).sdiff (loop.finite_incidenceSet 0).sdiff
  simpa [graph] using h

/-- The union's loop count is one, independently of the two parallel nonloop edges. -/
@[simp]
theorem ncard_loopSet_zero : (graph.loopSet 0).ncard = 1 := by
  simp [graph]

/-- At the other endpoint there are two incident edges and no contribution from the loop. -/
@[simp]
theorem incidenceCount_one : graph.incidenceCount 1 = 2 := by
  have hp : parallel.incidenceSet 1 = {0, 1} := by ext e; simp
  have hl : loop.incidenceSet 1 = ∅ := by ext e; simp
  simp [graph, Graph.incidenceCount_def, hp, hl]

/-- The links are the two parallel edges and the loop at `0`. -/
@[simp]
theorem graph_isLink (e x y : ℕ) :
    graph.IsLink e x y ↔
      ((e = 0 ∨ e = 1) ∧ ((x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0))) ∨
        (e = 2 ∧ x = 0 ∧ y = 0) := by
  simp [graph, parallel, loop]

/-- Enumerate the actual edge identities for finite edge-set computations. -/
noncomputable instance : Fintype E(graph) := Fintype.ofFinite _

open Classical in
/-- Only the loop is internal to the singleton vertex set. -/
theorem internal_singleton :
    (graph.internalEdges (({0} : Finset ℕ).subtype (· ∈ V(graph)))).map
      (Function.Embedding.subtype _) = {2} := by
  ext e
  rw [Graph.mem_map_internalEdges_subtype]
  simp [graph_isLink]

open Classical in
/-- The loop and both parallel edges are incident with `0`. -/
theorem incident_singleton :
    (graph.incidentEdges (({0} : Finset ℕ).subtype (· ∈ V(graph)))).map
      (Function.Embedding.subtype _) = {0, 1, 2} := by
  ext e
  rw [Graph.mem_map_incidentEdges_subtype]
  simp [Graph.Inc, graph_isLink]
  aesop

open Classical in
/-- Selecting both endpoints still counts each edge identity only once. -/
theorem internal_pair :
    (graph.internalEdges (({0, 1} : Finset ℕ).subtype (· ∈ V(graph)))).map
      (Function.Embedding.subtype _) = {0, 1, 2} := by
  ext e
  rw [Graph.mem_map_internalEdges_subtype]
  simp [graph_isLink]
  tauto

open Classical in
/-- An ambient vertex outside the graph cannot contribute an incident edge. -/
theorem incident_outside :
    graph.incidentEdges (({42} : Finset ℕ).subtype (· ∈ V(graph))) = ∅ := by
  apply Finset.map_injective (Function.Embedding.subtype _)
  ext e
  rw [Graph.mem_map_incidentEdges_subtype]
  simp [Graph.Inc, graph_isLink]

end TauCeti.Examples.IncidenceUnion
