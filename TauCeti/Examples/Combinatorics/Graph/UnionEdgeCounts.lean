/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.EdgeSets

/-!
# Counting internal and incident edges across a union

Two parallel edges join `0` to `1`; a third edge joins `1` to `2`, and a loop is based at `2`.
Split the graph into the parallel pair and the remaining two edges. The parts share vertex `1`
but have disjoint edge identities. For the selected vertices `{1, 2}`, the parallel pair has no
internal edges and two incident edges, while the other part has two of each. The union formulas
therefore give two internal edges and four incident edges, counting the loop once.

Both ambient types are `ℕ`, so the example also checks that only actual edge sets must be finite.
-/

namespace TauCeti.Examples.UnionEdgeCounts

open Finset
open scoped Graph

private def parallelPart : Graph ℕ ℕ := Graph.banana 0 1 {0, 1}

private def linkPart : Graph ℕ ℕ := Graph.banana 1 2 {2}

private def loopPart : Graph ℕ ℕ := Graph.bouquet 2 {3}

private theorem link_loop_disjoint : Disjoint E(linkPart) E(loopPart) := by
  simp [linkPart, loopPart]

private def rightPart : Graph ℕ ℕ :=
  (Graph.Compatible.of_disjoint_edgeSet link_loop_disjoint).union

private theorem parts_disjoint : Disjoint E(parallelPart) E(rightPart) := by
  simp [parallelPart, rightPart, linkPart, loopPart, Set.disjoint_left]

private theorem compatible : parallelPart.Compatible rightPart :=
  Graph.Compatible.of_disjoint_edgeSet parts_disjoint

/-- A four-edge multigraph on three actual vertices, with infinite ambient vertex and edge types.
-/
def graph : Graph ℕ ℕ := compatible.union

/-- The actual vertices are `0`, `1`, and `2`. -/
@[simp]
theorem vertexSet_graph : V(graph) = {0, 1, 2} := by
  ext x
  simp [graph, parallelPart, rightPart, linkPart, loopPart]
  tauto

/-- The four actual edge identities are retained in the union. -/
@[simp]
theorem edgeSet_graph : E(graph) = {0, 1, 2, 3} := by
  ext e
  simp [graph, parallelPart, rightPart, linkPart, loopPart]
  tauto

private noncomputable instance : Fintype E(parallelPart) :=
  (by simp [parallelPart] : (E(parallelPart)).Finite).fintype
private noncomputable instance : Fintype E(rightPart) :=
  (by simp [rightPart, linkPart, loopPart] : (E(rightPart)).Finite).fintype
private noncomputable instance : Fintype E(compatible.union) :=
  (by simp [parallelPart, rightPart, linkPart, loopPart] : (E(compatible.union)).Finite).fintype

/-- Finiteness concerns the four actual edges, despite the infinite ambient type. -/
noncomputable instance fintypeEdgeSet : Fintype E(graph) := by
  unfold graph
  infer_instance

open Classical in
private theorem parallel_internal :
    (parallelPart.internalEdges (({1, 2} : Finset ℕ).subtype (· ∈ V(parallelPart)))).map
      (.subtype _) = ∅ := by
  ext e
  rw [Graph.mem_map_internalEdges_subtype]
  simp [parallelPart]

open Classical in
private theorem parallel_incident :
    (parallelPart.incidentEdges (({1, 2} : Finset ℕ).subtype (· ∈ V(parallelPart)))).map
      (.subtype _) = {0, 1} := by
  ext e
  rw [Graph.mem_map_incidentEdges_subtype]
  simp [parallelPart]

open Classical in
private theorem right_internal :
    (rightPart.internalEdges (({1, 2} : Finset ℕ).subtype (· ∈ V(rightPart)))).map
      (.subtype _) = {2, 3} := by
  ext e
  rw [Graph.mem_map_internalEdges_subtype]
  simp [rightPart, linkPart, loopPart]

open Classical in
private theorem right_incident :
    (rightPart.incidentEdges (({1, 2} : Finset ℕ).subtype (· ∈ V(rightPart)))).map
      (.subtype _) = {2, 3} := by
  ext e
  rw [Graph.mem_map_incidentEdges_subtype]
  simp [rightPart, linkPart, loopPart]

open Classical in
/-- Only the third edge and the loop are internal to the selected two vertices. -/
theorem map_internalEdges_graph :
    (graph.internalEdges (({1, 2} : Finset ℕ).subtype (· ∈ V(graph)))).map
      (.subtype _) = {2, 3} := by
  unfold graph
  rw [compatible.map_internalEdges_union, parallel_internal, right_internal]
  ext e
  simp only [mem_union, notMem_empty, false_or]

open Classical in
/-- Every edge is incident to the selected vertices, with the loop counted once. -/
theorem map_incidentEdges_graph :
    (graph.incidentEdges (({1, 2} : Finset ℕ).subtype (· ∈ V(graph)))).map
      (.subtype _) = {0, 1, 2, 3} := by
  unfold graph
  rw [compatible.map_incidentEdges_union, parallel_incident, right_incident]
  ext e
  simp only [mem_union, mem_insert, mem_singleton]
  tauto

open Classical in
/-- The internal-edge count is the sum of zero from the parallel part and two from the other
part, including its loop exactly once. -/
theorem card_internalEdges_graph :
    (graph.internalEdges (({1, 2} : Finset ℕ).subtype (· ∈ V(graph)))).card = 2 := by
  unfold graph
  rw [compatible.card_internalEdges_union parts_disjoint,
    ← card_map (Function.Embedding.subtype _), parallel_internal,
    ← card_map (Function.Embedding.subtype _), right_internal]
  simp

open Classical in
/-- The incident-edge count is the sum of two from each part, despite their common vertex. -/
theorem card_incidentEdges_graph :
    (graph.incidentEdges (({1, 2} : Finset ℕ).subtype (· ∈ V(graph)))).card = 4 := by
  unfold graph
  rw [compatible.card_incidentEdges_union parts_disjoint,
    ← card_map (Function.Embedding.subtype _), parallel_incident,
    ← card_map (Function.Embedding.subtype _), right_incident]
  simp

open Classical in
/-- Two edge-disjoint graphs sharing one vertex have respectively two internal and four incident
edges at the selected vertices. The ambient types are infinite, and the count includes a loop
once and two parallel edges separately. -/
public theorem exists_union_edge_counts :
    ∃ (G H : Graph ℕ ℕ) (h : G.Compatible H) (edges : Fintype E(h.union)),
      letI := edges
      Disjoint E(G) E(H) ∧ V(G) ∩ V(H) = {1} ∧ V(h.union) = {0, 1, 2} ∧
        E(h.union) = {0, 1, 2, 3} ∧
        (h.union.internalEdges (({1, 2} : Finset ℕ).subtype (· ∈ V(h.union)))).card = 2 ∧
        (h.union.incidentEdges (({1, 2} : Finset ℕ).subtype (· ∈ V(h.union)))).card = 4 := by
  refine ⟨parallelPart, rightPart, compatible, inferInstance, parts_disjoint, ?_,
    vertexSet_graph, edgeSet_graph, card_internalEdges_graph, card_incidentEdges_graph⟩
  ext x
  simp [parallelPart, rightPart, linkPart, loopPart]
  omega

end TauCeti.Examples.UnionEdgeCounts
