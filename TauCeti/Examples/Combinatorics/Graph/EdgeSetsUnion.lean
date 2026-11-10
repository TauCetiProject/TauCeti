/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Combinatorics.Graph.Incidence.EdgeSetsUnion

/-!
# Counting edge sets in a union with loops and parallel edges

Two parallel edges join vertices `0` and `1`; a loop at `0` is adjoined with a third identity.
Selecting only vertex `0` gives one internal edge but three incident edges. Selecting both
endpoints makes all three edges internal, without counting either endpoint twice. The ambient
vertex and edge types are infinite, and an ambient vertex outside the graph contributes nothing.
-/

public section

open Graph

namespace TauCeti.Examples.EdgeSetsUnion

private theorem disjoint_edges :
    Disjoint E(banana (0 : ℕ) 1 ({0, 1} : Set ℕ)) E(bouquet 0 ({2} : Set ℕ)) := by
  simp

private theorem compatible :
    (banana (0 : ℕ) 1 ({0, 1} : Set ℕ)).Compatible (bouquet 0 ({2} : Set ℕ)) := by
  intro e heG heH
  exact (Set.disjoint_left.mp disjoint_edges heG heH).elim

/-- Two parallel edges, together with a loop at their common endpoint `0`. -/
def graph : Graph ℕ ℕ := compatible.union

@[simp]
theorem vertexSet_graph : V(graph) = {0, 1} := by
  ext x
  simp [graph, Set.pair_comm]

@[simp]
theorem edgeSet_graph : E(graph) = {0, 1, 2} := by
  ext e
  simp [graph]
  tauto

@[simp]
theorem graph_isLink (e x y : ℕ) :
    graph.IsLink e x y ↔
      ((e = 0 ∨ e = 1) ∧ ((x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0))) ∨
        (e = 2 ∧ x = 0 ∧ y = 0) := by
  simp [graph]

noncomputable instance : Fintype E(graph) :=
  Fintype.ofFinset {0, 1, 2} (by simp)

private noncomputable instance : Fintype E(banana (0 : ℕ) 1 ({0, 1} : Set ℕ)) :=
  Fintype.ofFinset {0, 1} (by simp)

private noncomputable instance : Fintype E(bouquet (0 : ℕ) ({2} : Set ℕ)) :=
  Fintype.ofFinset {2} (by simp)

/-- Only the loop is internal to the singleton vertex set. -/
theorem internal_singleton :
    (graph.internalEdges (({0} : Finset ℕ).preimage Subtype.val
      Subtype.val_injective.injOn)).map (Function.Embedding.subtype _) = {2} := by
  ext e
  simp [graph_isLink, eq_comm]

/-- The loop and both parallel edges are incident with `0`. -/
theorem incident_singleton :
    (graph.incidentEdges (({0} : Finset ℕ).preimage Subtype.val
      Subtype.val_injective.injOn)).map (Function.Embedding.subtype _) = {0, 1, 2} := by
  ext e
  simp [Graph.Inc, graph_isLink]
  aesop

/-- Selecting both endpoints still counts each edge identity only once. -/
theorem internal_pair :
    (graph.internalEdges (({0, 1} : Finset ℕ).preimage Subtype.val
      Subtype.val_injective.injOn)).map (Function.Embedding.subtype _) = {0, 1, 2} := by
  ext e
  simp [graph_isLink]
  tauto

/-- An ambient vertex outside the graph cannot contribute an incident edge. -/
theorem incident_outside :
    graph.incidentEdges (({42} : Finset ℕ).preimage Subtype.val
      Subtype.val_injective.injOn) = ∅ := by
  apply Finset.map_injective (Function.Embedding.subtype _)
  ext e
  simp [Graph.Inc, graph_isLink]

-- Exercise the additive formulas themselves, not just the union's incidence characterization.
example :
    (graph.internalEdges (({0, 1} : Finset ℕ).preimage Subtype.val
      Subtype.val_injective.injOn)).card =
    ((banana (0 : ℕ) 1 ({0, 1} : Set ℕ)).internalEdges
      (({0, 1} : Finset ℕ).preimage Subtype.val Subtype.val_injective.injOn)).card +
    ((bouquet (0 : ℕ) ({2} : Set ℕ)).internalEdges
      (({0, 1} : Finset ℕ).preimage Subtype.val Subtype.val_injective.injOn)).card := by
  let : Fintype E(compatible.union) := inferInstanceAs (Fintype E(graph))
  exact compatible.card_internalEdges_union disjoint_edges _

example :
    (graph.incidentEdges (({0} : Finset ℕ).preimage Subtype.val
      Subtype.val_injective.injOn)).card =
    ((banana (0 : ℕ) 1 ({0, 1} : Set ℕ)).incidentEdges
      (({0} : Finset ℕ).preimage Subtype.val Subtype.val_injective.injOn)).card +
    ((bouquet (0 : ℕ) ({2} : Set ℕ)).incidentEdges
      (({0} : Finset ℕ).preimage Subtype.val Subtype.val_injective.injOn)).card := by
  let : Fintype E(compatible.union) := inferInstanceAs (Fintype E(graph))
  exact compatible.card_incidentEdges_union disjoint_edges _

end TauCeti.Examples.EdgeSetsUnion
