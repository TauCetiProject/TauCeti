/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
public import TauCeti.Combinatorics.Graph.Connectivity.CutCapacity
public import TauCeti.Combinatorics.Graph.Union

/-!
# Aggregating weighted multigraph cuts

This example aggregates a weighted multigraph to capacities on unordered pairs of actual
vertices. The graph has two parallel edges of capacities two and three, a loop of capacity seven,
and an edge of capacity zero. Aggregation adds the parallel capacities, discards the loop, and
retains the zero value on the remaining pair.

The second pair-capacity function changes every diagonal value from zero to eleven. Its cut
function and support graph are unchanged, because diagonal pairs never cross a cut and never form
simple-graph edges. Both pair-capacity cut functions agree with the original multigraph cut
function on every vertex set.
-/

public section

open Finset Set
open scoped Graph

namespace TauCeti.Examples.CutAggregation

/-- The four edge identities in the weighted aggregation example. -/
abbrev Edge := Fin 4

private def parallelPart : Graph (Fin 3) Edge :=
  Graph.banana 0 1 {0, 1}

private def loopPart : Graph (Fin 3) Edge :=
  Graph.bouquet 0 {2}

private theorem parallel_loop_disjoint : Disjoint E(parallelPart) E(loopPart) := by
  simp [parallelPart, loopPart]

private def parallelLoopPart : Graph (Fin 3) Edge :=
  (Graph.Compatible.of_disjoint_edgeSet parallel_loop_disjoint).union

private def zeroPart : Graph (Fin 3) Edge :=
  Graph.banana 1 2 {3}

private theorem parallelLoop_zero_disjoint : Disjoint E(parallelLoopPart) E(zeroPart) := by
  simp [parallelLoopPart, parallelPart, loopPart, zeroPart]

/-- A three-vertex multigraph with two parallel edges, a loop, and one further edge. -/
def graph : Graph (Fin 3) Edge :=
  (Graph.Compatible.of_disjoint_edgeSet parallelLoop_zero_disjoint).union

private theorem isLink_graph (e : Edge) (x y : Fin 3) :
    graph.IsLink e x y ↔
      (((e = 0 ∨ e = 1) ∧ ((x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0))) ∨
        (e = 2 ∧ x = 0 ∧ y = 0)) ∨
        (e = 3 ∧ ((x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1))) := by
  simp [graph, parallelLoopPart, parallelPart, loopPart, zeroPart]

/-- Every ambient vertex is an actual vertex of `graph`. -/
@[simp]
theorem vertexSet_graph : V(graph) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  fin_cases x
  · exact ((isLink_graph 0 0 1).2 (by simp)).left_mem
  · exact ((isLink_graph 0 0 1).2 (by simp)).right_mem
  · exact ((isLink_graph 3 1 2).2 (by simp)).right_mem

/-- Every ambient edge identity is an actual edge of `graph`. -/
@[simp]
theorem edgeSet_graph : E(graph) = Set.univ := by
  ext e
  simp only [Set.mem_univ, iff_true]
  fin_cases e
  · exact ((isLink_graph 0 0 1).2 (by simp)).edge_mem
  · exact ((isLink_graph 1 0 1).2 (by simp)).edge_mem
  · exact ((isLink_graph 2 0 0).2 (by simp)).edge_mem
  · exact ((isLink_graph 3 1 2).2 (by simp)).edge_mem

/-- The actual vertex set is finite in the aggregation example. -/
noncomputable local instance : Fintype V(graph) :=
  Fintype.ofEquiv (Fin 3)
    (Equiv.subtypeUnivEquiv (p := (· ∈ V(graph))) (by simp)).symm

/-- The actual edge set is finite in the aggregation example. -/
noncomputable local instance : Fintype E(graph) :=
  Fintype.ofEquiv Edge
    (Equiv.subtypeUnivEquiv (p := (· ∈ E(graph))) (by simp)).symm

private theorem sum_edges (f : E(graph) → ℕ) :
    ∑ e, f e = ∑ e : Edge, f ⟨e, by simp⟩ := by
  exact Fintype.sum_equiv
    (Equiv.subtypeUnivEquiv (p := (· ∈ E(graph))) (by simp)) _ _ (fun _ ↦ rfl)

/-- Include one of the three ambient vertices into the actual vertex set of `graph`. -/
abbrev vertex (i : Fin 3) : V(graph) :=
  ⟨i, by simp⟩

/-- The weights two and three lie on the parallel edges, seven lies on the loop, and the final
edge has weight zero. -/
def edgeCapacity (e : E(graph)) : ℕ :=
  ![2, 3, 7, 0] e.1

/-- The first parallel edge has capacity two. -/
@[simp]
theorem edgeCapacity_zero : edgeCapacity ⟨0, by simp⟩ = 2 :=
  (rfl)

/-- The second parallel edge has capacity three. -/
@[simp]
theorem edgeCapacity_one : edgeCapacity ⟨1, by simp⟩ = 3 :=
  (rfl)

/-- The loop has capacity seven. -/
@[simp]
theorem edgeCapacity_two : edgeCapacity ⟨2, by simp⟩ = 7 :=
  (rfl)

/-- The edge from vertex one to vertex two has capacity zero. -/
@[simp]
theorem edgeCapacity_three : edgeCapacity ⟨3, by simp⟩ = 0 :=
  (rfl)

/-- The two parallel edges aggregate to capacity five on their unordered pair of endpoints. -/
theorem pairCapacity_zero_one :
    graph.pairCapacity edgeCapacity s(vertex 0, vertex 1) = 5 := by
  classical
  rw [graph.pairCapacity_mk_of_ne edgeCapacity (by decide)]
  rw [sum_edges]
  norm_num [Fin.sum_univ_four, isLink_graph]

/-- The loop is discarded by aggregation, so the diagonal capacity at vertex zero is zero. -/
theorem pairCapacity_zero_zero :
    graph.pairCapacity edgeCapacity s(vertex 0, vertex 0) = 0 :=
  Graph.pairCapacity_mk_self graph edgeCapacity (vertex 0)

/-- The edge from one to two is retained by the graph but has aggregated capacity zero. -/
theorem pairCapacity_one_two :
    graph.pairCapacity edgeCapacity s(vertex 1, vertex 2) = 0 := by
  classical
  rw [graph.pairCapacity_mk_of_ne edgeCapacity (by decide)]
  rw [sum_edges]
  norm_num [Fin.sum_univ_four, isLink_graph]

/-- A pair-capacity function obtained from the multigraph aggregation by assigning eleven to
every diagonal pair. -/
noncomputable def pairCapacityWithDiagonal (p : Sym2 V(graph)) : ℕ :=
  if p.IsDiag then 11 else graph.pairCapacity edgeCapacity p

/-- The modified pair-capacity function really has a nonzero diagonal. -/
@[simp]
theorem pairCapacityWithDiagonal_self (x : V(graph)) :
    pairCapacityWithDiagonal s(x, x) = 11 := by
  simp [pairCapacityWithDiagonal, Sym2.mk_isDiag_iff]

/-- Away from the diagonal, the modified pair capacities are the aggregated edge capacities. -/
theorem pairCapacityWithDiagonal_mk_of_ne (x y : V(graph)) (hxy : x ≠ y) :
    pairCapacityWithDiagonal s(x, y) = graph.pairCapacity edgeCapacity s(x, y) := by
  simp [pairCapacityWithDiagonal, Sym2.mk_isDiag_iff, hxy]

/-- Changing the diagonal values leaves the simple support graph unchanged. -/
theorem capacitySupport_pairCapacityWithDiagonal :
    capacitySupport pairCapacityWithDiagonal =
      capacitySupport (graph.pairCapacity edgeCapacity) :=
  capacitySupport_eq_of_offDiagonal_eq _ _ pairCapacityWithDiagonal_mk_of_ne

/-- The modified pair-capacity cut function agrees with the weighted multigraph cut function for
every choice of source side. This simultaneously verifies aggregation and diagonal invariance. -/
theorem pairCutCapacity_pairCapacityWithDiagonal (S : Finset V(graph)) :
    pairCutCapacity pairCapacityWithDiagonal S = graph.edgeCutCapacity edgeCapacity S := by
  calc
    pairCutCapacity pairCapacityWithDiagonal S =
        pairCutCapacity (graph.pairCapacity edgeCapacity) S :=
      congrFun (pairCutCapacity_eq_of_offDiagonal_eq _ _
        pairCapacityWithDiagonal_mk_of_ne) S
    _ = graph.edgeCutCapacity edgeCapacity S :=
      Graph.pairCutCapacity_pairCapacity graph edgeCapacity S

end TauCeti.Examples.CutAggregation
