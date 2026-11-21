/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.AddEdge
public import TauCeti.Combinatorics.Graph.Serre.Cycle.SpanningTree
public import TauCeti.Combinatorics.Graph.Serre.Multigraph

/-!
# Cycle modules of graphs with isolated vertices

This file computes the cycle ranks, the number of components and the spanning forests of four
small graphs whose darts are all loops, none of which is connected except the single vertex:

* the one-petal rose with an isolated vertex adjoined, `(noEdge Bool).addEdge false false`;
* two isolated vertices, `noEdge Bool`;
* the empty graph, `noEdge PEmpty`;
* a single vertex, `noEdge PUnit`.

In each case the cycle rank plus the number of vertices is the number of edges plus the number of
components, without a connectedness hypothesis: `1 + 2 = 1 + 2`, `0 + 2 = 0 + 2` and `0 + 0 = 0 + 0`
for the first three. The empty set of darts is their spanning forest, and none of the first three
has a spanning tree.

## References

* A. Hatcher, *Algebraic Topology*, §2.2 (incidence boundaries) and Chapter 3, p. 187 (cycles of
  graphs, componentwise).
* R. Diestel, *Graph Theory*, §1.9 (cycle spaces).
-/

public section

namespace TauCeti.Examples.SerreEdgeless

open TauCeti.SerreGraph

/-! ### The one-petal rose with an isolated vertex -/

/-- Adjoining an isolated vertex to the one-petal rose leaves its integral cycle rank one. -/
example : Module.finrank ℤ (((noEdge.{0, 0} Bool).addEdge false false).cycleLattice {.inr true}) =
    1 := by
  rw [cycleLattice_def, finrank_ker_incidenceBoundary_of_forall_src_eq_tgt fun e _ =>
    addEdge_src_eq_tgt isEmptyElim e, Nat.card_unique]

/-- Adjoining an isolated vertex to the one-petal rose leaves its binary cycle rank one. -/
example : Module.finrank (ZMod 2)
    (((noEdge.{0, 0} Bool).addEdge false false).modTwoCycleSpace {.inr true}) = 1 := by
  rw [modTwoCycleSpace_def, finrank_ker_incidenceBoundary_of_forall_src_eq_tgt
    fun e _ => addEdge_src_eq_tgt isEmptyElim e, Nat.card_unique]

/-- The one-petal rose with an isolated vertex has two components. -/
example : Nat.card (((noEdge.{0, 0} Bool).addEdge false false).supportGraph
    {.inr true}).ConnectedComponent = 2 := by
  rw [card_connectedComponent_supportGraph_of_forall_src_eq_tgt fun e _ =>
    addEdge_src_eq_tgt isEmptyElim e]
  exact Nat.card_eq_fintype_card.trans Fintype.card_bool

/-- The only spanning forest of the one-petal rose with an isolated vertex is empty: a spanning
forest cannot contain the loop. -/
example (F : Set ((noEdge.{0, 0} Bool).addEdge false false).E) :
    ((noEdge.{0, 0} Bool).addEdge false false).IsSpanningForest {.inr true} F ↔ F = ∅ :=
  ⟨fun hF => hF.eq_empty fun e _ => addEdge_src_eq_tgt isEmptyElim e,
    fun h => h ▸ isSpanningForest_empty_iff.mpr fun e _ => addEdge_src_eq_tgt isEmptyElim e⟩

/-- The one-petal rose with an isolated vertex has no spanning tree. -/
example : IsEmpty ((noEdge.{0, 0} Bool).addEdge false false).SpanningTree :=
  ⟨fun T => not_subsingleton Bool <|
    (preconnected_iff_of_forall_src_eq_tgt _ (addEdge_src_eq_tgt isEmptyElim)).mp
      ((connected_iff _).mp ((nonempty_spanningTree_iff _).mp ⟨T⟩)).2⟩

/-! ### Two isolated vertices -/

/-- Two isolated vertices have integral cycle rank zero. -/
example : Module.finrank ℤ ((noEdge.{0, 0} Bool).cycleLattice Set.univ) = 0 := by
  rw [cycleLattice_def, finrank_ker_incidenceBoundary_of_forall_src_eq_tgt fun e _ => isEmptyElim e,
    Nat.card_of_isEmpty]

/-- Two isolated vertices have binary cycle rank zero. -/
example : Module.finrank (ZMod 2) ((noEdge.{0, 0} Bool).modTwoCycleSpace Set.univ) = 0 := by
  rw [modTwoCycleSpace_def, finrank_ker_incidenceBoundary_of_forall_src_eq_tgt
    fun e _ => isEmptyElim e, Nat.card_of_isEmpty]

/-- Two isolated vertices form two components. -/
example : Nat.card ((noEdge.{0, 0} Bool).supportGraph Set.univ).ConnectedComponent = 2 := by
  rw [card_connectedComponent_supportGraph_of_forall_src_eq_tgt fun e _ => isEmptyElim e]
  exact Nat.card_eq_fintype_card.trans Fintype.card_bool

/-- The empty spanning forest of two isolated vertices. -/
example : (noEdge.{0, 0} Bool).IsSpanningForest Set.univ ∅ :=
  isSpanningForest_empty_iff.mpr fun e _ => isEmptyElim e

/-- Two isolated vertices have no spanning tree. -/
example : IsEmpty (noEdge.{0, 0} Bool).SpanningTree :=
  ⟨fun T => noEdge_not_connected ((nonempty_spanningTree_iff _).mp ⟨T⟩)⟩

/-! ### The empty graph -/

/-- The empty graph has integral cycle rank zero. -/
example : Module.finrank ℤ ((noEdge.{0, 0} PEmpty).cycleLattice Set.univ) = 0 := by
  rw [cycleLattice_def, finrank_ker_incidenceBoundary_of_forall_src_eq_tgt fun e _ => isEmptyElim e,
    Nat.card_of_isEmpty]

/-- The empty graph has binary cycle rank zero. -/
example : Module.finrank (ZMod 2) ((noEdge.{0, 0} PEmpty).modTwoCycleSpace Set.univ) = 0 := by
  rw [modTwoCycleSpace_def, finrank_ker_incidenceBoundary_of_forall_src_eq_tgt
    fun e _ => isEmptyElim e, Nat.card_of_isEmpty]

/-- The empty graph has no components. -/
example : Nat.card ((noEdge.{0, 0} PEmpty).supportGraph Set.univ).ConnectedComponent = 0 := by
  rw [card_connectedComponent_supportGraph_of_forall_src_eq_tgt fun e _ => isEmptyElim e,
    Nat.card_of_isEmpty]

/-- The empty spanning forest of the empty graph. -/
example : (noEdge.{0, 0} PEmpty).IsSpanningForest Set.univ ∅ :=
  isSpanningForest_empty_iff.mpr fun e _ => isEmptyElim e

/-- The empty graph has no spanning tree. -/
example : IsEmpty (noEdge.{0, 0} PEmpty).SpanningTree :=
  ⟨fun T => isEmptyElim ((connected_iff _).mp ((nonempty_spanningTree_iff _).mp ⟨T⟩)).1.some⟩

/-! ### A single vertex -/

/-- A single vertex forms one component. -/
example : Nat.card ((noEdge.{0, 0} PUnit).supportGraph Set.univ).ConnectedComponent = 1 := by
  rw [card_connectedComponent_supportGraph_of_forall_src_eq_tgt fun e _ => isEmptyElim e,
    Nat.card_unique]

/-- The multigraph underlying a single vertex has one component. -/
example : (noEdge.{0, 0} PUnit).toGraph.componentCount = 1 := by
  rw [componentCount_toGraph_noEdge, Nat.card_unique]

end TauCeti.Examples.SerreEdgeless
