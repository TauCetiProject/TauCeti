/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Multigraph
public import TauCeti.Combinatorics.Graph.Serre.Tree

/-!
# Serre graphs without edges

The Serre graph `SerreGraph.noEdge V` has the vertices `V` and no darts. Its only paths are the
empty ones, so every vertex is a connected component by itself: its underlying multigraph is
`Graph.noEdge Set.univ _` and has `Nat.card V` components.

Two boundary cases separate the notions of connectedness. The empty graph `noEdge PEmpty` is
preconnected, vacuously, but it is neither connected nor a tree and it has no component:
connectedness requires a vertex. The graph `noEdge Bool` of two isolated vertices is not even
preconnected and has two components, although it has a vertex: the presence of a base vertex does
not make a graph connected.

## References

* J.-P. Serre, *Trees*, Chapter I, §§2.1–2.2.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership
  problem*, §2, Convention 2.1.
-/

public section

universe u v

namespace TauCeti
namespace SerreGraph

variable {V : Type u}

/-- The multigraph underlying a Serre graph without edges has all vertices and no edges. -/
theorem toGraph_noEdge : (noEdge.{u, v} V).toGraph = Graph.noEdge Set.univ _ :=
  Graph.ext (by simp) fun q _ _ => isEmptyElim ((noEdge V).edge_surjective q).choose

/-- In a graph without edges every vertex is a connected component by itself, so the underlying
multigraph has as many components as there are vertices. -/
@[simp] theorem componentCount_toGraph_noEdge :
    (noEdge.{u, v} V).toGraph.componentCount = Nat.card V := by
  rw [Graph.componentCount_def]
  refine (Nat.card_congr (Equiv.ofBijective _
    ⟨fun a b h => ?_, (noEdge V).toGraph_connectedComponentOf_surjective⟩)).symm
  exact noEdge_nonempty_path_iff.mp (((noEdge V).toGraph_connectedComponentOf_eq_iff a b).mp h)

/-! ### The empty graph -/

/-- The empty graph is preconnected: there is no pair of vertices to join. -/
theorem noEdge_pempty_preconnected : (noEdge.{u, v} PEmpty).Preconnected :=
  noEdge_preconnected_iff.mpr inferInstance

/-- The empty graph is not connected, although it is preconnected. -/
theorem noEdge_pempty_not_connected : ¬(noEdge.{u, v} PEmpty).Connected :=
  fun h => (noEdge_connected_iff.mp h).1.elim PEmpty.elim

/-- The empty graph is not a tree. -/
theorem noEdge_pempty_not_isTree : ¬(noEdge.{u, v} PEmpty).IsTree :=
  fun h => noEdge_pempty_not_connected (h.connected _)

/-- The multigraph underlying the empty graph is not connected. -/
theorem toGraph_noEdge_pempty_not_connected : ¬(noEdge.{u, v} PEmpty).toGraph.Connected :=
  fun h => noEdge_pempty_not_connected ((connected_toGraph_iff _).mp h)

/-- The multigraph underlying the empty graph has no component. -/
theorem componentCount_toGraph_noEdge_pempty :
    (noEdge.{u, v} PEmpty).toGraph.componentCount = 0 :=
  componentCount_toGraph_noEdge.trans Nat.card_of_isEmpty

/-! ### Two isolated vertices -/

/-- Two isolated vertices are not joined by a path. -/
theorem noEdge_bool_not_preconnected : ¬(noEdge.{0, v} Bool).Preconnected :=
  fun h => Bool.false_ne_true ((noEdge_preconnected_iff.mp h).elim _ _)

/-- The graph of two isolated vertices is not connected, although it has a vertex. -/
theorem noEdge_bool_not_connected : ¬(noEdge.{0, v} Bool).Connected :=
  fun h => noEdge_bool_not_preconnected ((connected_iff _).mp h).2

/-- The multigraph underlying the graph of two isolated vertices is not connected. -/
theorem toGraph_noEdge_bool_not_connected : ¬(noEdge.{0, v} Bool).toGraph.Connected :=
  fun h => noEdge_bool_not_connected ((connected_toGraph_iff _).mp h)

/-- The multigraph underlying the graph of two isolated vertices has two components. -/
theorem componentCount_toGraph_noEdge_bool :
    (noEdge.{0, v} Bool).toGraph.componentCount = 2 :=
  componentCount_toGraph_noEdge.trans (by simp)

end SerreGraph
end TauCeti
