/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Simple
public import TauCeti.Combinatorics.Graph.Connectivity.EdgeCut
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Decomposition
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Maps

/-!
# Bridges and forests of multigraphs

Mathlib defines a bridge of a multigraph `G : Graph α β` as an edge `e` forming a singleton edge
cut, `Graph.IsBridge`.  This file characterizes bridges through edge-labelled walks:

* `Graph.IsLink.isBridge_iff_not_reachable_deleteEdges`: an edge joining `x` and `y` is a bridge
  exactly when `x` and `y` are not reachable from each other once the edge is deleted.
* `Graph.isBridge_iff_exists_not_reachable_deleteEdges`: the same criterion with the ends of the
  edge quantified existentially.
* `Graph.IsLink.isBridge_iff_forall_walk_mem_edges`: equivalently, every walk between the ends of
  the edge traverses it.
* `Graph.isBridge_iff_forall_cycle_notMem`: an actual edge is a bridge exactly when it lies on no
  cycle.

Consequently loops are never bridges, and neither is an edge having a distinct parallel edge.
A multigraph is a forest, `Graph.IsForest`, when it has no cycles; since loops and pairs of
parallel edges are cycles of multigraphs, a forest has neither.
`Graph.isForest_iff_forall_isBridge` shows that a multigraph is a forest exactly when every actual
edge is a bridge.  The statements need no finiteness assumptions.

The statements follow the corresponding results for simple graphs in Mathlib,
`SimpleGraph.isBridge_iff`, `SimpleGraph.isBridge_iff_forall_walk_mem_edges`,
`SimpleGraph.isBridge_iff_forall_cycle_notMem`, `SimpleGraph.IsBridge.notMem_edges_of_isCycle`,
`SimpleGraph.isAcyclic_iff_forall_isBridge`, and `SimpleGraph.IsAcyclic.anti`, adapted to
multigraphs whose walks record edge identities. The proof of `Graph.isForest_iff_forall_isBridge`
is adapted from Mathlib's proof of `SimpleGraph.isAcyclic_iff_forall_isBridge`.
-/

public section

open Set

universe u v

namespace Graph

variable {α : Type u} {β : Type v} {G H : Graph α β} {e f : β} {x y u w : α}

/-! ### Bridges and deletion -/

/-- The ends of a link of a bridge are not reachable from each other once the bridge is
deleted. -/
theorem IsBridge.not_reachable_deleteEdges (he : G.IsBridge e) (h : G.IsLink e x y) :
    ¬ (G.deleteEdges {e}).Reachable x y := by
  obtain ⟨S, -, hS, hx, hy⟩ := he.isEdgeCut_singleton.exists_of_isLink h (mem_singleton e)
  intro hr
  refine hy (hr.mem_of_edgeCut_eq_empty ?_ hx)
  rw [edgeCut_deleteEdges, hS, sdiff_self]

/-- An edge joining `x` and `y` is a bridge exactly when deleting it leaves `y` unreachable
from `x`. -/
theorem IsLink.isBridge_iff_not_reachable_deleteEdges (h : G.IsLink e x y) :
    G.IsBridge e ↔ ¬ (G.deleteEdges {e}).Reachable x y := by
  refine ⟨fun he ↦ he.not_reachable_deleteEdges h, fun hxy ↦ ?_⟩
  refine isEdgeCut_iff.mpr ⟨{z | (G.deleteEdges {e}).Reachable x z}, subset_antisymm ?_ ?_⟩
  · have hcut := edgeCut_setOf_reachable (G.deleteEdges {e}) x
    rwa [edgeCut_deleteEdges, sdiff_eq_empty] at hcut
  · rw [singleton_subset_iff, Graph.mem_edgeCut_iff]
    refine ⟨x, y, h, Reachable.refl ?_, hxy⟩
    rw [vertexSet_deleteEdges]
    exact h.left_mem

/-- An edge is a bridge exactly when it links two vertices that are not reachable from each other
once it is deleted. -/
theorem isBridge_iff_exists_not_reachable_deleteEdges :
    G.IsBridge e ↔ ∃ x y, G.IsLink e x y ∧ ¬ (G.deleteEdges {e}).Reachable x y := by
  refine ⟨fun he ↦ ?_, fun ⟨_, _, h, hxy⟩ ↦ h.isBridge_iff_not_reachable_deleteEdges.mpr hxy⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he.mem_edgeSet
  exact ⟨x, y, h, he.not_reachable_deleteEdges h⟩

/-- An edge joining `x` and `y` is a bridge exactly when every walk from `x` to `y` traverses
it. -/
theorem IsLink.isBridge_iff_forall_walk_mem_edges (h : G.IsLink e x y) :
    G.IsBridge e ↔ ∀ p : G.Walk x y, e ∈ p.edges := by
  rw [h.isBridge_iff_not_reachable_deleteEdges, reachable_deleteEdges_iff_exists_walk]
  simp only [mem_singleton_iff, h.left_mem, true_and, not_exists, not_forall, not_not]
  exact forall_congr' fun p ↦ ⟨fun ⟨_, hf, hfe⟩ ↦ hfe ▸ hf, fun he ↦ ⟨e, he, rfl⟩⟩

/-- A loop is never a bridge. -/
theorem IsLoopAt.not_isBridge (h : G.IsLoopAt e x) : ¬ G.IsBridge e := fun he ↦ by
  obtain ⟨S, -, hS⟩ := he.isEdgeCut_singleton.exists_edgeCut
  exact h.notMem_edgeCut (hS ▸ mem_singleton e)

/-- An edge with a distinct parallel edge is not a bridge. -/
theorem IsLink.not_isBridge_of_isLink_of_ne (he : G.IsLink e x y) (hf : G.IsLink f x y)
    (hfe : f ≠ e) : ¬ G.IsBridge e := by
  rw [he.isBridge_iff_not_reachable_deleteEdges, not_not]
  apply IsLink.reachable (e := f)
  rw [deleteEdges_isLink]
  exact ⟨hf, hfe⟩

/-! ### Bridges and cycles -/

/-- A bridge lies on no cycle. -/
theorem IsBridge.notMem_edges_of_isCycle (he : G.IsBridge e) {p : G.Walk u u}
    (hp : p.IsCycle) : e ∉ p.edges := by
  intro hep
  obtain ⟨x, y, h, q, r, rfl⟩ := Walk.mem_edges_iff_exists_append.mp hep
  have htrail := hp.isTrail
  rw [Walk.isTrail_def, Walk.edges_append, Walk.edges_cons] at htrail
  have hq : e ∉ q.edges := fun heq ↦ List.disjoint_of_nodup_append htrail heq (by simp)
  have hr : e ∉ r.edges := ((List.nodup_append.mp htrail).2.1).notMem
  rw [(h.symm).isBridge_iff_forall_walk_mem_edges] at he
  simpa [Walk.edges_append, hq, hr] using he (r.append q)

/-- An actual edge is a bridge exactly when it lies on no cycle. -/
theorem isBridge_iff_forall_cycle_notMem (he : e ∈ E(G)) :
    G.IsBridge e ↔ ∀ ⦃u : α⦄ (p : G.Walk u u), p.IsCycle → e ∉ p.edges := by
  refine ⟨fun hb _ _ hp ↦ hb.notMem_edges_of_isCycle hp, fun hcyc ↦ ?_⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
  rw [h.isBridge_iff_not_reachable_deleteEdges]
  intro hr
  classical
  obtain ⟨-, q, hq⟩ := reachable_deleteEdges_iff_exists_walk.mp hr.symm
  refine hcyc (.cons e h q.bypass) ?_ (by simp)
  exact (Walk.cons_isCycle_iff ..).mpr
    ⟨q.bypass_isPath, fun hm ↦ hq e (q.edges_bypass_subset_edges hm) rfl⟩

/-! ### Forests -/

/-- A multigraph is a forest if it has no cycles. Loops and pairs of distinct parallel edges
form cycles, so a forest has neither. -/
def IsForest (G : Graph α β) : Prop := ∀ ⦃u : α⦄ (p : G.Walk u u), ¬ p.IsCycle

theorem isForest_def : G.IsForest ↔ ∀ ⦃u : α⦄ (p : G.Walk u u), ¬ p.IsCycle := Iff.rfl

/-- A multigraph is a forest exactly when every actual edge is a bridge. -/
theorem isForest_iff_forall_isBridge : G.IsForest ↔ ∀ ⦃e⦄, e ∈ E(G) → G.IsBridge e := by
  refine ⟨fun hG e he ↦ (isBridge_iff_forall_cycle_notMem he).mpr fun _ p hp ↦ (hG p hp).elim,
    fun hG u p hp ↦ ?_⟩
  obtain ⟨e, he⟩ := p.edges.exists_mem_of_ne_nil <| by simp [hp.not_nil]
  exact (hG (p.edges_subset_edgeSet he)).notMem_edges_of_isCycle hp he

/-- Every actual edge of a forest is a bridge. -/
theorem IsForest.isBridge (hG : G.IsForest) (he : e ∈ E(G)) : G.IsBridge e :=
  isForest_iff_forall_isBridge.mp hG he

/-- A subgraph of a forest is a forest. -/
theorem IsForest.anti (hHG : H ≤ G) (hG : G.IsForest) : H.IsForest :=
  fun _ p hp ↦ hG (p.mapLe hHG) ((Walk.isCycle_mapLe hHG p).mpr hp)

/-- A forest has no loops. -/
theorem IsForest.loopless (hG : G.IsForest) : G.Loopless where
  not_isLoopAt _ _ h := hG h.toWalk h.isCycle_toWalk

/-- Two edges of a forest joining the same ends are equal. -/
theorem IsForest.eq_of_isLink (hG : G.IsForest) (he : G.IsLink e x y) (hf : G.IsLink f x y) :
    f = e := by
  by_contra hfe
  exact he.not_isBridge_of_isLink_of_ne hf hfe (hG.isBridge he.edge_mem)

/-- A graph with no edges is a forest. -/
@[simp]
theorem isForest_noEdge (X : Set α) : (noEdge X β).IsForest :=
  isForest_iff_forall_isBridge.mpr fun _ he ↦ by simp at he

/-! ### Graphs on two vertices -/

/-- The single edge joining two distinct vertices is a bridge. -/
theorem isBridge_banana_singleton (huw : u ≠ w) (e : β) : (banana u w {e}).IsBridge e :=
  isEdgeCut_iff.mpr ⟨{u}, edgeCut_banana_singleton huw {e}⟩

/-- Two distinct vertices joined by a single edge form a forest. -/
theorem isForest_banana_singleton (huw : u ≠ w) (e : β) : (banana u w {e}).IsForest :=
  isForest_iff_forall_isBridge.mpr fun f hf ↦ by
    rw [edgeSet_banana, mem_singleton_iff] at hf
    exact hf ▸ isBridge_banana_singleton huw e

/-- No edge of a graph on two vertices with several edges is a bridge. -/
theorem not_isBridge_banana {F : Set β} (he : e ∈ F) (hf : f ∈ F) (hfe : f ≠ e) :
    ¬ (banana u w F).IsBridge e :=
  IsLink.not_isBridge_of_isLink_of_ne (x := u) (y := w) (by simp [he]) (by simp [hf]) hfe

end Graph
