/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Simple
public import TauCeti.Combinatorics.Graph.Connectivity.Component
public import TauCeti.Combinatorics.Graph.Connectivity.EdgeCut
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Decomposition
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Maps

import Mathlib.SetTheory.Cardinal.NatCard

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

Deleting an edge joining `x` and `y` affects only the connected component containing them:
`Graph.IsLink.reachable_iff_reachable_deleteEdges_or` shows that this component splits into the
components of `x` and of `y` in the deletion, which are distinct exactly when the edge is a
bridge, and `Graph.IsLink.reachable_deleteEdges_iff_of_not_reachable` that reachability elsewhere
is unchanged.  Counting components, `Graph.isBridge_iff_componentCount_deleteEdges_eq_add_one`
shows that, when there are finitely many components, an edge is a bridge exactly when deleting it
increases the number of connected components by one; deleting any other edge leaves the number
unchanged (`Graph.componentCount_deleteEdges_of_not_isBridge`).

A multigraph is a forest, `Graph.IsForest`, when it has no cycles; since loops and pairs of
parallel edges are cycles of multigraphs, a forest has neither.
`Graph.isForest_iff_forall_isBridge` shows that a multigraph is a forest exactly when every actual
edge is a bridge.  Only the component count after deleting a bridge assumes finitely many
components; the other statements need no finiteness assumptions.

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

/-- The set of all bridges of a multigraph. -/
def bridgeSet (G : Graph α β) : Set β := {e | G.IsBridge e}

@[simp]
theorem mem_bridgeSet {e : β} : e ∈ G.bridgeSet ↔ G.IsBridge e := Iff.rfl

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

/-! ### Bridges and connected components -/

/-- Deleting an edge that is not a bridge does not change reachability. -/
theorem reachable_deleteEdges_iff_of_not_isBridge (he : ¬ G.IsBridge e) :
    (G.deleteEdges {e}).Reachable u v ↔ G.Reachable u v := by
  refine ⟨Reachable.mono deleteEdges_le, fun huv ↦ ?_⟩
  by_cases heG : e ∈ E(G)
  · obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet heG
    have hxy : (G.deleteEdges {e}).Reachable x y := by
      simpa [h.isBridge_iff_not_reachable_deleteEdges] using he
    refine (h.reachable_deleteEdges_or_reachable huv).elim id fun hux ↦ ?_
    have hvx : G.Reachable v x := huv.symm.trans hux
    -- Both `u` and `v` lie on the side of `x` or of `y`, which are joined in the deletion.
    have hside : ∀ {w}, G.Reachable w x → (G.deleteEdges {e}).Reachable x w := fun hw ↦
      (h.reachable_iff_reachable_deleteEdges_or.mp hw.symm).elim id hxy.trans
    exact (hside hux).symm.trans (hside hvx)
  · obtain ⟨hu, ⟨p⟩⟩ := reachable_def.mp huv
    exact reachable_deleteEdges_iff_exists_walk.mpr
      ⟨hu, p, fun f hf hfe ↦ heG (hfe ▸ p.edges_subset_edgeSet hf)⟩

/-- Deleting an edge that is not a bridge leaves the number of connected components unchanged. -/
theorem componentCount_deleteEdges_of_not_isBridge (he : ¬ G.IsBridge e) :
    (G.deleteEdges {e}).componentCount = G.componentCount := by
  have hle : G.deleteEdges {e} ≤ G := deleteEdges_le
  rw [componentCount_eq_natCard_toSimpleGraph, componentCount_eq_natCard_toSimpleGraph]
  refine Nat.card_congr (Equiv.ofBijective
    (SimpleGraph.ConnectedComponent.map (toSimpleGraphHomOfLE hle)) ⟨fun C D hCD ↦ ?_, fun C ↦ ?_⟩)
  · induction C using SimpleGraph.ConnectedComponent.ind with | h z => ?_
    induction D using SimpleGraph.ConnectedComponent.ind with | h w => ?_
    rw [toSimpleGraph_connectedComponentMk_eq_iff, reachable_deleteEdges_iff_of_not_isBridge he]
    exact (map_toSimpleGraphHomOfLE_connectedComponentMk_eq_map_iff hle).mp hCD
  · induction C using SimpleGraph.ConnectedComponent.ind with | h z => ?_
    exact ⟨_, (map_toSimpleGraphHomOfLE_connectedComponentMk_eq_iff hle).mpr
      (Reachable.refl z.2)⟩

/-- Deleting a bridge increases the number of connected components by exactly one: the
component containing its ends splits into the components of its two ends, and every other
component is unchanged. -/
theorem IsBridge.componentCount_deleteEdges [Finite G.ConnectedComponent] (he : G.IsBridge e) :
    (G.deleteEdges {e}).componentCount = G.componentCount + 1 := by
  classical
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he.mem_edgeSet
  have hle : G.deleteEdges {e} ≤ G := deleteEdges_le
  let mk := (G.deleteEdges {e}).toSimpleGraph.connectedComponentMk
  let A := mk ⟨y, by simpa using h.right_mem⟩
  -- A vertex reachable from `x` but outside the component of `y` stays reachable from `x`.
  have hside : ∀ {z}, mk z ≠ A → G.Reachable x z → (G.deleteEdges {e}).Reachable x z :=
    fun hz hxz ↦ (h.reachable_iff_reachable_deleteEdges_or.mp hxz).resolve_right fun hyz ↦
      hz (toSimpleGraph_connectedComponentMk_eq_iff.mpr hyz.symm)
  -- Away from the component of `y` in the deletion, the induced map of components is bijective.
  let ψ : {C // C ≠ A} → G.toSimpleGraph.ConnectedComponent :=
    fun C ↦ SimpleGraph.ConnectedComponent.map (toSimpleGraphHomOfLE hle) C
  have hψ : Function.Bijective ψ := by
    refine ⟨fun ⟨C, hC⟩ ⟨D, hD⟩ hCD ↦ ?_, fun C ↦ ?_⟩
    · induction C using SimpleGraph.ConnectedComponent.ind with | h z => ?_
      induction D using SimpleGraph.ConnectedComponent.ind with | h w => ?_
      have hzw : G.Reachable z w :=
        (map_toSimpleGraphHomOfLE_connectedComponentMk_eq_map_iff hle).mp hCD
      rw [Subtype.mk.injEq]
      refine toSimpleGraph_connectedComponentMk_eq_iff.mpr
        ((h.reachable_deleteEdges_or_reachable hzw).elim id fun hzx ↦ ?_)
      exact (hside hC hzx.symm).symm.trans (hside hD (hzx.symm.trans hzw))
    · induction C using SimpleGraph.ConnectedComponent.ind with | h z => ?_
      by_cases hz : mk ⟨z, by simp⟩ = A
      · refine ⟨⟨mk ⟨x, by simpa using h.left_mem⟩,
          fun hxA ↦ he.not_reachable_deleteEdges h
            (toSimpleGraph_connectedComponentMk_eq_iff.mp hxA)⟩,
          (map_toSimpleGraphHomOfLE_connectedComponentMk_eq_iff hle).mpr ?_⟩
        exact h.reachable.trans ((toSimpleGraph_connectedComponentMk_eq_iff.mp hz).symm.mono hle)
      · refine ⟨⟨_, hz⟩, ?_⟩
        exact (map_toSimpleGraphHomOfLE_connectedComponentMk_eq_iff hle).mpr
          (Reachable.refl z.2)
  have : Finite G.toSimpleGraph.ConnectedComponent := Finite.of_equiv _ G.connectedComponentEquiv
  have : Finite {C // C ≠ A} := Finite.of_equiv _ (Equiv.ofBijective ψ hψ).symm
  rw [componentCount_eq_natCard_toSimpleGraph, componentCount_eq_natCard_toSimpleGraph,
    ← Nat.card_congr (Equiv.optionSubtypeNe A), Finite.card_option,
    Nat.card_congr (Equiv.ofBijective ψ hψ)]

/-- **Bridges by component counts.**  With finitely many connected components, an edge is a
bridge exactly when deleting it increases the number of connected components by one. -/
theorem isBridge_iff_componentCount_deleteEdges_eq_add_one [Finite G.ConnectedComponent] :
    G.IsBridge e ↔ (G.deleteEdges {e}).componentCount = G.componentCount + 1 :=
  ⟨IsBridge.componentCount_deleteEdges, fun h ↦ by_contra fun he ↦ by
    simp [componentCount_deleteEdges_of_not_isBridge he] at h⟩

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
