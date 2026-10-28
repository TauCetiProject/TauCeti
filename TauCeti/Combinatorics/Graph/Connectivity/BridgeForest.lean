/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Graph.Maps
public import TauCeti.Combinatorics.Graph.Connectivity.Bridge
public import TauCeti.Combinatorics.Graph.Delete

/-!
# The bridge forest of a multigraph

Deleting all bridges of a multigraph `G : Graph α β` leaves a graph whose connected components
are the maximal bridgeless pieces of `G`.  Contracting each of these components to a vertex while
keeping the bridges as edges gives the *bridge forest* of `G`.  This file constructs it directly,
using Mathlib's vertex map `Graph.map`, and proves that it is a forest whose connected components
correspond to those of `G`.

## Main definitions

* `Graph.bridgeComponent G x`: the connected component containing `x` of the graph obtained
  from `G` by deleting all of its bridges, as an induced subgraph.
* `Graph.bridgeForest G : Graph (Graph α β) β`: the bridge forest.  Its vertices are the connected
  components of `G` with all bridges deleted (`Graph.mem_vertexSet_bridgeForest_iff`), and its
  edges are the bridges of `G`, each joining the components containing its ends.

## Main results

* `Graph.IsBridge.bridgeComponent_ne`: every bridge joins distinct components.
* `Graph.reachable_deleteEdges_bridgeForest_iff`: for any set `F` of bridges, two vertices are
  reachable in `G` after deleting `F` exactly when their components are reachable in the bridge
  forest after deleting `F`.  In particular the components of the bridge forest correspond to
  those of `G` (`Graph.reachable_bridgeForest_iff`, `Graph.componentCount_bridgeForest`), and the
  bridge forest is connected exactly when `G` is (`Graph.connected_bridgeForest_iff`).
* `Graph.isForest_bridgeForest`: the bridge forest is a forest; in particular no two bridges join
  the same pair of components (`Graph.IsForest.eq_of_isLink`).
* `Graph.not_isBridge_deleteEdges_setOf_isBridge`: the graph left after deleting all bridges has
  no bridges.
* `Graph.finite_setOf_isBridge`, `Graph.ncard_vertexSet_bridgeForest`: when `G` has finitely many
  actual vertices it has finitely many bridges, and the number of components left after deleting
  all bridges is the number of bridges plus the number of components of `G`.

Only the counting statements assume finiteness, and only of the actual vertex set.
-/

public section

open Set

namespace Graph

variable {α β : Type*} {G : Graph α β} {e f : β} {x y : α} {F : Set β}

/-! ### Components after deleting all bridges -/

/-- The connected component containing `x` of the graph obtained from `G` by deleting all of its
bridges, as an induced subgraph.  For `x ∉ V(G)` it is the graph with no vertices.  Unlike
`Graph.connectedComponentOf`, it is defined at every point, as the vertex map `Graph.map`
requires; `Graph.bridgeComponent_eq_connectedComponentOf` compares the two. -/
def bridgeComponent (G : Graph α β) (x : α) : Graph α β :=
  (G.deleteEdges {e | G.IsBridge e}).induce
    {y | (G.deleteEdges {e | G.IsBridge e}).Reachable x y}

/-- The vertices of the bridge component of `x` are the points reachable from `x` without using
bridges. -/
@[simp]
theorem vertexSet_bridgeComponent :
    V(G.bridgeComponent x) = {y | (G.deleteEdges {e | G.IsBridge e}).Reachable x y} := by
  simp [bridgeComponent]

/-- The bridge component of an actual vertex is its connected component after deleting all
bridges. -/
theorem bridgeComponent_eq_connectedComponentOf (hx : x ∈ V(G)) :
    G.bridgeComponent x =
      ((G.deleteEdges {e | G.IsBridge e}).connectedComponentOf x
        (by rwa [vertexSet_deleteEdges])).1 := by
  set C := (G.deleteEdges {e | G.IsBridge e}).connectedComponentOf x
    (by rwa [vertexSet_deleteEdges])
  have hV : ∀ y, y ∈ V(C.1) ↔ (G.deleteEdges {e | G.IsBridge e}).Reachable x y := fun _ ↦
    mem_vertexSet_connectedComponentOf_iff _
  refine Graph.ext (by ext y; simp [hV]) fun e u v ↦ ?_
  rw [bridgeComponent, induce_isLink, mem_ofPred_eq, mem_ofPred_eq, ← hV, ← hV]
  exact ⟨fun ⟨h, hu, hv⟩ ↦ (C.2.isInducedSubgraph.isLink_congr hu hv).mpr h,
    fun h ↦ ⟨(C.2.isInducedSubgraph.isLink_congr h.left_mem h.right_mem).mp h, h.left_mem,
      h.right_mem⟩⟩

/-- The bridge component of an actual vertex is a connected component of the graph obtained by
deleting all bridges. -/
theorem bridgeComponent_isConnectedComponentOf (hx : x ∈ V(G)) :
    (G.bridgeComponent x).IsConnectedComponentOf (G.deleteEdges {e | G.IsBridge e}) := by
  rw [bridgeComponent_eq_connectedComponentOf hx]
  exact (connectedComponentOf _ _ _).property

/-- Two actual vertices have the same bridge component exactly when they are reachable from each
other without using bridges. -/
theorem bridgeComponent_eq_bridgeComponent_iff (hx : x ∈ V(G)) :
    G.bridgeComponent x = G.bridgeComponent y ↔
      (G.deleteEdges {e | G.IsBridge e}).Reachable x y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hxx : x ∈ V(G.bridgeComponent x) := by
      simpa [vertexSet_bridgeComponent] using hx
    rw [h, vertexSet_bridgeComponent, mem_ofPred_eq] at hxx
    exact hxx.symm
  · rw [bridgeComponent, bridgeComponent]
    congr 1
    ext z
    exact ⟨h.symm.trans, h.trans⟩

/-- Every bridge joins distinct bridge components. -/
theorem IsBridge.bridgeComponent_ne (he : G.IsBridge e) (h : G.IsLink e x y) :
    G.bridgeComponent x ≠ G.bridgeComponent y := by
  rw [Ne, bridgeComponent_eq_bridgeComponent_iff h.left_mem]
  exact fun hxy ↦ he.not_reachable_deleteEdges h
    (hxy.mono (G.deleteEdges_anti (singleton_subset_iff.mpr he)))

/-- **The graph left after deleting all bridges is bridgeless.**  An edge that is not a bridge
lies on a cycle, which contains no bridge. -/
theorem not_isBridge_deleteEdges_setOf_isBridge :
    ¬ (G.deleteEdges {e | G.IsBridge e}).IsBridge f := by
  intro hf
  have hfG : f ∈ E(G) \ {e | G.IsBridge e} := by
    simpa only [edgeSet_deleteEdges] using hf.mem_edgeSet
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet hfG.1
  have hxy : (G.deleteEdges {f}).Reachable x y := by
    by_contra hxy
    exact hfG.2 (h.isBridge_iff_not_reachable_deleteEdges.mpr hxy)
  classical
  obtain ⟨-, q, hq⟩ := reachable_deleteEdges_iff_exists_walk.mp hxy.symm
  -- Closing a path from `y` to `x` avoiding `f` with `f` gives a cycle, so it uses no bridge.
  have hcyc : (Walk.cons f h q.bypass).IsCycle := (Walk.cons_isCycle_iff ..).mpr
    ⟨q.bypass_isPath, fun hm ↦ hq f (q.edges_bypass_subset_edges hm) rfl⟩
  refine hf.not_reachable_deleteEdges (by simpa using ⟨h, hfG.2⟩) ?_
  rw [deleteEdges_deleteEdges]
  refine reachable_deleteEdges_iff_exists_walk.mpr ⟨h.left_mem, q.bypass.reverse, fun g hg ↦ ?_⟩
  rw [Walk.edges_reverse, List.mem_reverse] at hg
  have hgf : g ≠ f := fun hgf ↦ hq f (q.edges_bypass_subset_edges (hgf ▸ hg)) rfl
  have hgcyc : g ∈ (Walk.cons f h q.bypass).edges := by simp [hg]
  rintro (hgB | hgf')
  · exact (hgB : G.IsBridge g).notMem_edges_of_isCycle hcyc hgcyc
  · exact hgf hgf'

/-! ### The bridge forest -/

/-- The **bridge forest** of a multigraph `G`.  Its vertices are the connected components of `G`
with all bridges deleted, regarded as subgraphs, and its edges are the bridges of `G`; a bridge
joins the components containing its two ends. -/
def bridgeForest (G : Graph α β) : Graph (Graph α β) β :=
  (G.restrict {e | G.IsBridge e}).map G.bridgeComponent

/-- The vertices of the bridge forest are the bridge components of the actual vertices. -/
@[simp]
theorem vertexSet_bridgeForest : V(G.bridgeForest) = G.bridgeComponent '' V(G) := by
  simp [bridgeForest]

/-- The edges of the bridge forest are the bridges. -/
@[simp]
theorem edgeSet_bridgeForest : E(G.bridgeForest) = {e | G.IsBridge e} := by
  simp only [bridgeForest, edgeSet_map, edgeSet_restrict, inter_eq_right]
  exact fun _ he ↦ IsBridge.mem_edgeSet he

/-- A bridge forest edge is a bridge, joining the bridge components of its ends. -/
@[simp]
theorem bridgeForest_isLink {H K : Graph α β} :
    G.bridgeForest.IsLink e H K ↔ G.IsBridge e ∧
      ∃ x y, G.IsLink e x y ∧ G.bridgeComponent x = H ∧ G.bridgeComponent y = K := by
  simp only [bridgeForest, map_isLink, Relation.Map, restrict_isLink, mem_ofPred_eq]
  exact ⟨fun ⟨x, y, ⟨he, h⟩, hx, hy⟩ ↦ ⟨he, x, y, h, hx, hy⟩,
    fun ⟨he, x, y, h, hx, hy⟩ ↦ ⟨x, y, ⟨he, h⟩, hx, hy⟩⟩

/-- A bridge joining `x` and `y` joins their bridge components in the bridge forest. -/
theorem IsBridge.isLink_bridgeForest (he : G.IsBridge e) (h : G.IsLink e x y) :
    G.bridgeForest.IsLink e (G.bridgeComponent x) (G.bridgeComponent y) :=
  bridgeForest_isLink.mpr ⟨he, x, y, h, rfl, rfl⟩

/-- The vertices of the bridge forest are exactly the connected components of `G` with all
bridges deleted. -/
theorem mem_vertexSet_bridgeForest_iff {H : Graph α β} :
    H ∈ V(G.bridgeForest) ↔ H.IsConnectedComponentOf (G.deleteEdges {e | G.IsBridge e}) := by
  rw [vertexSet_bridgeForest]
  refine ⟨fun ⟨x, hx, hH⟩ ↦ hH ▸ bridgeComponent_isConnectedComponentOf hx, fun hH ↦ ?_⟩
  obtain ⟨x, hx⟩ := hH.nonempty
  have hxG : x ∈ V(G) := by simpa using hH.le.vertexSet_mono hx
  refine ⟨x, hxG, ?_⟩
  rw [bridgeComponent_eq_connectedComponentOf hxG]
  exact congrArg Subtype.val
    (ConnectedComponent.eq_connectedComponentOf (C := ⟨H, hH⟩) hx).symm

/-- The bridge component of a point is a vertex of the bridge forest exactly when the point is an
actual vertex. -/
theorem bridgeComponent_mem_vertexSet_bridgeForest_iff :
    G.bridgeComponent x ∈ V(G.bridgeForest) ↔ x ∈ V(G) := by
  refine ⟨fun hx ↦ ?_, mem_image_of_mem _⟩
  obtain ⟨y, hy, hyx⟩ := (vertexSet_bridgeForest (G := G)) ▸ hx
  have hyy : y ∈ V(G.bridgeComponent y) := by simpa [vertexSet_bridgeComponent] using hy
  rw [hyx, vertexSet_bridgeComponent, mem_ofPred_eq] at hyy
  simpa using hyy.left_mem

/-- **Reachability in the bridge forest.**  For a set `F` of bridges of `G`, two points are
reachable in `G` after deleting `F` exactly when their bridge components are reachable in the
bridge forest after deleting `F`. -/
theorem reachable_deleteEdges_bridgeForest_iff (hF : F ⊆ {e | G.IsBridge e}) :
    (G.bridgeForest.deleteEdges F).Reachable (G.bridgeComponent x) (G.bridgeComponent y) ↔
      (G.deleteEdges F).Reachable x y := by
  have hle := G.deleteEdges_anti hF
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hx : x ∈ V(G) := bridgeComponent_mem_vertexSet_bridgeForest_iff.mp
      (by simpa using h.left_mem)
    obtain ⟨-, ⟨p⟩⟩ := reachable_def.mp h
    -- Lift a walk in the bridge forest step by step: each bridge is preceded by a walk inside a
    -- bridge component.
    suffices ∀ {H K : Graph α β} (p : (G.bridgeForest.deleteEdges F).Walk H K) {x y : α},
        x ∈ V(G) → G.bridgeComponent x = H → G.bridgeComponent y = K →
          (G.deleteEdges F).Reachable x y from this p hx rfl rfl
    intro H K p
    induction p with
    | nil =>
      intro x y hx hxH hyH
      exact ((bridgeComponent_eq_bridgeComponent_iff hx).mp (hxH.trans hyH.symm)).mono hle
    | cons e h p ih =>
      intro x y hx hxH hyK
      obtain ⟨h, heF⟩ := (deleteEdges_isLink ..).mp h
      obtain ⟨-, u, v, huv, rfl, rfl⟩ := bridgeForest_isLink.mp h
      have hxu := ((bridgeComponent_eq_bridgeComponent_iff hx).mp hxH).mono hle
      have huv' : (G.deleteEdges F).IsLink e u v := (deleteEdges_isLink ..).mpr ⟨huv, heF⟩
      exact hxu.trans (huv'.reachable.trans (ih huv.right_mem rfl hyK))
  · obtain ⟨hx, p, hp⟩ := reachable_deleteEdges_iff_exists_walk.mp h
    clear h
    -- Project a walk avoiding `F`: bridges become edges of the bridge forest, and all other edges
    -- stay inside a bridge component.
    induction p with
    | nil => exact Reachable.refl (by simpa using mem_image_of_mem _ hx)
    | @cons x z y e h p ih =>
      have hzy := ih h.right_mem fun f hf ↦ hp f (by simp [hf])
      have heF : e ∉ F := hp e (by simp)
      by_cases he : G.IsBridge e
      · exact ((deleteEdges_isLink ..).mpr ⟨he.isLink_bridgeForest h, heF⟩).reachable.trans hzy
      · have hxz : (G.deleteEdges {e | G.IsBridge e}).Reachable x z :=
          ((deleteEdges_isLink ..).mpr ⟨h, he⟩).reachable
        rwa [(bridgeComponent_eq_bridgeComponent_iff hx).mpr hxz]

/-- Two points are reachable in `G` exactly when their bridge components are reachable in the
bridge forest. -/
theorem reachable_bridgeForest_iff :
    G.bridgeForest.Reachable (G.bridgeComponent x) (G.bridgeComponent y) ↔ G.Reachable x y := by
  simpa using reachable_deleteEdges_bridgeForest_iff (G := G) (F := ∅) (x := x) (y := y)
    (empty_subset _)

/-- **The bridge forest is a forest.** -/
theorem isForest_bridgeForest : G.bridgeForest.IsForest := by
  refine isForest_iff_forall_isBridge.mpr fun e he ↦ ?_
  rw [edgeSet_bridgeForest, mem_ofPred_eq] at he
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he.mem_edgeSet
  rw [(he.isLink_bridgeForest h).isBridge_iff_not_reachable_deleteEdges,
    reachable_deleteEdges_bridgeForest_iff (singleton_subset_iff.mpr he)]
  exact he.not_reachable_deleteEdges h

/-- The bridge forest is connected, hence a tree, exactly when `G` is connected. -/
theorem connected_bridgeForest_iff : G.bridgeForest.Connected ↔ G.Connected := by
  simp only [connected_iff_forall_reachable, vertexSet_bridgeForest, image_nonempty]
  refine and_congr_right fun _ ↦ ⟨fun h x y hx hy ↦ ?_, ?_⟩
  · exact reachable_bridgeForest_iff.mp (h (mem_image_of_mem _ hx) (mem_image_of_mem _ hy))
  · rintro h - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact reachable_bridgeForest_iff.mpr (h hx hy)

/-- The bridge forest has as many connected components as `G`. -/
theorem componentCount_bridgeForest : G.bridgeForest.componentCount = G.componentCount := by
  have hmem (x : V(G)) : G.bridgeComponent x ∈ V(G.bridgeForest) :=
    bridgeComponent_mem_vertexSet_bridgeForest_iff.mpr x.2
  let φ : G.toSimpleGraph.ConnectedComponent → G.bridgeForest.toSimpleGraph.ConnectedComponent :=
    SimpleGraph.ConnectedComponent.lift
      (fun x ↦ G.bridgeForest.toSimpleGraph.connectedComponentMk ⟨_, hmem x⟩)
      fun x y p _ ↦ by
        rw [toSimpleGraph_connectedComponentMk_eq_iff, reachable_bridgeForest_iff]
        exact toSimpleGraph_reachable_iff.mp p.reachable
  have hφ : Function.Bijective φ := by
    refine ⟨fun C D hCD ↦ ?_, fun C ↦ ?_⟩
    · induction C using SimpleGraph.ConnectedComponent.ind with | h x => ?_
      induction D using SimpleGraph.ConnectedComponent.ind with | h y => ?_
      simp only [φ, SimpleGraph.ConnectedComponent.lift_mk,
        toSimpleGraph_connectedComponentMk_eq_iff, reachable_bridgeForest_iff] at hCD ⊢
      exact hCD
    · induction C using SimpleGraph.ConnectedComponent.ind with | h H => ?_
      obtain ⟨H, hH⟩ := H
      obtain ⟨x, hx, rfl⟩ := (vertexSet_bridgeForest (G := G)) ▸ hH
      exact ⟨G.toSimpleGraph.connectedComponentMk ⟨x, hx⟩, SimpleGraph.ConnectedComponent.lift_mk⟩
  rw [componentCount_eq_natCard_toSimpleGraph, componentCount_eq_natCard_toSimpleGraph,
    Nat.card_congr (Equiv.ofBijective φ hφ)]

/-! ### Counting -/

/-- **Counting the bridge forest.**  For a multigraph with finitely many actual vertices, the
number of connected components left after deleting all bridges, which is the number of vertices
of the bridge forest, is the number of bridges plus the number of connected components. -/
theorem ncard_vertexSet_bridgeForest [Finite V(G)] :
    V(G.bridgeForest).ncard = {e | G.IsBridge e}.ncard + G.componentCount := by
  rw [← Nat.card_coe_set_eq, add_comm, ← componentCount_deleteEdges_of_subset_setOf_isBridge
    finite_setOf_isBridge subset_rfl, componentCount_def]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ mem_vertexSet_bridgeForest_iff)

end Graph
