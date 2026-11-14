/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import TauCeti.Combinatorics.Graph.Connectivity.Component
public import TauCeti.Combinatorics.Graph.Subgraph.OfSimpleGraph

/-!
# Walk traces and connectivity for subgraphs of simple graphs viewed as multigraphs

This file extends `TauCeti.Combinatorics.Graph.Subgraph.OfSimpleGraph` to walk traces, subgraph
walks, reachability, connectedness, closed subgraphs, and connected components.

Under the representation `S ↦ S.toGraph ≤ Graph.ofSimpleGraph H`:
* the subgraph `p.toSubgraph` traced by a simple-graph walk `p` corresponds to the multigraph
  `walkGraph` of `p.toGraph`;
* walks in the coerced simple graph `S.coe` are canonically equivalent to edge-labelled walks in
  `S.toGraph`, preserving length, vertex support, edge lists, trails, paths, and cycles;
* reachability and connectedness of `S.toGraph` agree with `S.coe.Reachable` and `S.Connected`;
* closed subgraphs and connected-component subgraphs of `Graph.ofSimpleGraph H` correspond to
  edge-closed subgraphs and maximal connected subgraphs (`C.toSubgraph`) of `H`.
-/

public section

open Set
open scoped Graph Sym2

universe u

namespace SimpleGraph.Walk

variable {V : Type u} {H : SimpleGraph V} {u v : V}

/-- The multigraph associated to the subgraph traced by a simple-graph walk is the multigraph walk
trace of the translated walk. -/
@[simp]
theorem toSubgraph_toGraph (p : H.Walk u v) :
    p.toSubgraph.toGraph = (Graph.ofSimpleGraph H).walkGraph p.toGraph := by
  refine Graph.ext (by simp) fun e x y ↦ ?_
  simp only [Subgraph.toGraph_isLink, adj_toSubgraph_iff_mem_edges, Graph.Walk.walkGraph_isLink,
    Graph.ofSimpleGraph_isLink, edges_toGraph]
  constructor
  · rintro ⟨rfl, hx⟩
    have hmem : s(x, y) ∈ E(Graph.ofSimpleGraph H) :=
      p.toGraph.edges_subset_edgeSet (by simpa only [edges_toGraph] using hx)
    exact ⟨⟨rfl, by simpa only [Graph.edgeSet_ofSimpleGraph] using hmem⟩, hx⟩
  · rintro ⟨⟨rfl, -⟩, hx⟩
    exact ⟨rfl, hx⟩

end SimpleGraph.Walk

namespace Graph.Walk

variable {V : Type u} {H : SimpleGraph V} {u v : V}

/-- Every walk in `Graph.ofSimpleGraph H` traces a subgraph of `Graph.ofSimpleGraph H`. -/
theorem walkGraph_le_ofSimpleGraph (p : (Graph.ofSimpleGraph H).Walk u v) :
    (Graph.ofSimpleGraph H).walkGraph p ≤ Graph.ofSimpleGraph H :=
  p.walkGraph_le (by simp)

/-- The multigraph traced by a walk in `Graph.ofSimpleGraph H` is the multigraph of the subgraph
traced by its underlying simple-graph walk. -/
theorem walkGraph_ofSimpleGraph_eq_toGraph (p : (Graph.ofSimpleGraph H).Walk u v) :
    (Graph.ofSimpleGraph H).walkGraph p = p.toSimpleGraph.toSubgraph.toGraph := by
  rw [SimpleGraph.Walk.toSubgraph_toGraph, p.toGraph_toSimpleGraph]

/-- Converting a walk trace in `Graph.ofSimpleGraph H` to `H.Subgraph` yields `Walk.toSubgraph` of
the underlying simple-graph walk. -/
@[simp]
theorem walkGraph_toSimpleGraphSubgraph (p : (Graph.ofSimpleGraph H).Walk u v)
    (hp : (Graph.ofSimpleGraph H).walkGraph p ≤ Graph.ofSimpleGraph H) :
    hp.toSimpleGraphSubgraph = p.toSimpleGraph.toSubgraph := by
  rw [← SimpleGraph.Subgraph.toGraph_inj, hp.toGraph_toSimpleGraphSubgraph,
    p.walkGraph_ofSimpleGraph_eq_toGraph]

end Graph.Walk

namespace SimpleGraph.Subgraph

variable {V : Type u} {H : SimpleGraph V}

/-! ### Walks in subgraphs -/

/-- Regard a walk in `S.coe` as an edge-labelled walk in `S.toGraph`. -/
def walkToGraph (S : H.Subgraph) : {u v : S.verts} → S.coe.Walk u v → S.toGraph.Walk u.1 v.1
  | _, _, .nil => .nil
  | u, _, .cons (v := w) h p =>
      .cons s(u.1, w.1) ((S.toGraph_isLink s(u.1, w.1) u.1 w.1).mpr ⟨rfl, h⟩) (S.walkToGraph p)

@[simp]
theorem walkToGraph_nil (S : H.Subgraph) (u : S.verts) :
    S.walkToGraph (.nil : S.coe.Walk u u) = .nil := (rfl)

@[simp]
theorem walkToGraph_cons (S : H.Subgraph) {u v w : S.verts} (h : S.coe.Adj u v)
    (p : S.coe.Walk v w) :
    S.walkToGraph (.cons h p) =
      .cons s(u.1, v.1) ((S.toGraph_isLink s(u.1, v.1) u.1 v.1).mpr ⟨rfl, h⟩) (S.walkToGraph p) :=
  (rfl)

/-- Regard an edge-labelled walk in `S.toGraph` between vertices of `S` as a walk in `S.coe`. -/
def walkOfGraph (S : H.Subgraph) :
    {x y : V} → S.toGraph.Walk x y → (hx : x ∈ S.verts) → (hy : y ∈ S.verts) →
      S.coe.Walk ⟨x, hx⟩ ⟨y, hy⟩
  | _, _, .nil, _, _ => .nil
  | x, _, .cons (y := y) e h p, hx, hz =>
      let hadj : S.Adj x y := ((S.toGraph_isLink e x y).mp h).2
      .cons ((S.coe_adj ⟨x, hx⟩ ⟨y, S.edge_vert hadj.symm⟩).mpr hadj)
        (S.walkOfGraph p (S.edge_vert hadj.symm) hz)

@[simp]
theorem walkOfGraph_nil (S : H.Subgraph) {x : V} (hx : x ∈ S.verts) :
    S.walkOfGraph (.nil : S.toGraph.Walk x x) hx hx = .nil := (rfl)

@[simp]
theorem walkOfGraph_cons (S : H.Subgraph) {x y z : V} {e : Sym2 V}
    (h : S.toGraph.IsLink e x y) (p : S.toGraph.Walk y z) (hx : x ∈ S.verts) (hz : z ∈ S.verts) :
    S.walkOfGraph (.cons e h p) hx hz =
      .cons ((S.coe_adj ⟨x, hx⟩ ⟨y, S.edge_vert (((S.toGraph_isLink e x y).mp h).2).symm⟩).mpr
          (((S.toGraph_isLink e x y).mp h).2))
        (S.walkOfGraph p (S.edge_vert (((S.toGraph_isLink e x y).mp h).2).symm) hz) :=
  (rfl)

@[simp]
theorem walkOfGraph_walkToGraph (S : H.Subgraph) {u v : S.verts} (p : S.coe.Walk u v) :
    S.walkOfGraph (S.walkToGraph p) u.2 v.2 = p := by
  induction p <;> simp_all

@[simp]
theorem walkToGraph_walkOfGraph (S : H.Subgraph) {x y : V} (p : S.toGraph.Walk x y)
    (hx : x ∈ S.verts) (hy : y ∈ S.verts) :
    S.walkToGraph (S.walkOfGraph p hx hy) = p := by
  induction p with
  | nil => rfl
  | cons e h p ih =>
      obtain ⟨rfl, -⟩ := (S.toGraph_isLink ..).mp h
      simp [ih]

/-- Walks in `S.coe` are canonically equivalent to edge-labelled walks in `S.toGraph`. -/
def walkEquivToGraph (S : H.Subgraph) (u v : S.verts) :
    S.coe.Walk u v ≃ S.toGraph.Walk u.1 v.1 where
  toFun := S.walkToGraph
  invFun p := S.walkOfGraph p u.2 v.2
  left_inv := S.walkOfGraph_walkToGraph
  right_inv p := S.walkToGraph_walkOfGraph p u.2 v.2

@[simp]
theorem walkEquivToGraph_apply (S : H.Subgraph) {u v : S.verts} (p : S.coe.Walk u v) :
    S.walkEquivToGraph u v p = S.walkToGraph p := (rfl)

@[simp]
theorem walkEquivToGraph_symm_apply (S : H.Subgraph) {u v : S.verts}
    (p : S.toGraph.Walk u.1 v.1) :
    (S.walkEquivToGraph u v).symm p = S.walkOfGraph p u.2 v.2 := (rfl)

/-- Mapping `S.walkToGraph p` into `Graph.ofSimpleGraph H` agrees with mapping `p` into `H` via
`S.hom` and then applying `SimpleGraph.Walk.toGraph`. -/
@[simp]
theorem mapLe_walkToGraph (S : H.Subgraph) {u v : S.verts} (p : S.coe.Walk u v) :
    (S.walkToGraph p).mapLe S.toGraph_le_ofSimpleGraph = (p.map S.hom).toGraph := by
  induction p with
  | nil => simp
  | cons h p ih =>
      rw [walkToGraph_cons, Graph.Walk.mapLe_cons, ih, SimpleGraph.Walk.map_cons,
        SimpleGraph.Walk.toGraph_cons]
      rfl

/-- Mapping `S.walkOfGraph p` into `H` via `S.hom` agrees with mapping `p` into
`Graph.ofSimpleGraph H` and forgetting edge labels. -/
@[simp]
theorem map_walkOfGraph (S : H.Subgraph) {x y : V} (p : S.toGraph.Walk x y)
    (hx : x ∈ S.verts) (hy : y ∈ S.verts) :
    (S.walkOfGraph p hx hy).map S.hom =
      (p.mapLe S.toGraph_le_ofSimpleGraph).toSimpleGraph := by
  rw [← SimpleGraph.Walk.toSimpleGraph_toGraph ((S.walkOfGraph p hx hy).map S.hom),
    ← S.mapLe_walkToGraph, S.walkToGraph_walkOfGraph]
  rfl

@[simp]
theorem length_walkToGraph (S : H.Subgraph) {u v : S.verts} (p : S.coe.Walk u v) :
    (S.walkToGraph p).length = p.length := by
  induction p <;> simp_all

@[simp]
theorem support_walkToGraph (S : H.Subgraph) {u v : S.verts} (p : S.coe.Walk u v) :
    (S.walkToGraph p).support = p.support.map Subtype.val := by
  induction p <;> simp_all

@[simp]
theorem edges_walkToGraph (S : H.Subgraph) {u v : S.verts} (p : S.coe.Walk u v) :
    (S.walkToGraph p).edges = p.edges.map (Sym2.map Subtype.val) := by
  induction p <;> simp_all

@[simp]
theorem isTrail_walkToGraph_iff (S : H.Subgraph) {u v : S.verts} (p : S.coe.Walk u v) :
    (S.walkToGraph p).IsTrail ↔ p.IsTrail := by
  rw [Graph.Walk.isTrail_def, SimpleGraph.Walk.isTrail_def, edges_walkToGraph,
    List.nodup_map_iff (Sym2.map.injective Subtype.val_injective)]

@[simp]
theorem isPath_walkToGraph_iff (S : H.Subgraph) {u v : S.verts} (p : S.coe.Walk u v) :
    (S.walkToGraph p).IsPath ↔ p.IsPath := by
  rw [Graph.Walk.isPath_def, SimpleGraph.Walk.isPath_def, support_walkToGraph,
    List.nodup_map_iff Subtype.val_injective]

@[simp]
theorem isCycle_walkToGraph_iff (S : H.Subgraph) {u : S.verts} (p : S.coe.Walk u u) :
    (S.walkToGraph p).IsCycle ↔ p.IsCycle := by
  have hnil : ¬(S.walkToGraph p).Nil ↔ ¬p.Nil := by
    rw [← Graph.Walk.length_eq_zero_iff, ← SimpleGraph.Walk.length_eq_zero_iff,
      length_walkToGraph]
  simp only [Graph.Walk.isCycle_def, SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def,
    edges_walkToGraph, List.nodup_map_iff (Sym2.map.injective Subtype.val_injective),
    support_walkToGraph, ← List.map_tail, List.nodup_map_iff Subtype.val_injective, ne_eq,
    Graph.Walk.eq_nil_iff_nil, SimpleGraph.Walk.eq_nil_iff_nil]
  rw [hnil]
  tauto

/-! ### Reachability, connectedness, closed subgraphs, and components -/

@[simp]
theorem reachable_toGraph_iff {S : H.Subgraph} {u v : S.verts} :
    S.toGraph.Reachable u.1 v.1 ↔ S.coe.Reachable u v := by
  rw [Graph.reachable_def, S.vertexSet_toGraph, SimpleGraph.Reachable]
  exact ⟨fun ⟨_, ⟨p⟩⟩ ↦ ⟨S.walkOfGraph p u.2 v.2⟩, fun ⟨p⟩ ↦ ⟨u.2, ⟨S.walkToGraph p⟩⟩⟩

theorem reachable_toGraph_iff_exists {S : H.Subgraph} {x y : V} :
    S.toGraph.Reachable x y ↔
      ∃ (hx : x ∈ S.verts) (hy : y ∈ S.verts), S.coe.Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  constructor
  · intro h
    have hx : x ∈ S.verts := S.vertexSet_toGraph ▸ h.left_mem
    have hy : y ∈ S.verts := S.vertexSet_toGraph ▸ h.right_mem
    exact ⟨hx, hy, (reachable_toGraph_iff (u := ⟨x, hx⟩) (v := ⟨y, hy⟩)).mp h⟩
  · rintro ⟨hx, hy, h⟩
    exact reachable_toGraph_iff.mpr h

@[simp]
theorem connected_toGraph_iff {S : H.Subgraph} :
    S.toGraph.Connected ↔ S.Connected := by
  rw [Graph.connected_iff_toSimpleGraph_connected, S.toSimpleGraphToGraphIso.connected_iff,
    S.connected_iff']

@[simp]
theorem isClosedSubgraph_toGraph_iff {S : H.Subgraph} :
    S.toGraph ≤c Graph.ofSimpleGraph H ↔ ∀ ⦃x y : V⦄, x ∈ S.verts → H.Adj x y → S.Adj x y := by
  constructor
  · intro h x y hx hxy
    have hx' : x ∈ V(S.toGraph) := S.vertexSet_toGraph.symm ▸ hx
    exact (S.toGraph_adj x y).mp
      ((h.adj_congr hx').mpr ((Graph.ofSimpleGraph_adj_iff x y).mpr hxy))
  · intro h
    refine Graph.IsClosedSubgraph.mk' S.toGraph_le_ofSimpleGraph fun e x hex hx ↦ ?_
    rw [S.vertexSet_toGraph] at hx
    rw [S.edgeSet_toGraph]
    obtain ⟨y, hexy⟩ := hex
    rw [Graph.ofSimpleGraph_isLink] at hexy
    exact hexy.1 ▸ Subgraph.mem_edgeSet.mpr (h hx (H.mem_edgeSet.mp (hexy.1 ▸ hexy.2)))

end SimpleGraph.Subgraph

namespace Graph

/-- Multigraph connectedness of `Graph.ofSimpleGraph H` agrees with connectedness of `H`. -/
@[simp]
theorem connected_ofSimpleGraph_iff {V : Type u} {H : SimpleGraph V} :
    (Graph.ofSimpleGraph H).Connected ↔ H.Connected := by
  rw [Graph.connected_iff_toSimpleGraph_connected,
    (Graph.toSimpleGraphOfSimpleGraphIso H).connected_iff]

end Graph

namespace SimpleGraph

variable {V : Type u} {H : SimpleGraph V}

namespace ConnectedComponent

theorem toSubgraph_toGraph (C : H.ConnectedComponent) :
    C.toSubgraph.toGraph = (Graph.ofSimpleGraph H).induce C.supp := by
  simp [ConnectedComponent.toSubgraph]

theorem toSubgraph_isClosedSubgraph (C : H.ConnectedComponent) :
    C.toSubgraph.toGraph ≤c Graph.ofSimpleGraph H := by
  rw [Subgraph.isClosedSubgraph_toGraph_iff]
  intro x y hx hxy
  simp only [ConnectedComponent.toSubgraph, Subgraph.induce_adj, Subgraph.top_adj]
  exact ⟨hx, (C.mem_supp_congr_adj hxy).mp hx, hxy⟩

theorem toSubgraph_isConnectedComponentOf (C : H.ConnectedComponent) :
    C.toSubgraph.toGraph.IsConnectedComponentOf (Graph.ofSimpleGraph H) := by
  have hconn : C.toSubgraph.toGraph.Connected :=
    Subgraph.connected_toGraph_iff.mpr C.connected_toSubgraph
  refine Graph.isConnectedComponentOf_iff.mpr
    ⟨C.toSubgraph_isClosedSubgraph, hconn.nonempty, fun K hK hKne hKC ↦ ?_⟩
  exact hconn.ext_of_isClosedSubgraph
    (hK.anti_right hKC C.toSubgraph.toGraph_le_ofSimpleGraph) hKne

end ConnectedComponent

namespace Subgraph

/-- A subgraph of `H` maps to a connected component of `Graph.ofSimpleGraph H` if and only if it is
maximal among connected subgraphs of `H`. -/
@[simp]
theorem isConnectedComponentOf_toGraph_iff {S : H.Subgraph} :
    S.toGraph.IsConnectedComponentOf (Graph.ofSimpleGraph H) ↔ Maximal Subgraph.Connected S := by
  rw [ConnectedComponent.maximal_subgraph_connected_iff S]
  constructor
  · intro h
    have hconn : S.Connected := connected_toGraph_iff.mp h.connected
    have hclosed : ∀ v ∈ S.verts, ∀ w, H.Adj v w → S.Adj v w :=
      fun _ hv _ hvw ↦ isClosedSubgraph_toGraph_iff.mp h.isClosedSubgraph hv hvw
    obtain ⟨C, hC⟩ := hconn.exists_verts_eq_connectedComponentSupp hclosed
    refine ⟨C, ?_⟩
    have hind : S.IsInduced := isInducedSubgraph_toGraph_iff.mp h.isInducedSubgraph
    ext x y
    · simp [hC]
    · simp only [ConnectedComponent.toSubgraph, induce_adj, top_adj]
      exact ⟨fun ⟨hx, hy, hxy⟩ ↦ hind (hC ▸ hx) (hC ▸ hy) hxy,
        fun hxy ↦ ⟨hC ▸ S.edge_vert hxy, hC ▸ S.edge_vert hxy.symm, S.adj_sub hxy⟩⟩
  · rintro ⟨C, rfl⟩
    exact C.toSubgraph_isConnectedComponentOf

end Subgraph

end SimpleGraph
