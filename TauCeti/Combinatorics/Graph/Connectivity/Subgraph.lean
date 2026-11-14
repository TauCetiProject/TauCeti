/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import TauCeti.Combinatorics.Graph.Connectivity.Bridge.OfSimpleGraph
public import TauCeti.Combinatorics.Graph.Connectivity.Isomorphism
public import TauCeti.Combinatorics.Graph.Connectivity.Walk.Trace
public import TauCeti.Combinatorics.Graph.Subgraph

/-!
# Walks and connectivity of simple-graph subgraphs viewed as multigraphs

This file extends the order isomorphism `SimpleGraph.subgraphOfSimpleGraphOrderIso` between
`H.Subgraph` and subgraphs of `Graph.ofSimpleGraph H` to walk-traced subgraphs, subgraph walks, and
connectivity invariants.

Converting a simple-graph walk `p : H.Walk x y` to `Graph.ofSimpleGraph H` identifies Mathlib's
traced subgraph `p.toSubgraph` with the multigraph traced graph `walkGraph`. For an arbitrary
subgraph `S : H.Subgraph` and base vertex `x ∈ S.verts`, edge-labelled walks in `S.toGraph`
correspond bijectively to ambient walks `p : H.Walk x y` satisfying `p.toSubgraph ≤ S`, and the
canonical isomorphism `S.ofSimpleGraphCoeIso` identifies connectedness, acyclicity/forests, and edge
and vertex connectivity of `S.toGraph` with those of `S` and `S.coe`.

## Main declarations

* `SimpleGraph.Walk.toGraph_toSubgraph`: `p.toSubgraph.toGraph` equals the multigraph `walkGraph` of
  `p.toGraph`.
* `SimpleGraph.Subgraph.walkToGraphEquiv`: equivalence between
  `{p : H.Walk x y // p.toSubgraph ≤ S}` and `S.toGraph.Walk x y` when `x ∈ S.verts`.
* `SimpleGraph.Subgraph.connected_toGraph_iff`, `SimpleGraph.Subgraph.isForest_toGraph_iff`,
  `SimpleGraph.Subgraph.isEdgeConnected_toGraph_iff`,
  `SimpleGraph.Subgraph.isVertexConnected_toGraph_iff`: transport of connectivity invariants between
  `S.toGraph` and `S` / `S.coe`.
-/

public section

open Set
open scoped Graph Sym2

universe u

namespace SimpleGraph.Walk

variable {α : Type u} {H : SimpleGraph α} {x y : α}

/-- Converting a walk's traced `Subgraph` to a multigraph agrees with taking `walkGraph` of the
converted walk in `Graph.ofSimpleGraph H`. -/
@[simp]
theorem toGraph_toSubgraph (p : H.Walk x y) :
    p.toSubgraph.toGraph = (Graph.ofSimpleGraph H).walkGraph p.toGraph := by
  refine Graph.ext (by simp) fun e a b ↦ ?_
  simp only [Subgraph.toGraph_isLink, adj_toSubgraph_iff_mem_edges, Graph.Walk.walkGraph_isLink,
    Graph.ofSimpleGraph_isLink, edges_toGraph]
  exact ⟨fun ⟨he, hmem⟩ ↦ ⟨⟨he, he ▸ p.edges_subset_edgeSet hmem⟩, he ▸ hmem⟩,
    fun ⟨⟨he, _⟩, hmem⟩ ↦ ⟨he, he ▸ hmem⟩⟩

end SimpleGraph.Walk

namespace Graph.Walk

variable {α : Type u} {H : SimpleGraph α} {x y : α}

/-- Every walk in `Graph.ofSimpleGraph H` traces a subgraph of `Graph.ofSimpleGraph H`, since every
element of `α` is an actual vertex of `Graph.ofSimpleGraph H`. -/
theorem walkGraph_le_ofSimpleGraph (p : (Graph.ofSimpleGraph H).Walk x y) :
    (Graph.ofSimpleGraph H).walkGraph p ≤ Graph.ofSimpleGraph H :=
  p.walkGraph_le (mem_univ x)

theorem toGraph_toSubgraph_toSimpleGraph (p : (Graph.ofSimpleGraph H).Walk x y) :
    p.toSimpleGraph.toSubgraph.toGraph = (Graph.ofSimpleGraph H).walkGraph p := by
  rw [SimpleGraph.Walk.toGraph_toSubgraph, toGraph_toSimpleGraph]

@[simp]
theorem toSimpleGraphSubgraph_walkGraph (p : (Graph.ofSimpleGraph H).Walk x y)
    (hp : (Graph.ofSimpleGraph H).walkGraph p ≤ Graph.ofSimpleGraph H) :
    hp.toSimpleGraphSubgraph = p.toSimpleGraph.toSubgraph :=
  SimpleGraph.Subgraph.toGraph_injective (by simp)

end Graph.Walk

namespace SimpleGraph.Subgraph

variable {α : Type u} {H : SimpleGraph α} {S : H.Subgraph}

/-- Transfer an ambient simple-graph walk contained in `S` to an edge-labelled walk in
`S.toGraph`. -/
def walkToGraph {x y : α} (p : H.Walk x y) (hp : p.toSubgraph ≤ S) : S.toGraph.Walk x y :=
  p.toGraph.transfer S.toGraph_le_ofSimpleGraph fun e he ↦ by
    rw [S.edgeSet_toGraph]
    rw [SimpleGraph.Walk.edges_toGraph] at he
    exact Subgraph.edgeSet_mono hp (p.mem_edges_toSubgraph.mpr he)

@[simp]
theorem mapLe_walkToGraph {x y : α} (p : H.Walk x y) (hp : p.toSubgraph ≤ S) :
    (S.walkToGraph p hp).mapLe S.toGraph_le_ofSimpleGraph = p.toGraph :=
  Graph.Walk.mapLe_transfer S.toGraph_le_ofSimpleGraph p.toGraph _

@[simp]
theorem support_walkToGraph {x y : α} (p : H.Walk x y) (hp : p.toSubgraph ≤ S) :
    (S.walkToGraph p hp).support = p.support := by
  rw [← Graph.Walk.support_mapLe_eq_support S.toGraph_le_ofSimpleGraph, mapLe_walkToGraph,
    SimpleGraph.Walk.support_toGraph]

@[simp]
theorem edges_walkToGraph {x y : α} (p : H.Walk x y) (hp : p.toSubgraph ≤ S) :
    (S.walkToGraph p hp).edges = p.edges := by
  rw [← Graph.Walk.edges_mapLe_eq_edges S.toGraph_le_ofSimpleGraph, mapLe_walkToGraph,
    SimpleGraph.Walk.edges_toGraph]

@[simp]
theorem length_walkToGraph {x y : α} (p : H.Walk x y) (hp : p.toSubgraph ≤ S) :
    (S.walkToGraph p hp).length = p.length := by
  rw [← Graph.Walk.length_mapLe S.toGraph_le_ofSimpleGraph, mapLe_walkToGraph,
    SimpleGraph.Walk.length_toGraph]

/-- When `x ∈ S.verts`, an edge-labelled walk from `x` to `y` in `S.toGraph` traces a simple-graph
walk in `H` whose `toSubgraph` is contained in `S`. -/
theorem toSubgraph_toSimpleGraph_mapLe_le {x y : α} (hx : x ∈ S.verts)
    (p : S.toGraph.Walk x y) :
    (p.mapLe S.toGraph_le_ofSimpleGraph).toSimpleGraph.toSubgraph ≤ S := by
  rw [← toGraph_le_toGraph_iff, Graph.Walk.toGraph_toSubgraph_toSimpleGraph,
    Graph.Walk.walkGraph_mapLe]
  exact p.walkGraph_le (S.vertexSet_toGraph.symm ▸ hx)

/-- For `x ∈ S.verts`, ambient walks `p : H.Walk x y` with `p.toSubgraph ≤ S` correspond
bijectively to edge-labelled walks in `S.toGraph`. -/
def walkToGraphEquiv (S : H.Subgraph) {x : α} (hx : x ∈ S.verts) (y : α) :
    {p : H.Walk x y // p.toSubgraph ≤ S} ≃ S.toGraph.Walk x y where
  toFun p := S.walkToGraph p.1 p.2
  invFun q := ⟨(q.mapLe S.toGraph_le_ofSimpleGraph).toSimpleGraph,
    S.toSubgraph_toSimpleGraph_mapLe_le hx q⟩
  left_inv p := Subtype.ext (by simp)
  right_inv q := Graph.Walk.mapLe_injective S.toGraph_le_ofSimpleGraph x y (by simp)

@[simp]
theorem walkToGraphEquiv_apply (S : H.Subgraph) {x : α} (hx : x ∈ S.verts) (y : α)
    (p : {p : H.Walk x y // p.toSubgraph ≤ S}) :
    S.walkToGraphEquiv hx y p = S.walkToGraph p.1 p.2 := (rfl)

@[simp]
theorem coe_walkToGraphEquiv_symm_apply (S : H.Subgraph) {x : α} (hx : x ∈ S.verts) (y : α)
    (q : S.toGraph.Walk x y) :
    ((S.walkToGraphEquiv hx y).symm q : H.Walk x y) =
      (q.mapLe S.toGraph_le_ofSimpleGraph).toSimpleGraph := (rfl)

/-- Reachability in `S.toGraph` agrees with reachability in `S.coe` on `S.verts`. -/
@[simp]
theorem reachable_toGraph_iff {x y : α} :
    S.toGraph.Reachable x y ↔
      ∃ (hx : x ∈ S.verts) (hy : y ∈ S.verts), S.coe.Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  refine ⟨fun h ↦ ?_, fun ⟨hx, hy, hr⟩ ↦ ?_⟩
  · let ux : V(S.toGraph) := ⟨x, h.left_mem⟩
    let uy : V(S.toGraph) := ⟨y, h.right_mem⟩
    have hx : x ∈ S.verts := S.vertexSet_toGraph ▸ h.left_mem
    have hy : y ∈ S.verts := S.vertexSet_toGraph ▸ h.right_mem
    have hux : S.toGraphToSimpleGraphIso ux = ⟨x, hx⟩ :=
      Subtype.ext (S.coe_toGraphToSimpleGraphIso_apply ux)
    have huy : S.toGraphToSimpleGraphIso uy = ⟨y, hy⟩ :=
      Subtype.ext (S.coe_toGraphToSimpleGraphIso_apply uy)
    have hr := S.toGraphToSimpleGraphIso.reachable_iff.mpr
      ((Graph.toSimpleGraph_reachable_iff (G := S.toGraph) (u := ux) (v := uy)).mpr h)
    rw [hux, huy] at hr
    exact ⟨hx, hy, hr⟩
  · let ux : V(S.toGraph) := ⟨x, S.vertexSet_toGraph.symm ▸ hx⟩
    let uy : V(S.toGraph) := ⟨y, S.vertexSet_toGraph.symm ▸ hy⟩
    have hux : S.toGraphToSimpleGraphIso ux = ⟨x, hx⟩ :=
      Subtype.ext (S.coe_toGraphToSimpleGraphIso_apply ux)
    have huy : S.toGraphToSimpleGraphIso uy = ⟨y, hy⟩ :=
      Subtype.ext (S.coe_toGraphToSimpleGraphIso_apply uy)
    rw [← hux, ← huy] at hr
    exact (Graph.toSimpleGraph_reachable_iff (G := S.toGraph) (u := ux) (v := uy)).mp
      (S.toGraphToSimpleGraphIso.reachable_iff.mp hr)

@[simp]
theorem connected_toGraph_iff : S.toGraph.Connected ↔ S.Connected := by
  rw [Graph.connected_iff_toSimpleGraph_connected, ← S.toGraphToSimpleGraphIso.symm.connected_iff,
    ← Subgraph.connected_iff']

@[simp]
theorem isForest_toGraph_iff : S.toGraph.IsForest ↔ S.coe.IsAcyclic :=
  S.ofSimpleGraphCoeIso.isForest_iff.trans Graph.isForest_ofSimpleGraph_iff

@[simp]
theorem isEdgeConnected_toGraph_iff (k : ℕ) :
    S.toGraph.IsEdgeConnected k ↔ S.coe.IsEdgeConnected k :=
  (S.ofSimpleGraphCoeIso.isEdgeConnected_iff k).trans
    (Graph.isEdgeConnected_ofSimpleGraph_iff S.coe k)

@[simp]
theorem edgeConnectivity_toGraph :
    S.toGraph.edgeConnectivity = S.coe.edgeConnectivity :=
  S.ofSimpleGraphCoeIso.edgeConnectivity_eq.trans (Graph.edgeConnectivity_ofSimpleGraph S.coe)

@[simp]
theorem isVertexConnected_toGraph_iff (k : ℕ) :
    S.toGraph.IsVertexConnected k ↔ S.coe.IsVertexConnected k :=
  S.toGraphToSimpleGraphIso.isVertexConnected_iff.symm

@[simp]
theorem vertexConnectivity_toGraph :
    S.toGraph.vertexConnectivity = S.coe.vertexConnectivity :=
  S.toGraphToSimpleGraphIso.vertexConnectivity_eq.symm

end SimpleGraph.Subgraph

namespace Graph

/-- `Graph.ofSimpleGraph H` is connected as a multigraph if and only if `H` is connected. -/
@[simp]
theorem connected_ofSimpleGraph_iff {α : Type u} (H : SimpleGraph α) :
    (Graph.ofSimpleGraph H).Connected ↔ H.Connected := by
  rw [connected_iff_toSimpleGraph_connected, (toSimpleGraphOfSimpleGraphIso H).connected_iff]

end Graph

namespace SimpleGraph

/-- Every preconnected simple graph with finitely many edges has a finite vertex type: either `α` is
a subsingleton, or every vertex is incident to at least one edge of `H`. -/
theorem Preconnected.finite_of_finite_edgeSet {α : Type u} {H : SimpleGraph α} [Finite H.edgeSet]
    (hH : H.Preconnected) : Finite α := by
  by_cases hsub : Subsingleton α
  · exact Finite.of_subsingleton
  · rw [not_subsingleton_iff_nontrivial] at hsub
    have hpair : ∀ s : Sym2 α, {x : α | x ∈ s}.Finite :=
      Sym2.ind fun u v ↦ by
        have hset : {x : α | x ∈ s(u, v)} = {u, v} := by ext; simp
        rw [hset]
        exact (Set.finite_singleton v).insert u
    have hf : (⋃ e : H.edgeSet, {x : α | x ∈ (e : Sym2 α)}).Finite :=
      Set.finite_iUnion fun e ↦ hpair e.1
    refine Set.finite_univ_iff.mp (hf.subset fun x _ ↦ ?_)
    obtain ⟨y, hyx⟩ := exists_ne x
    obtain ⟨p⟩ := hH x y
    cases p with
    | nil => exact (hyx rfl).elim
    | @cons _ z _ hadj _ =>
      exact Set.mem_iUnion.mpr ⟨⟨s(x, z), H.mem_edgeSet.mpr hadj⟩, Sym2.mem_mk_left x z⟩

end SimpleGraph
