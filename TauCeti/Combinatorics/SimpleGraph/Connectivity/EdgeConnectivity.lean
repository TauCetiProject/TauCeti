/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Data.ENat.Lattice

/-!
# The edge connectivity of a simple graph

Mathlib's `SimpleGraph.IsEdgeConnected G k` says that `G` stays preconnected after deleting any
set of fewer than `k` edges. This file introduces the numerical invariant
`G.edgeConnectivity : ℕ∞`, the supremum of the natural thresholds at which `G` is edge-connected,
and bounds it by vertex degrees. As for multigraphs, a graph on at most one vertex has edge
connectivity `⊤`. It also lifts walks and trails in `G` with `toSubgraph ≤ K` to reachability in
edge-deleted subgraphs of `K.coe`, showing without finiteness assumptions that every closed trail
(and in particular every cycle) traces a `2`-edge-connected subgraph.

The supremum definition and the degree bounds follow the proposal
[mathlib4#42494](https://github.com/leanprover-community/mathlib4/pull/42494), and the invariant
matches the multigraph `Graph.edgeConnectivity` on `Graph.ofSimpleGraph`.

## Main definitions

* `SimpleGraph.edgeConnectivity G`: the supremum in `ℕ∞` of the natural thresholds `k` at which
  `G` is `k`-edge-connected.

## Main results

* `SimpleGraph.isEdgeConnected_iff_le_edgeConnectivity`: the invariant records exactly the
  thresholds in `ℕ∞` at which `G` is edge-connected.
* `SimpleGraph.edgeConnectivity_le_degree`, `SimpleGraph.edgeConnectivity_le_minDegree`: on at
  least two vertices, edge connectivity is at most every degree, hence at most the minimum degree.
* `SimpleGraph.edgeConnectivity_eq_top_iff`: on a finite vertex type, edge connectivity is `⊤`
  exactly when there is at most one vertex.
* `SimpleGraph.Walk.reachable_deleteEdges_coe`,
  `SimpleGraph.Walk.IsTrail.reachable_deleteEdges_coe_or_reachable_deleteEdges_coe`: lifting walks
  and trails in `G` with `toSubgraph ≤ K` to reachability in edge-deleted subgraphs of `K.coe`.
* `SimpleGraph.Walk.IsTrail.isEdgeConnected_two_toSubgraph`,
  `SimpleGraph.Walk.IsCycle.isEdgeConnected_two_toSubgraph`: the subgraph traced by a closed trail
  (in particular, a cycle) is `2`-edge-connected.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G H : SimpleGraph V} {k : ℕ∞}

variable (G) in
/-- The edge connectivity of a simple graph: the supremum in `ℕ∞` of the natural thresholds `k` at
which it is `k`-edge-connected. It is `⊤` when there is at most one vertex. -/
noncomputable def edgeConnectivity : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsEdgeConnected k), (k : ℕ∞)

/-- Edge connectivity records exactly the thresholds at which the graph is edge-connected. -/
theorem isEdgeConnected_iff_le_edgeConnectivity : G.IsEdgeConnected k ↔ k ≤ G.edgeConnectivity := by
  have hnat (n : ℕ) : G.IsEdgeConnected n ↔ n ≤ G.edgeConnectivity :=
    (Antitone.natCast_le_iSup_iff
      (fun _ _ hmn (h : G.IsEdgeConnected _) u v ↦ (h u v).anti (Nat.cast_le.2 hmn)) .zero).symm
  cases k with
  | top => simp [isEdgeConnected_top_iff_forall_nat, hnat, ENat.eq_top_iff_forall_ge]
  | coe n => exact hnat n

/-- Edge connectivity is monotone in the graph. -/
@[gcongr]
theorem edgeConnectivity_mono (hGH : G ≤ H) : G.edgeConnectivity ≤ H.edgeConnectivity :=
  iSup_mono fun _ ↦ iSup_mono' fun hk ↦ ⟨fun u v ↦ (hk u v).mono hGH, le_rfl⟩

/-- A graph on at most one vertex has edge connectivity `⊤`. -/
@[simp]
theorem edgeConnectivity_eq_top_of_subsingleton [Subsingleton V] : G.edgeConnectivity = ⊤ :=
  top_le_iff.1 (isEdgeConnected_iff_le_edgeConnectivity.1 .of_subsingleton)

/-! ### Degree bounds -/

/-- On at least two vertices, edge connectivity is at most the degree of every vertex of finite
degree. -/
theorem edgeConnectivity_le_degree [Nontrivial V] (u : V) [Fintype (G.neighborSet u)] :
    G.edgeConnectivity ≤ G.degree u :=
  (isEdgeConnected_iff_le_edgeConnectivity.2 le_rfl).le_degree

/-- On a finite vertex type with at least two vertices, a `k`-edge-connected graph has minimum
degree at least `k`. -/
theorem IsEdgeConnected.le_minDegree [Fintype V] [DecidableRel G.Adj] [Nontrivial V]
    (h : G.IsEdgeConnected k) : k ≤ G.minDegree := by
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  rw [hu]
  exact h.le_degree

/-- On a finite vertex type with at least two vertices, edge connectivity is at most the minimum
degree. -/
theorem edgeConnectivity_le_minDegree [Fintype V] [DecidableRel G.Adj] [Nontrivial V] :
    G.edgeConnectivity ≤ G.minDegree :=
  (isEdgeConnected_iff_le_edgeConnectivity.2 le_rfl).le_minDegree

/-- On a finite vertex type, edge connectivity is `⊤` exactly when there is at most one vertex. -/
theorem edgeConnectivity_eq_top_iff [Finite V] : G.edgeConnectivity = ⊤ ↔ Subsingleton V := by
  refine ⟨fun h ↦ ?_, fun _ ↦ edgeConnectivity_eq_top_of_subsingleton⟩
  by_contra hV
  rw [not_subsingleton_iff_nontrivial] at hV
  have := Fintype.ofFinite V
  classical
  obtain ⟨u⟩ := (inferInstance : Nonempty V)
  exact ENat.natCast_ne_top (G.degree u) (top_le_iff.1 (h ▸ G.edgeConnectivity_le_degree u))

/-! ### Subgraph walks and cycle connectivity -/

/-- If a walk `p` in `G` has `p.toSubgraph ≤ K` and uses none of the underlying edges of
`s : Set (Sym2 K.verts)`, then its endpoints are reachable in `K.coe.deleteEdges s`. -/
theorem Walk.reachable_deleteEdges_coe {K : G.Subgraph} {s : Set (Sym2 K.verts)} {u v : V}
    (p : G.Walk u v) (hpK : p.toSubgraph ≤ K) (hps : ∀ e ∈ s, e.map Subtype.val ∉ p.edges) :
    (K.coe.deleteEdges s).Reachable ⟨u, hpK.1 p.start_mem_verts_toSubgraph⟩
      ⟨v, hpK.1 p.end_mem_verts_toSubgraph⟩ := by
  let pK := p.mapToSubgraph.map (Subgraph.inclusion hpK)
  refine (pK.toDeleteEdges s fun e he hes ↦ hps e hes ?_).reachable
  have hedges : pK.edges.map (Sym2.map Subtype.val) = p.edges := calc
    pK.edges.map (Sym2.map Subtype.val)
      = (p.mapToSubgraph.edges.map (Sym2.map (Subgraph.inclusion hpK))).map
          (Sym2.map Subtype.val) := by rw [Walk.edges_map]
    _ = p.mapToSubgraph.edges.map (Sym2.map p.toSubgraph.hom) := by
        rw [List.map_map]
        congr 1
        ext x
        cases x using Sym2.ind
        rfl
    _ = (p.mapToSubgraph.map p.toSubgraph.hom).edges := (Walk.edges_map _ _).symm
    _ = p.edges := congrArg Walk.edges p.map_mapToSubgraph_hom
  exact hedges ▸ List.mem_map_of_mem he

/-- Along a trail `p : G.Walk u v` with `p.toSubgraph ≤ K`, deleting any single edge `f` of `K.coe`
leaves every vertex on `p` reachable from `u` or from `v` in `K.coe.deleteEdges {f}`. -/
theorem Walk.IsTrail.reachable_deleteEdges_coe_or_reachable_deleteEdges_coe {K : G.Subgraph}
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) (hpK : p.toSubgraph ≤ K) (f : Sym2 K.verts)
    {w : V} (hw : w ∈ p.support) :
    (K.coe.deleteEdges {f}).Reachable ⟨w, hpK.1 (p.mem_verts_toSubgraph.mpr hw)⟩
      ⟨u, hpK.1 p.start_mem_verts_toSubgraph⟩ ∨
    (K.coe.deleteEdges {f}).Reachable ⟨w, hpK.1 (p.mem_verts_toSubgraph.mpr hw)⟩
      ⟨v, hpK.1 p.end_mem_verts_toSubgraph⟩ := by
  classical
  let p₁ := p.takeUntil w hw
  let p₂ := p.dropUntil w hw
  have hspec : p₁.append p₂ = p := p.take_spec hw
  have hp₁K : p₁.toSubgraph ≤ K :=
    le_trans le_sup_left (by rw [← Walk.toSubgraph_append, hspec]; exact hpK)
  have hp₂K : p₂.toSubgraph ≤ K :=
    le_trans le_sup_right (by rw [← Walk.toSubgraph_append, hspec]; exact hpK)
  by_cases hf₁ : f.map Subtype.val ∈ p₁.edges
  · have hf₂ : f.map Subtype.val ∉ p₂.edges :=
      hp.disjoint_edges_takeUntil_dropUntil hw hf₁
    exact Or.inr (p₂.reachable_deleteEdges_coe hp₂K (Set.forall_mem_singleton.mpr hf₂))
  · exact Or.inl (p₁.reachable_deleteEdges_coe hp₁K (Set.forall_mem_singleton.mpr hf₁)).symm

/-- The subgraph traced by any closed trail in a simple graph is `2`-edge-connected, with no
finiteness assumption. -/
theorem Walk.IsTrail.isEdgeConnected_two_toSubgraph {u : V} {c : G.Walk u u} (hc : c.IsTrail) :
    c.toSubgraph.coe.IsEdgeConnected 2 := by
  rw [isEdgeConnected_two_iff_forall_preconnected]
  intro f a b
  have ha : a.1 ∈ c.support := c.mem_verts_toSubgraph.mp a.2
  have hb : b.1 ∈ c.support := c.mem_verts_toSubgraph.mp b.2
  let u₀ : c.toSubgraph.verts := ⟨_, c.start_mem_verts_toSubgraph⟩
  have hra : (c.toSubgraph.coe.deleteEdges {f}).Reachable a u₀ := by
    rcases hc.reachable_deleteEdges_coe_or_reachable_deleteEdges_coe le_rfl f ha with h | h <;>
      exact h
  have hrb : (c.toSubgraph.coe.deleteEdges {f}).Reachable b u₀ := by
    rcases hc.reachable_deleteEdges_coe_or_reachable_deleteEdges_coe le_rfl f hb with h | h <;>
      exact h
  exact hra.trans hrb.symm

/-- The subgraph traced by any cycle in a simple graph is `2`-edge-connected, with no finiteness
assumption. -/
theorem Walk.IsCycle.isEdgeConnected_two_toSubgraph {u : V} {c : G.Walk u u} (hc : c.IsCycle) :
    c.toSubgraph.coe.IsEdgeConnected 2 :=
  hc.isTrail.isEdgeConnected_two_toSubgraph

end SimpleGraph
