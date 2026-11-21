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

Mathlib's `SimpleGraph.IsEdgeReachable G k u v` says that `u` and `v` stay reachable after deleting
any set of fewer than `k` edges, and `SimpleGraph.IsEdgeConnected G k` requires this for every pair.
This file introduces the numerical invariants `G.edgeReachability u v` and `G.edgeConnectivity`,
the suprema in `ℕ∞` of the natural thresholds at which the corresponding predicates hold, and
bounds them by vertex degrees. As for multigraphs, a graph on at most one vertex has edge
connectivity `⊤`. It also lifts walks and trails in `G` with `toSubgraph ≤ K` to reachability in
edge-deleted subgraphs of `K.coe`, showing without finiteness assumptions that every closed trail
(and in particular every cycle) traces a `2`-edge-connected subgraph.

The supremum definitions and the degree bounds follow the proposal
[mathlib4#42494](https://github.com/leanprover-community/mathlib4/pull/42494), and the invariants
match `Graph.edgeReachability` and `Graph.edgeConnectivity` on `Graph.ofSimpleGraph`.

## Main definitions

* `SimpleGraph.edgeReachability G u v`: the supremum in `ℕ∞` of the natural thresholds `k` at
  which `u` and `v` are `k`-edge-reachable.
* `SimpleGraph.edgeConnectivity G`: the supremum in `ℕ∞` of the natural thresholds `k` at which
  `G` is `k`-edge-connected.

## Main results

* `SimpleGraph.isEdgeReachable_iff_le_edgeReachability`: local edge reachability records exactly
  the thresholds in `ℕ∞` at which two vertices are edge-reachable.
* `SimpleGraph.isEdgeConnected_iff_le_edgeConnectivity`: the invariant records exactly the
  thresholds in `ℕ∞` at which `G` is edge-connected.
* `SimpleGraph.edgeConnectivity_eq_iInf_edgeReachability`: edge connectivity is the least local
  edge reachability between any pair of vertices.
* `SimpleGraph.edgeReachability_le_degree`: local edge reachability between distinct vertices is
  at most the degree of either endpoint when that degree is finite.
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
/-- The local edge reachability of two vertices: the supremum in `ℕ∞` of the natural thresholds
`k` at which they are `k`-edge-reachable. -/
noncomputable def edgeReachability (u v : V) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsEdgeReachable k u v), (k : ℕ∞)

variable (G) in
/-- The edge connectivity of a simple graph: the supremum in `ℕ∞` of the natural thresholds `k` at
which it is `k`-edge-connected. It is `⊤` when there is at most one vertex. -/
noncomputable def edgeConnectivity : ℕ∞ :=
  ⨆ (k : ℕ) (_ : G.IsEdgeConnected k), (k : ℕ∞)

/-- Injective graph homomorphisms preserve local edge reachability. -/
theorem IsEdgeReachable.map {W : Type*} {H : SimpleGraph W} {u v : V}
    (h : G.IsEdgeReachable k u v) (f : G →g H) (hf : Function.Injective f) :
    H.IsEdgeReachable k (f u) (f v) := by
  intro s hs
  let f' : G.deleteEdges (Sym2.map f ⁻¹' s) →g H.deleteEdges s :=
    { toFun := f
      map_rel' {a b} hab := by
        rw [deleteEdges_adj] at hab ⊢
        exact ⟨f.map_adj hab.1, by simpa using hab.2⟩ }
  apply (h (lt_of_le_of_lt ?_ hs)).map f'
  rw [← (Sym2.map.injective hf).encard_image]
  exact Set.encard_le_encard (Set.image_preimage_subset _ _)

namespace Iso

/-- Local edge reachability is invariant under graph isomorphism. -/
theorem isEdgeReachable_iff {W : Type*} {H : SimpleGraph W} (e : G ≃g H) (u v : V) :
    H.IsEdgeReachable k (e u) (e v) ↔ G.IsEdgeReachable k u v :=
  ⟨fun h ↦ by simpa using h.map e.symm.toHom e.symm.injective,
    fun h ↦ h.map e.toHom e.injective⟩

end Iso

/-- Local edge reachability records exactly the thresholds at which two vertices are
edge-reachable. -/
theorem isEdgeReachable_iff_le_edgeReachability {u v : V} :
    G.IsEdgeReachable k u v ↔ k ≤ G.edgeReachability u v := by
  have hnat (n : ℕ) : G.IsEdgeReachable n u v ↔ n ≤ G.edgeReachability u v :=
    (Antitone.natCast_le_iSup_iff
      (fun _ _ hmn (h : G.IsEdgeReachable _ u v) ↦ h.anti (Nat.cast_le.2 hmn)) .zero).symm
  cases k with
  | top => simp [isEdgeReachable_top_iff_forall_nat, hnat, ENat.eq_top_iff_forall_ge]
  | coe n => exact hnat n

/-- Local edge reachability is at most `k` exactly when every reachable natural threshold is at
most `k`. -/
theorem edgeReachability_le_iff {u v : V} :
    G.edgeReachability u v ≤ k ↔ ∀ n : ℕ, G.IsEdgeReachable n u v → (n : ℕ∞) ≤ k := by
  refine ⟨fun h n hn ↦ (isEdgeReachable_iff_le_edgeReachability.mp hn).trans h, fun h ↦ ?_⟩
  exact ENat.forall_natCast_le_iff_le.mp fun n hn ↦
    h n (isEdgeReachable_iff_le_edgeReachability.mpr hn)

/-- Edge connectivity records exactly the thresholds at which the graph is edge-connected. -/
theorem isEdgeConnected_iff_le_edgeConnectivity : G.IsEdgeConnected k ↔ k ≤ G.edgeConnectivity := by
  have hnat (n : ℕ) : G.IsEdgeConnected n ↔ n ≤ G.edgeConnectivity :=
    (Antitone.natCast_le_iSup_iff
      (fun _ _ hmn (h : G.IsEdgeConnected _) u v ↦ (h u v).anti (Nat.cast_le.2 hmn)) .zero).symm
  cases k with
  | top => simp [isEdgeConnected_top_iff_forall_nat, hnat, ENat.eq_top_iff_forall_ge]
  | coe n => exact hnat n

/-- Local edge reachability is monotone in the graph. -/
@[gcongr]
theorem edgeReachability_mono (hGH : G ≤ H) (u v : V) :
    G.edgeReachability u v ≤ H.edgeReachability u v :=
  iSup_mono fun _ ↦ iSup_mono' fun hk ↦ ⟨hk.mono hGH, le_rfl⟩

/-- Edge connectivity is monotone in the graph. -/
@[gcongr]
theorem edgeConnectivity_mono (hGH : G ≤ H) : G.edgeConnectivity ≤ H.edgeConnectivity :=
  iSup_mono fun _ ↦ iSup_mono' fun hk ↦ ⟨fun u v ↦ (hk u v).mono hGH, le_rfl⟩

/-- Local edge reachability is symmetric in its endpoints. -/
theorem edgeReachability_comm (u v : V) : G.edgeReachability u v = G.edgeReachability v u :=
  ENat.eq_of_forall_natCast_le_iff fun _ ↦ by
    simp only [← isEdgeReachable_iff_le_edgeReachability, isEdgeReachable_comm]

/-- A vertex has infinite local edge reachability with itself. -/
@[simp]
theorem edgeReachability_self (u : V) : G.edgeReachability u u = ⊤ :=
  top_unique (isEdgeReachable_iff_le_edgeReachability.mp .rfl)

/-- Local edge reachability satisfies the ultrametric triangle inequality. -/
theorem min_edgeReachability_le (u v w : V) :
    min (G.edgeReachability u v) (G.edgeReachability v w) ≤ G.edgeReachability u w :=
  ENat.forall_natCast_le_iff_le.mp fun _ hk ↦
    isEdgeReachable_iff_le_edgeReachability.mp
      ((isEdgeReachable_iff_le_edgeReachability.mpr (le_min_iff.mp hk).1).trans
        (isEdgeReachable_iff_le_edgeReachability.mpr (le_min_iff.mp hk).2))

namespace Iso

/-- Local numerical edge reachability is unchanged by a graph isomorphism. -/
@[simp]
theorem edgeReachability_eq {W : Type*} {H : SimpleGraph W} (e : G ≃g H) (u v : V) :
    H.edgeReachability (e u) (e v) = G.edgeReachability u v :=
  ENat.eq_of_forall_natCast_le_iff fun _ ↦ by
    simp only [← isEdgeReachable_iff_le_edgeReachability, e.isEdgeReachable_iff]

end Iso

/-- Edge connectivity is the infimum of the local edge reachabilities between all pairs of
vertices. -/
theorem edgeConnectivity_eq_iInf_edgeReachability (G : SimpleGraph V) :
    G.edgeConnectivity = ⨅ u, ⨅ v, G.edgeReachability u v :=
  ENat.eq_of_forall_natCast_le_iff fun _ ↦ by
    simp only [le_iInf_iff, ← isEdgeReachable_iff_le_edgeReachability,
      ← isEdgeConnected_iff_le_edgeConnectivity, IsEdgeConnected]

/-- Edge connectivity is at most the local edge reachability between any two vertices. -/
theorem edgeConnectivity_le_edgeReachability (u v : V) :
    G.edgeConnectivity ≤ G.edgeReachability u v := by
  rw [edgeConnectivity_eq_iInf_edgeReachability]
  exact iInf_le_of_le u (iInf_le_of_le v le_rfl)

/-- A graph on at most one vertex has edge connectivity `⊤`. -/
@[simp]
theorem edgeConnectivity_eq_top_of_subsingleton [Subsingleton V] : G.edgeConnectivity = ⊤ :=
  top_le_iff.1 (isEdgeConnected_iff_le_edgeConnectivity.1 .of_subsingleton)

/-! ### Degree bounds -/

/-- The local edge reachability between distinct vertices is at most the degree of the first
vertex when that degree is finite. By symmetry, the same bound holds at the other endpoint. -/
theorem edgeReachability_le_degree {u v : V} (huv : u ≠ v) [Fintype (G.neighborSet u)] :
    G.edgeReachability u v ≤ G.degree u :=
  ENat.forall_natCast_le_iff_le.mp fun _ hk ↦
    ((isEdgeReachable_iff_le_edgeReachability.mpr hk).le_degree huv)

/-- When `u` has finite degree, the local edge reachability from `u` is `⊤` exactly at `u`
itself. In particular, on a finite or locally finite graph it is `⊤` exactly on the diagonal. -/
@[simp]
theorem edgeReachability_eq_top_iff {u v : V} [Finite (G.neighborSet u)] :
    G.edgeReachability u v = ⊤ ↔ u = v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ edgeReachability_self u⟩
  by_contra huv
  let _ := Fintype.ofFinite (G.neighborSet u)
  exact ENat.natCast_ne_top (G.degree u)
    (top_le_iff.1 (h ▸ G.edgeReachability_le_degree huv))

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

/-! ### Induced subgraphs -/

/-- A bridge remains a bridge in an induced subgraph containing both of its endpoints. -/
theorem IsBridge.induce {u v : V} (hb : G.IsBridge s(u, v)) {C : Set V} (hu : u ∈ C)
    (hv : v ∈ C) : (G.induce C).IsBridge s(⟨u, hu⟩, ⟨v, hv⟩) := by
  by_cases h : G.Adj u v
  · have huv : (G.induce C).Adj ⟨u, hu⟩ ⟨v, hv⟩ := induce_adj.mpr h
    apply (isBridge_iff_forall_cycle_notMem huv).mpr
    intro z p hp hep
    have hp' : (p.map (Embedding.induce (G := G) C).toHom).IsCycle :=
      hp.map (f := (Embedding.induce (G := G) C).toHom)
        (Embedding.induce (G := G) C).injective
    apply hb.notMem_edges_of_isCycle hp'
    rw [Walk.edges_map]
    simpa using List.mem_map_of_mem
      (f := Sym2.map ((Embedding.induce (G := G) C) : C → V)) hep
  · rw [isBridge_iff]
    intro hreach
    apply (isBridge_iff.mp hb)
    rw [deleteEdges_eq_self.mpr (by simpa [Set.disjoint_singleton_right] using h)]
    exact (hreach.mono (deleteEdges_le _)).map (Embedding.induce (G := G) C).toHom

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
  have ha : a.val ∈ c.support := c.mem_verts_toSubgraph.mp a.property
  have hb : b.val ∈ c.support := c.mem_verts_toSubgraph.mp b.property
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
