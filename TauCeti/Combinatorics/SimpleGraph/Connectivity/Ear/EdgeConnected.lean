/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Ear.Basic

/-!
# Ear decompositions of `2`-edge-connected simple graphs

A finite simple graph on a nonempty vertex type is `2`-edge-connected exactly when it can be built
from one vertex by repeatedly adjoining open or closed ears. One direction holds without any
finiteness assumption and is `SimpleGraph.EarDecomposition.isEdgeConnected_two`; this file proves
the converse.

The extension step needs no finiteness. A non-bridge edge `uv` leaving a subgraph `H`, with
`u ∈ H` and `v ∉ H`, lies on an ear: after deleting `uv`, a path leads from `v` back to `u`, and
stopping it at its first vertex `w` of `H` gives a closed ear when `w = u` and an open ear
otherwise. In a `2`-edge-connected graph no edge is a bridge, so every proper subgraph with a
vertex admits an ear: if it misses a vertex, connectivity supplies an edge leaving it; otherwise
it misses an edge, which is a single-edge open ear. On a finite vertex type the subgraphs form a
finite lattice, so adjoining ears until the whole graph is reached extends every ear decomposition
of a subgraph to one of `⊤` with the same initial subgraph.

## Main results

* `SimpleGraph.Adj.exists_ear_mem_edges`: a non-bridge edge leaving a subgraph lies on an ear over
  that subgraph.
* `SimpleGraph.IsEdgeConnected.exists_ear`: in a `2`-edge-connected graph, every proper subgraph
  with a vertex admits an ear.
* `SimpleGraph.IsEdgeConnected.exists_earDecomposition_of_earDecomposition`: in a finite
  `2`-edge-connected graph, every ear decomposition of a subgraph extends to one of `⊤` with the
  same initial subgraph.
* `SimpleGraph.IsEdgeConnected.exists_earDecomposition_initial_eq_singletonSubgraph`: such a graph
  has an ear decomposition of `⊤` starting at any prescribed vertex.
* `SimpleGraph.isEdgeConnected_two_iff_exists_earDecomposition_initial_eq_singletonSubgraph`,
  `SimpleGraph.isEdgeConnected_two_iff_nonempty_earDecomposition`: the ear characterizations of
  finite `2`-edge-connected simple graphs.

## References

* H. E. Robbins, *A theorem on graphs, with an application to a problem of traffic control*,
  Amer. Math. Monthly 46 (1939), 281--283.
* R. Diestel, *Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017,
  Section 3.1.
-/

public section

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {H : G.Subgraph}

/-- A non-bridge edge from a vertex of `H` to a vertex outside `H` lies on an open or closed ear
over `H`. No finiteness assumption is needed. -/
theorem Adj.exists_ear_mem_edges {u v : V} (huv : G.Adj u v) (hu : u ∈ H.verts)
    (hv : v ∉ H.verts) (hb : ¬G.IsBridge s(u, v)) :
    ∃ e : G.Ear H, s(u, v) ∈ e.toWalk.2.2.edges := by
  classical
  -- A path `q` from `v` back to `u` avoiding the edge `uv`.
  have hreach : (G.deleteEdges {s(u, v)}).Reachable v u := by
    by_contra h
    exact hb (isBridge_iff.mpr fun h' ↦ h h'.symm)
  obtain ⟨p, hp⟩ := reachable_deleteEdges_iff_exists_walk.mp hreach
  let q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  -- Stop `q` at its first vertex `w` in `H`.
  let s : Finset V := {x ∈ q.support.toFinset | x ∈ H.verts}
  obtain ⟨w, hws, hwq, hfirst⟩ := q.exists_mem_support_forall_mem_support_imp_eq s
    ⟨u, by simp [s, hu]⟩
  have hw : w ∈ H.verts := (Finset.mem_filter.mp hws).2
  let r := q.takeUntil w hwq
  have hr : r.IsPath := hq.takeUntil hwq
  have hrH : ∀ x ∈ r.support, x ∈ H.verts → x = w := fun x hx hxH ↦
    hfirst x (by simp [s, q.support_takeUntil_subset_support hwq hx, hxH]) hx
  have hre : s(u, v) ∉ r.edges := fun h ↦
    hp (p.edges_bypass_subset_edges (q.edges_takeUntil_subset_edges hwq h))
  -- Every edge of `cons huv r` is new: `uv` has the new end `v`, and an edge of `H` on `r`
  -- would have both ends equal to `w`.
  have hedge : ∀ e ∈ (Walk.cons huv r).edges, e ∉ H.edgeSet := by
    intro e he heH
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact hv (H.edge_vert (Subgraph.mem_edgeSet.mp heH).symm)
    · induction e using Sym2.ind with
      | _ a b =>
        have hab := Subgraph.mem_edgeSet.mp heH
        have ha := hrH a (r.fst_mem_support_of_mem_edges he) (H.edge_vert hab)
        have hb := hrH b (r.snd_mem_support_of_mem_edges he) (H.edge_vert hab.symm)
        exact hab.ne (ha.trans hb.symm)
  by_cases huw : u = w
  · subst w
    refine ⟨.closed (Walk.cons huv r) ((Walk.cons_isCycle_iff r huv).mpr ⟨hr, hre⟩) hu ?_, ?_⟩
    · intro x hx hxu hxH
      rw [Walk.support_cons, List.mem_cons] at hx
      exact hxu (hrH x (hx.resolve_left hxu) hxH)
    · rw [Ear.toWalk_closed]; simp
  · have hur : u ∉ r.support := fun h ↦ huw (hrH u h hu)
    have hint : ∀ x ∈ (Walk.cons huv r).support, x ≠ u → x ≠ w → x ∉ H.verts := by
      intro x hx hxu hxw hxH
      rw [Walk.support_cons, List.mem_cons] at hx
      exact hxw (hrH x (hx.resolve_left hxu) hxH)
    exact ⟨.«open» (Walk.cons huv r) ((Walk.cons_isPath_iff huv r).mpr ⟨hr, hur⟩) hu hw huw
      hint hedge, by rw [Ear.toWalk_open]; simp⟩

/-- In a `2`-edge-connected simple graph, every proper subgraph with at least one vertex admits an
open or closed ear. No finiteness assumption is needed. -/
theorem IsEdgeConnected.exists_ear (hG : G.IsEdgeConnected 2) (hH : H ≠ ⊤)
    (hverts : H.verts.Nonempty) : Nonempty (G.Ear H) := by
  by_cases hspan : H.IsSpanning
  · obtain ⟨e, -⟩ := hspan.exists_open_ear hH
    exact ⟨e⟩
  · obtain ⟨y, hy⟩ : ∃ y, y ∉ H.verts := by simpa [Subgraph.IsSpanning] using hspan
    obtain ⟨x, hx⟩ := hverts
    obtain ⟨p⟩ := hG.preconnected two_ne_zero x y
    obtain ⟨d, -, hd₁, hd₂⟩ := p.exists_boundary_dart H.verts hx hy
    obtain ⟨e, -⟩ := d.adj.exists_ear_mem_edges hd₁ hd₂
      (isEdgeConnected_two_iff_forall_not_isBridge.mp hG _)
    exact ⟨e⟩

/-- In a `2`-edge-connected simple graph on a finite vertex type, every ear decomposition of a
subgraph extends to an ear decomposition of `⊤` with the same initial subgraph. -/
theorem IsEdgeConnected.exists_earDecomposition_of_earDecomposition [Finite V]
    (hG : G.IsEdgeConnected 2) (d₀ : G.EarDecomposition H) :
    ∃ d : G.EarDecomposition (⊤ : G.Subgraph), d.initial = d₀.initial := by
  induction H using WellFoundedGT.induction with
  | ind H ih =>
    by_cases htop : H = ⊤
    · exact ⟨d₀.copy htop, d₀.initial_copy htop⟩
    · obtain ⟨e⟩ := hG.exists_ear htop d₀.connected_final.nonempty
      obtain ⟨d, hinit⟩ := ih e.adjoin e.lt_adjoin (d₀.snoc e)
      exact ⟨d, hinit.trans (d₀.initial_snoc e)⟩

/-- A `2`-edge-connected simple graph on a finite vertex type has an ear decomposition of `⊤`
starting at any prescribed vertex. -/
theorem IsEdgeConnected.exists_earDecomposition_initial_eq_singletonSubgraph [Finite V]
    (hG : G.IsEdgeConnected 2) (v : V) :
    ∃ d : G.EarDecomposition (⊤ : G.Subgraph), d.initial = G.singletonSubgraph v := by
  obtain ⟨d, hinit⟩ := hG.exists_earDecomposition_of_earDecomposition (.vertex G v)
  exact ⟨d, hinit.trans (EarDecomposition.initial_vertex v)⟩

/-- **Ear characterization of `2`-edge-connectivity.** A simple graph on a finite nonempty vertex
type is `2`-edge-connected exactly when it can be built from one vertex by adjoining open or
closed ears. -/
theorem isEdgeConnected_two_iff_exists_earDecomposition_initial_eq_singletonSubgraph [Finite V]
    [Nonempty V] :
    G.IsEdgeConnected 2 ↔
      ∃ (v : V) (d : G.EarDecomposition (⊤ : G.Subgraph)), d.initial = G.singletonSubgraph v :=
  ⟨fun hG ↦ ⟨_, hG.exists_earDecomposition_initial_eq_singletonSubgraph (Classical.arbitrary V)⟩,
    fun ⟨_, d, _⟩ ↦ d.isEdgeConnected_two⟩

/-- A simple graph on a finite nonempty vertex type is `2`-edge-connected exactly when it has an
ear decomposition of `⊤`, starting from either a vertex or a cycle. -/
theorem isEdgeConnected_two_iff_nonempty_earDecomposition [Finite V] [Nonempty V] :
    G.IsEdgeConnected 2 ↔ Nonempty (G.EarDecomposition (⊤ : G.Subgraph)) :=
  ⟨fun hG ↦
      (hG.exists_earDecomposition_initial_eq_singletonSubgraph (Classical.arbitrary V)).nonempty,
    fun ⟨d⟩ ↦ d.isEdgeConnected_two⟩

end SimpleGraph
