/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Connectivity.EdgeSide

/-!
# Spanning forests and the exchange property

A spanning forest of a simple graph `G` is an acyclic subgraph `F ≤ G` on the same vertices with
the same reachability relation as `G` (`SimpleGraph.IsSpanningForest`). Disconnected graphs are
not excluded: a spanning forest is a spanning tree of every connected component, and the spanning
forests of a connected graph are exactly its spanning trees. These are the objects of which
minimum spanning forests are the lightest.

For a spanning forest `F` of `G`, every edge `uv` of `G` has a unique path of `F` between its ends,
the forest path. Removing an edge `f` of `F` and adding `uv` gives again a spanning forest exactly
when `f` lies on that path; in the language of fundamental cycles and cuts, exactly when `f` lies
on the fundamental cycle of `uv`. Two spanning forests can moreover exchange edges symmetrically:
for an edge `e` of `F'` outside `F` there is an edge `f` of `F` outside `F'` such that both
`F - f + e` and `F' - e + f` are spanning forests. No finiteness is assumed anywhere except in the
edge count.

## Main definitions

* `SimpleGraph.IsSpanningForest F G`: `F ≤ G`, `F` is acyclic and `F.Reachable = G.Reachable`.

## Main results

* `SimpleGraph.isSpanningForest_iff_maximal`: the spanning forests of `G` are its maximal acyclic
  subgraphs.
* `SimpleGraph.Connected.isSpanningForest_iff_le_and_isTree`: the spanning forests of a connected
  graph are its spanning trees.
* `SimpleGraph.IsSpanningForest.ncard_edgeSet_add_card_connectedComponent`: on `n` vertices, a
  spanning forest of a graph with `c` connected components has `n - c` edges.
* `SimpleGraph.IsSpanningForest.existsUnique_path`: a spanning forest has exactly one path between
  any two vertices joined in `G`.
* `SimpleGraph.isSpanningForest_exchange_iff`: the exchange criterion. For an edge `uv` of `G` with
  forest path `p` and an edge `f` of `F`, the graph `F - f + uv` is a spanning forest of `G` if and
  only if `f` lies on `p`.
* `SimpleGraph.IsSpanningForest.exists_exchange_of_walk`: an edge `uv` of the forest can be
  exchanged for an edge of any walk of `G` from `u` to `v`.
* `SimpleGraph.IsSpanningForest.exists_symm_exchange`: the symmetric exchange property.
* `SimpleGraph.IsSpanningForest.exists_cut_exchange`,
  `SimpleGraph.IsSpanningForest.exists_cycle_exchange`: an edge of `G` leaving a set `S` of
  vertices can be exchanged for an edge of the forest leaving `S`, and an edge of the forest on a
  cycle of `G` can be exchanged for an edge of that cycle outside the forest. These are the
  exchanges behind the cut and cycle properties of minimum spanning forests.

## References

* Reinhard Diestel, *Graph Theory*, sixth edition, Springer, 2025, §1.5 and §1.9.
* Richard A. Brualdi, *Comments on bases in dependence structures*, Bull. Austral. Math. Soc. 1
  (1969), 161–167, for the symmetric exchange property of bases.
-/

public section

namespace SimpleGraph

variable {V : Type*} {F F' G H : SimpleGraph V} {u v : V}

/-- `F` is a spanning forest of `G`: an acyclic subgraph of `G` on the same vertices with the same
reachability relation as `G`, that is, a spanning tree of every connected component of `G`.
When `G` is connected these are the spanning trees of `G`
(`SimpleGraph.Connected.isSpanningForest_iff_le_and_isTree`). -/
structure IsSpanningForest (F G : SimpleGraph V) : Prop where
  /-- A spanning forest is a subgraph. -/
  le : F ≤ G
  /-- A spanning forest has no cycle. -/
  isAcyclic : F.IsAcyclic
  /-- A spanning forest joins exactly the vertices that `G` joins. -/
  reachable_eq : F.Reachable = G.Reachable

/-- The spanning forests of `G` are its maximal acyclic subgraphs. -/
theorem isSpanningForest_iff_maximal :
    F.IsSpanningForest G ↔ Maximal (fun K ↦ K ≤ G ∧ K.IsAcyclic) F :=
  ⟨fun hF ↦ (maximal_isAcyclic_iff_reachable_eq hF.le hF.isAcyclic).mpr hF.reachable_eq,
    fun h ↦ ⟨h.prop.1, h.prop.2, G.reachable_eq_of_maximal_isAcyclic F h⟩⟩

/-- Every acyclic subgraph of `G` extends to a spanning forest of `G`. -/
theorem IsAcyclic.exists_isSpanningForest_ge (hH : H.IsAcyclic) (hHG : H ≤ G) :
    ∃ F : SimpleGraph V, H ≤ F ∧ F.IsSpanningForest G := by
  obtain ⟨F, hHF, hFG, hF, hreach⟩ := G.exists_isAcyclic_reachable_eq_le_of_le_of_isAcyclic hHG hH
  exact ⟨F, hHF, hFG, hF, hreach⟩

/-- Every graph has a spanning forest. -/
theorem exists_isSpanningForest (G : SimpleGraph V) : ∃ F : SimpleGraph V, F.IsSpanningForest G :=
  let ⟨F, hFG, hF, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
  ⟨F, hFG, hF, hreach⟩

/-- A graph is a spanning forest of itself exactly when it is acyclic. -/
@[simp]
theorem isSpanningForest_self_iff : G.IsSpanningForest G ↔ G.IsAcyclic :=
  ⟨IsSpanningForest.isAcyclic, fun h ↦ ⟨le_rfl, h, rfl⟩⟩

/-- The graph without edges is its own only spanning forest. -/
@[simp]
theorem isSpanningForest_bot_iff : F.IsSpanningForest ⊥ ↔ F = ⊥ :=
  ⟨fun hF ↦ le_bot_iff.mp hF.le, by rintro rfl; exact isSpanningForest_self_iff.mpr isAcyclic_bot⟩

/-- The spanning forests of a connected graph are its spanning trees. -/
theorem Connected.isSpanningForest_iff_le_and_isTree (hG : G.Connected) :
    F.IsSpanningForest G ↔ F ≤ G ∧ F.IsTree := by
  rw [isSpanningForest_iff_maximal]
  exact ⟨fun h ↦ ⟨h.prop.1, (hG.maximal_le_isAcyclic_iff_isTree h.prop.1).mp h⟩,
    fun h ↦ (hG.maximal_le_isAcyclic_iff_isTree h.1).mpr h.2⟩

namespace IsSpanningForest

/-- Two vertices are joined in a spanning forest of `G` exactly when they are joined in `G`. -/
theorem reachable_iff (hF : F.IsSpanningForest G) : F.Reachable u v ↔ G.Reachable u v := by
  rw [hF.reachable_eq]

/-- A spanning forest of a connected graph is a tree. -/
theorem isTree (hF : F.IsSpanningForest G) (hG : G.Connected) : F.IsTree :=
  ((hG.isSpanningForest_iff_le_and_isTree).mp hF).2

/-- **The forest path.** A spanning forest of `G` has exactly one path between two vertices
joined in `G`, in particular between the ends of every edge of `G`. -/
theorem existsUnique_path (hF : F.IsSpanningForest G) (h : G.Reachable u v) :
    ∃! p : F.Walk u v, p.IsPath :=
  (hF.reachable_iff.mpr h).elim_path fun p ↦
    ⟨p.val, p.property, fun q hq ↦
      congrArg Subtype.val ((hF.isAcyclic.subsingleton_path u v).elim ⟨q, hq⟩ p)⟩

/-- A spanning forest of `G` has as many connected components as `G`. -/
theorem card_connectedComponent (hF : F.IsSpanningForest G) :
    Nat.card F.ConnectedComponent = Nat.card G.ConnectedComponent :=
  Nat.card_congr (F.connectedComponentEquivOfReachableEq hF.reachable_eq)

/-- **Edge count of a spanning forest.** On `n` vertices, a spanning forest of a graph with `c`
connected components has `n - c` edges. -/
theorem ncard_edgeSet_add_card_connectedComponent [Finite V] (hF : F.IsSpanningForest G) :
    F.edgeSet.ncard + Nat.card G.ConnectedComponent = Nat.card V := by
  rw [← hF.card_connectedComponent]
  exact hF.isAcyclic.ncard_edgeSet_add_card_connectedComponent

end IsSpanningForest

/-- **The exchange criterion.** Let `F` be a spanning forest of `G`, let `u`, `v` be adjacent in
`G` and let `p` be the path of `F` from `u` to `v`. For an edge `f` of `F`, removing `f` from `F`
and adding the edge `uv` gives a spanning forest of `G` exactly when `f` lies on `p`, that is, on
the fundamental cycle of `uv`. -/
theorem isSpanningForest_exchange_iff (hF : F.IsSpanningForest G) (huv : G.Adj u v) {f : Sym2 V}
    (hf : f ∈ F.edgeSet) {p : F.Walk u v} (hp : p.IsPath) :
    (F.deleteEdges {f} ⊔ edge u v).IsSpanningForest G ↔ f ∈ p.edges := by
  refine ⟨fun h ↦ by_contra fun hfp ↦ ?_, fun hfp ↦ ?_⟩
  · -- If `f` is off `p`, then `p` survives the deletion of `f`. Acyclicity then forces `uv` to be
    -- an edge of `F - f` already, and `F - f` no longer joins the ends of the bridge `f`.
    have hreach : (F.deleteEdges {f}).Reachable u v := ⟨p.toDeleteEdge f hfp⟩
    have hadj := ((isAcyclic_sup_fromEdgeSet_iff.mp h.isAcyclic).2 hreach).resolve_left huv.ne
    rw [sup_edge_of_adj _ hadj] at h
    induction f using Sym2.ind with
    | _ x y =>
      exact isBridge_iff.mp (isAcyclic_iff_forall_isBridge.mp hF.isAcyclic hf)
        (h.reachable_iff.mpr (hF.le ((mem_edgeSet _).mp hf)).reachable)
  · -- If `f` is on `p`, its deletion separates `u` from `v`, so adding `uv` closes no cycle.
    have hnr : ¬(F.deleteEdges {f}).Reachable u v :=
      (hp.mem_edges_iff_not_reachable_deleteEdges hF.isAcyclic).mp hfp
    refine ⟨sup_le ((F.deleteEdges_le _).trans hF.le) ((edge_le_iff (G := G)).mpr (.inr huv)),
      (hF.isAcyclic.anti (F.deleteEdges_le _)).sup_edge_of_not_reachable hnr, ?_⟩
    rw [p.reachable.reachable_deleteEdges_sup_edge_eq hnr, hF.reachable_eq]

/-- **Exchange along a walk.** Let `F` be a spanning forest of `G`, `uv` an edge of `F` and `q` a
walk from `u` to `v` in a subgraph `H` of `G`. Then some edge `xy` of `q` has its ends separated in
`F - uv`, and `uv` can be exchanged for it: the graph `F - uv + xy` is again a spanning forest
of `G`. -/
theorem IsSpanningForest.exists_exchange_of_walk (hF : F.IsSpanningForest G)
    (he : s(u, v) ∈ F.edgeSet) (q : H.Walk u v) (hH : H ≤ G) :
    ∃ x y, s(x, y) ∈ q.edges ∧ ¬(F.deleteEdges {s(u, v)}).Reachable x y ∧
      (F.deleteEdges {s(u, v)} ⊔ edge x y).IsSpanningForest G := by
  -- Since `uv` is a bridge of `F`, some edge `xy` of `q` leaves the side of `u` in `F - uv`.
  have hsep : ¬(F.deleteEdges {s(u, v)}).Reachable u v :=
    isBridge_iff.mp (isAcyclic_iff_forall_isBridge.mp hF.isAcyclic he)
  obtain ⟨⟨⟨x, y⟩, hxy⟩, hd, hx, hy⟩ :=
    q.exists_boundary_dart {z | (F.deleteEdges {s(u, v)}).Reachable u z} .rfl hsep
  simp only [Set.mem_ofPred_eq] at hx hy
  have hxy' : ¬(F.deleteEdges {s(u, v)}).Reachable x y := fun h ↦ hy (hx.trans h)
  have hG : G.Adj x y := hH hxy
  -- By duality `uv` lies on the forest path from `x` to `y`.
  obtain ⟨p, hp, -⟩ := hF.existsUnique_path hG.reachable
  exact ⟨x, y, q.edge_mem_edges_of_mem_darts hd, hxy',
    (isSpanningForest_exchange_iff hF hG he hp).mpr
      ((hp.mem_edges_iff_not_reachable_deleteEdges hF.isAcyclic).mpr hxy')⟩

/-- **Symmetric exchange.** For spanning forests `F`, `F'` of `G` and an edge `e` of `F'` that is
not in `F`, there is an edge `f` of `F` that is not in `F'` such that both `F - f + e` and
`F' - e + f` are spanning forests of `G`. -/
theorem IsSpanningForest.exists_symm_exchange (hF : F.IsSpanningForest G)
    (hF' : F'.IsSpanningForest G) {e : Sym2 V} (he : e ∈ F'.edgeSet) (heF : e ∉ F.edgeSet) :
    ∃ f ∈ F.edgeSet, f ∉ F'.edgeSet ∧
      (F.deleteEdges {f} ⊔ fromEdgeSet {e}).IsSpanningForest G ∧
      (F'.deleteEdges {e} ⊔ fromEdgeSet {f}).IsSpanningForest G := by
  induction e using Sym2.ind with
  | _ u v =>
    -- The edge `e` of `F'` can be exchanged for an edge `f = s(x, y)` of the `F`-path from `u` to
    -- `v` whose ends are separated in `F' - e`.
    have huv : F'.Adj u v := (mem_edgeSet _).mp he
    obtain ⟨p, hp, -⟩ := hF.existsUnique_path (hF'.le huv).reachable
    obtain ⟨x, y, hfp, hxy', hF'xy⟩ := hF'.exists_exchange_of_walk he p hF.le
    have hf : s(x, y) ∈ F.edgeSet := p.edges_subset_edgeSet hfp
    refine ⟨s(x, y), hf, fun hf' ↦ hxy' ?_, ?_, ?_⟩
    · -- `f ≠ e` because `f ∈ F` and `e ∉ F`, so an edge `f` of `F'` would survive in `F' - e`.
      have hne : s(x, y) ≠ s(u, v) := fun h ↦ heF (h ▸ hf)
      exact (deleteEdges_adj.mpr ⟨hf', Set.notMem_singleton_iff.mpr hne⟩).reachable
    · rw [← edge]
      exact (isSpanningForest_exchange_iff hF (hF'.le huv) hf hp).mpr hfp
    · rwa [← edge]

/-- **Exchange across a cut.** Let `F` be a spanning forest of `G` and `uv` an edge of `G` leaving
a set `S` of vertices. Then some edge `xy` of `F` leaving `S` can be exchanged for `uv`: the graph
`F - xy + uv` is again a spanning forest of `G`. -/
theorem IsSpanningForest.exists_cut_exchange (hF : F.IsSpanningForest G) (huv : G.Adj u v)
    {S : Set V} (hu : u ∈ S) (hv : v ∉ S) :
    ∃ x y, F.Adj x y ∧ x ∈ S ∧ y ∉ S ∧
      (F.deleteEdges {s(x, y)} ⊔ edge u v).IsSpanningForest G := by
  obtain ⟨p, hp, -⟩ := hF.existsUnique_path huv.reachable
  obtain ⟨⟨⟨x, y⟩, hxy⟩, hd, hx, hy⟩ := p.exists_boundary_dart S hu hv
  exact ⟨x, y, hxy, hx, hy, (isSpanningForest_exchange_iff hF huv ((mem_edgeSet _).mpr hxy) hp).mpr
    (p.edge_mem_edges_of_mem_darts hd)⟩

/-- **Exchange along a cycle.** Let `F` be a spanning forest of `G` and `e` an edge of `F` on a
cycle `c` of `G`. Then `e` can be exchanged for some edge `xy` of `c` outside `F`: the graph
`F - e + xy` is again a spanning forest of `G`. -/
theorem IsSpanningForest.exists_cycle_exchange (hF : F.IsSpanningForest G) {a : V}
    {c : G.Walk a a} (hc : c.IsCycle) {e : Sym2 V} (hec : e ∈ c.edges) (heF : e ∈ F.edgeSet) :
    ∃ x y, s(x, y) ∈ c.edges ∧ ¬F.Adj x y ∧
      (F.deleteEdges {e} ⊔ edge x y).IsSpanningForest G := by
  induction e using Sym2.ind with
  | _ u v =>
    -- The edges of `c` other than `uv` join `u` to `v`: in the graph `H` of the edges of `c`, the
    -- edge `uv` lies on the cycle `c`, so it is not a bridge.
    set H := fromEdgeSet c.edgeSet
    have hH : ∀ e ∈ c.edges, e ∈ H.edgeSet := fun e he ↦ by
      rw [edgeSet_fromEdgeSet]
      exact ⟨he, G.not_isDiag_of_mem_edgeSet (c.edges_subset_edgeSet he)⟩
    obtain ⟨-, ⟨q⟩⟩ := adj_and_reachable_delete_edges_iff_exists_cycle.mpr
      ⟨a, c.transfer H hH, hc.transfer hH, by rwa [Walk.edges_transfer]⟩
    -- The bridge `uv` of `F` can be exchanged for an edge `xy` of `q`.
    obtain ⟨x, y, hxyq, hxy', hF'⟩ := hF.exists_exchange_of_walk heF q
      fun _ _ h ↦ c.adj_of_mem_edges ((fromEdgeSet_adj _).mp (deleteEdges_adj.mp h).1).1
    obtain ⟨hxyH, hne⟩ := deleteEdges_adj.mp (q.adj_of_mem_edges hxyq)
    exact ⟨x, y, ((fromEdgeSet_adj _).mp hxyH).1,
      fun h ↦ hxy' (deleteEdges_adj.mpr ⟨h, hne⟩).reachable, hF'⟩

end SimpleGraph
