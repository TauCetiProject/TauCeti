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
* `SimpleGraph.IsSpanningForest.exists_symm_exchange`: the symmetric exchange property.

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
    -- The ends of `e` are separated in `F' - e`, so the `F`-path from `u` to `v` has an edge
    -- `f = s(x, y)` whose ends are separated in `F' - e`.
    have huv : F'.Adj u v := (mem_edgeSet _).mp he
    have hsep : ¬(F'.deleteEdges {s(u, v)}).Reachable u v :=
      isBridge_iff.mp (isAcyclic_iff_forall_isBridge.mp hF'.isAcyclic he)
    obtain ⟨p, hp, -⟩ := hF.existsUnique_path (hF'.le huv).reachable
    obtain ⟨⟨⟨x, y⟩, hxy⟩, hd, hx, hy⟩ :=
      p.exists_boundary_dart {z | (F'.deleteEdges {s(u, v)}).Reachable u z} .rfl hsep
    simp only [Set.mem_ofPred_eq] at hx hy
    have hxy' : ¬(F'.deleteEdges {s(u, v)}).Reachable x y := fun h ↦ hy (hx.trans h)
    have hf : s(x, y) ∈ F.edgeSet := (mem_edgeSet _).mpr hxy
    have hfp : s(x, y) ∈ p.edges := p.edge_mem_edges_of_mem_darts hd
    refine ⟨s(x, y), hf, fun hf' ↦ hxy' ?_, ?_, ?_⟩
    · -- `f ≠ e` because `f ∈ F` and `e ∉ F`, so an edge `f` of `F'` would survive in `F' - e`.
      have hne : s(x, y) ≠ s(u, v) := fun h ↦ heF (h ▸ hf)
      exact (deleteEdges_adj.mpr ⟨hf', Set.notMem_singleton_iff.mpr hne⟩).reachable
    · rw [← edge]
      exact (isSpanningForest_exchange_iff hF (hF'.le huv) hf hp).mpr hfp
    · -- By duality `e` lies on the `F'`-path from `x` to `y`.
      obtain ⟨q, hq, -⟩ := hF'.existsUnique_path (hF.le hxy).reachable
      rw [← edge]
      exact (isSpanningForest_exchange_iff hF' (hF.le hxy) he hq).mpr
        ((hq.mem_edges_iff_not_reachable_deleteEdges hF'.isAcyclic).mpr hxy')

end SimpleGraph
