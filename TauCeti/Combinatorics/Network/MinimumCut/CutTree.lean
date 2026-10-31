/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.Basic
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.EdgeSide
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Flow-equivalent trees and cut trees

Let `f` be a set function on a finite vertex type, with minimum cut values
`λ(s, t) = pairMinimumValue f s t`. A tree `T` on the same vertex type with edge weights `w` is
**flow-equivalent** for `f` when, for any two distinct vertices, `λ(s, t)` is the minimum weight on
the tree path from `s` to `t`. It is a **cut tree** (a Gomory–Hu tree) when moreover, for every
tree edge `s(u, v)`, the side of `u` left by deleting that edge is a minimum `u`–`v` cut.

This file develops what these properties give, independently of how such a tree is constructed:

* `IsFlowEquivalentTree.reachable_deleteEdges_iff`: the threshold partition. Deleting the tree
  edges of weight below `k` leaves `s` and `t` connected exactly when `s = t` or `k ≤ λ(s, t)`.
* `IsCutTree.isMinimum_edgeSide_of_mem_edges`: the query theorem. A minimum-weight edge on the tree
  path from `s` to `t` yields a minimum `s`–`t` cut by deleting that edge.
* `IsCutTree.apply_edgeSide_le`: deleting a tree edge of minimum weight gives a side that
  minimizes `f` among all sets separating two vertices, with value that minimum weight.
* `IsFlowEquivalentTree.card_image_pairMinimumValue_le`: the minimum cut values between distinct
  vertices take at most `|V| - 1` distinct values, since each is a tree-edge weight.

Neither property assumes symmetry or submodularity of `f`. The results here take the tree as
given; for symmetric submodular `f`, Gomory and Hu show that a cut tree always exists.

## References

* R. E. Gomory and T. C. Hu, *Multi-terminal network flows*, J. SIAM 9 (1961), 551–570.
* D. Gusfield, *Very Simple Methods for All Pairs Network Flow Analysis*, SIAM J. Comput. 19
  (1990), 143–155.
* B. Korte and J. Vygen, *Combinatorial Optimization: Theory and Algorithms*, Section 8.6.
-/

public section

namespace TauCeti.TerminalCut

open Finset SimpleGraph

variable {V K : Type*}

section FlowEquivalent

variable [Finite V] [Zero K] [LinearOrder K]

/-- A tree `T` on the vertex type with edge weights `w` is flow-equivalent for `f` when the minimum
cut value between any two distinct vertices is the minimum weight on the tree path between them.
Only the weights of tree edges matter. -/
structure IsFlowEquivalentTree (f : Finset V → K) (T : SimpleGraph V) (w : Sym2 V → K) :
    Prop where
  /-- The graph is a tree. -/
  isTree : T.IsTree
  /-- Every edge on a tree path weighs at least the minimum cut value between its ends. -/
  le_weight ⦃s t : V⦄ ⦃p : T.Walk s t⦄ (hp : p.IsPath) ⦃e : Sym2 V⦄ (he : e ∈ p.edges) :
    pairMinimumValue f s t ≤ w e
  /-- Some edge on a tree path between distinct vertices attains the minimum cut value. -/
  exists_weight_eq ⦃s t : V⦄ (hst : s ≠ t) ⦃p : T.Walk s t⦄ (hp : p.IsPath) :
    ∃ e ∈ p.edges, w e = pairMinimumValue f s t

namespace IsFlowEquivalentTree

variable {f : Finset V → K} {T : SimpleGraph V} {w : Sym2 V → K}

/-- The weight of a tree edge is the minimum cut value between its ends. -/
theorem weight_eq (hT : IsFlowEquivalentTree f T w) {u v : V} (huv : T.Adj u v) :
    w s(u, v) = pairMinimumValue f u v := by
  obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq huv.ne huv.isPath_toWalk
  simp only [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at he
  rwa [he] at hwe

/-- **Threshold partition.** Deleting the tree edges of weight below `k` leaves two vertices
connected exactly when they are equal or their minimum cut value is at least `k`. -/
theorem reachable_deleteEdges_iff (hT : IsFlowEquivalentTree f T w) (k : K) {s t : V} :
    (T.deleteEdges {e | w e < k}).Reachable s t ↔ s = t ∨ k ≤ pairMinimumValue f s t := by
  classical
  refine ⟨fun ⟨q⟩ ↦ or_iff_not_imp_left.mpr fun hst ↦ ?_, ?_⟩
  · -- The path from `s` to `t` avoiding light edges is the tree path; it has an edge of weight
    -- equal to the minimum cut value.
    have hp : (q.toPath.val.mapLe (T.deleteEdges_le _)).IsPath := q.toPath.property.mapLe _
    obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
    rw [Walk.edges_mapLe_eq_edges] at he
    have := q.toPath.val.edges_subset_edgeSet he
    simp only [edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_ofPred_eq, not_lt] at this
    exact hwe ▸ this.2
  · rintro (rfl | hk)
    · rfl
    obtain ⟨p, hp, -⟩ := hT.isTree.existsUnique_path s t
    exact ⟨p.toDeleteEdges _ fun e he ↦ not_lt.mpr (hk.trans (hT.le_weight hp he))⟩

/-- Any set separating two vertices has value at least the weight of some tree edge. -/
theorem exists_weight_le (hT : IsFlowEquivalentTree f T w) {S : Finset V} {s t : V}
    (hs : s ∈ S) (ht : t ∉ S) : ∃ e ∈ T.edgeSet, w e ≤ f S := by
  have hst : s ≠ t := fun h ↦ ht (h ▸ hs)
  obtain ⟨p, hp, -⟩ := hT.isTree.existsUnique_path s t
  obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
  exact ⟨e, p.edges_subset_edgeSet he, hwe ▸ pairMinimumValue_le f hs ht⟩

/-- The minimum cut values between distinct vertices take at most `|V| - 1` distinct values,
since each is the weight of a tree edge. -/
theorem card_image_pairMinimumValue_le [Fintype V] [DecidableEq V] [DecidableEq K]
    (hT : IsFlowEquivalentTree f T w) :
    #((univ.filter fun p : V × V ↦ p.1 ≠ p.2).image fun p ↦ pairMinimumValue f p.1 p.2) ≤
      Fintype.card V - 1 := by
  classical
  have hsub : ((univ.filter fun p : V × V ↦ p.1 ≠ p.2).image fun p ↦ pairMinimumValue f p.1 p.2) ⊆
      T.edgeFinset.image w := by
    simp only [subset_iff, mem_image, mem_filter, mem_univ, true_and, mem_edgeFinset,
      forall_exists_index, and_imp, Prod.forall]
    rintro _ s t hst rfl
    obtain ⟨p, hp, -⟩ := hT.isTree.existsUnique_path s t
    obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
    exact ⟨e, p.edges_subset_edgeSet he, hwe⟩
  have hcard := hT.isTree.card_edgeFinset
  exact (card_le_card hsub).trans (card_image_le.trans (by omega))

end IsFlowEquivalentTree

end FlowEquivalent

section CutTree

variable [Fintype V] [Zero K] [LinearOrder K]

/-- A cut tree, or Gomory–Hu tree, for `f`: a flow-equivalent tree in which, for every tree edge
`s(u, v)`, the side of `u` left by deleting that edge is a minimum `u`–`v` cut. -/
structure IsCutTree (f : Finset V → K) (T : SimpleGraph V) (w : Sym2 V → K) : Prop
    extends IsFlowEquivalentTree f T w where
  /-- Deleting a tree edge leaves a minimum cut between its ends. -/
  isMinimum_edgeSide ⦃u v : V⦄ (huv : T.Adj u v) : IsMinimum f {u} {v} (T.edgeSide u v)

namespace IsCutTree

variable {f : Finset V → K} {T : SimpleGraph V} {w : Sym2 V → K}

/-- The side left by deleting a tree edge has value equal to the weight of that edge. -/
theorem apply_edgeSide (hT : IsCutTree f T w) {u v : V} (huv : T.Adj u v) :
    f (T.edgeSide u v) = w s(u, v) := by
  rw [hT.weight_eq huv, (hT.isMinimum_edgeSide huv).pairMinimumValue_eq]

/-- **Query theorem.** If `s(u, v)` has minimum weight on the tree path from `s` to `t`, and `s`
lies on the side of `u`, then that side is a minimum `s`–`t` cut. Since the two sides of a tree
edge cover the vertices, one of the orientations `(u, v)` and `(v, u)` applies. -/
theorem isMinimum_edgeSide_of_mem_edges (hT : IsCutTree f T w) {s t u v : V} {p : T.Walk s t}
    (hp : p.IsPath) (huv : s(u, v) ∈ p.edges) (hmin : ∀ e ∈ p.edges, w s(u, v) ≤ w e)
    (hs : s ∈ T.edgeSide u v) : IsMinimum f {s} {t} (T.edgeSide u v) := by
  have ht : t ∉ T.edgeSide u v :=
    (hp.mem_edges_iff_notMem_edgeSide hT.isTree.isAcyclic hs).mp huv
  have hst : s ≠ t := fun h ↦ ht (h ▸ hs)
  obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
  have hw : w s(u, v) = pairMinimumValue f s t :=
    le_antisymm (hwe ▸ hmin e he) (hT.le_weight hp huv)
  rw [isMinimum_singleton_iff_pairMinimumValue_eq]
  exact ⟨hs, ht, by rw [hT.apply_edgeSide (p.adj_of_mem_edges huv), hw]⟩

/-- **Global minimum cut.** Deleting a tree edge of minimum weight gives a side whose value is at
most that of every set separating two vertices. -/
theorem apply_edgeSide_le (hT : IsCutTree f T w) {u v : V} (huv : T.Adj u v)
    (hmin : ∀ e ∈ T.edgeSet, w s(u, v) ≤ w e) {S : Finset V} {s t : V} (hs : s ∈ S)
    (ht : t ∉ S) : f (T.edgeSide u v) ≤ f S := by
  obtain ⟨e, he, hle⟩ := hT.exists_weight_le hs ht
  rw [hT.apply_edgeSide huv]
  exact (hmin e he).trans hle

end IsCutTree

end CutTree

/-!
## Examples

On four vertices, let `f S = min (|S|, 4 - |S|)`. Every two distinct vertices have minimum cut
value one, so any tree with unit weights is flow-equivalent for `f`. The unit-weight star is a cut
tree, but the unit-weight path is not: deleting its middle edge leaves a side of value two. Thus
flow-equivalence records the numerical minimum cut values without their minimizing cuts.
-/

/-- The balanced cut function on four vertices. -/
private def balanced (S : Finset (Fin 4)) : ℕ := min #S (4 - #S)

private theorem balanced_compl (S : Finset (Fin 4)) : balanced Sᶜ = balanced S := by
  have h : #S ≤ 4 := by simpa using card_le_univ S
  simp only [balanced, card_compl, Fintype.card_fin]
  omega

private theorem pairMinimumValue_balanced {s t : Fin 4} (hst : s ≠ t) :
    pairMinimumValue balanced s t = 1 := by
  obtain ⟨S, hS⟩ := exists_minimum balanced (disjoint_singleton.mpr hst)
  obtain ⟨hs, ht⟩ := isAdmissible_singleton.mp hS.admissible
  refine le_antisymm ((pairMinimumValue_le balanced (mem_singleton_self s)
    (notMem_singleton.mpr hst.symm)).trans (by simp [balanced])) ?_
  have h1 : 0 < #S := card_pos.mpr ⟨s, hs⟩
  have h2 : #S < 4 := by simpa using card_lt_univ_of_notMem ht
  rw [hS.pairMinimumValue_eq, balanced]
  omega

/-- Every unit-weight tree on four vertices is flow-equivalent for the balanced cut function. -/
private theorem isFlowEquivalentTree_balanced {T : SimpleGraph (Fin 4)} (hT : T.IsTree) :
    IsFlowEquivalentTree balanced T fun _ ↦ 1 where
  isTree := hT
  le_weight s t _ _ _ _ := by
    rcases eq_or_ne s t with rfl | hst
    · simp
    · rw [pairMinimumValue_balanced hst]
  exists_weight_eq s t hst p _ := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges
      (by rw [Ne, Walk.edges_eq_nil]; exact Walk.not_nil_of_ne hst)
    exact ⟨e, he, (pairMinimumValue_balanced hst).symm⟩

/-- The unit-weight star is a cut tree for the balanced cut function. -/
example : IsCutTree balanced (starGraph 0) fun _ ↦ 1 := by
  refine ⟨isFlowEquivalentTree_balanced (isTree_starGraph 0), fun u v huv ↦ ?_⟩
  have hbridge : (starGraph (0 : Fin 4)).IsBridge s(u, v) :=
    isAcyclic_iff_forall_adj_isBridge.mp (isAcyclic_starGraph 0) huv
  have hleaf : ∀ {a b : Fin 4}, a ≠ 0 → (starGraph 0).edgeSide a b = {a} ∨ b ≠ 0 := by
    intro a b ha
    by_cases hb : b = 0
    · subst hb
      exact .inl (edgeSide_eq_singleton fun y hy ↦ by simp_all [starGraph_adj])
    · exact .inr hb
  -- One end of a star edge is the centre; the side of the leaf is a singleton, and the side of
  -- the centre is its complement.
  have hval : balanced ((starGraph 0).edgeSide u v) = 1 := by
    rw [starGraph_adj] at huv
    rcases huv with ⟨hne, rfl | rfl⟩
    · rw [← balanced_compl, hbridge.compl_edgeSide (connected_starGraph 0).preconnected,
        (hleaf hne.symm).resolve_right (not_not.mpr rfl)]
      rfl
    · rw [(hleaf hne).resolve_right (not_not.mpr rfl)]
      rfl
  rw [isMinimum_singleton_iff_pairMinimumValue_eq, pairMinimumValue_balanced huv.ne]
  exact ⟨self_mem_edgeSide _ u v, hbridge.notMem_edgeSide, hval⟩

/-- The unit-weight path is flow-equivalent for the balanced cut function. -/
example : IsFlowEquivalentTree balanced (pathGraph 4) fun _ ↦ 1 :=
  isFlowEquivalentTree_balanced (isTree_pathGraph_add_one 3)

/-- The unit-weight path is not a cut tree for the balanced cut function: deleting its middle edge
leaves the side `{0, 1}`, of value two. -/
example : ¬IsCutTree balanced (pathGraph 4) fun _ ↦ 1 := by
  intro hT
  have h12 : (pathGraph 4).Adj 1 2 := by simp [pathGraph_adj]
  have hbridge : (pathGraph 4).IsBridge s(1, 2) :=
    isAcyclic_iff_forall_adj_isBridge.mp (isAcyclic_pathGraph 4) h12
  have hside : (pathGraph 4).edgeSide 1 2 = {0, 1} := by
    have h0 : (0 : Fin 4) ∈ (pathGraph 4).edgeSide 1 2 :=
      mem_edgeSide.mpr (deleteEdges_adj.mpr ⟨by simp [pathGraph_adj], by decide⟩).reachable
    have h3 : (3 : Fin 4) ∈ (pathGraph 4).edgeSide 2 1 :=
      mem_edgeSide.mpr (deleteEdges_adj.mpr ⟨by simp [pathGraph_adj], by decide⟩).reachable
    have h2 := hbridge.notMem_edgeSide
    ext x
    fin_cases x
    · simpa using h0
    · simp
    · simpa using h2
    · simpa using fun h ↦ Finset.disjoint_left.mp hbridge.disjoint_edgeSide h h3
  have := hT.apply_edgeSide h12
  rw [hside] at this
  exact absurd this (by decide)

end TauCeti.TerminalCut
