/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.Basic
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.EdgeSide
import TauCeti.Combinatorics.SimpleGraph.Finite

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
* `IsCutTree.of_isMinimum_edgeSide`: a tree whose edges all leave minimum cuts between their ends
  is a cut tree for the weights given by those minimum cut values.

Neither property assumes symmetry or submodularity of `f`. The results here take the tree as
given; for symmetric submodular `f`, a cut tree always exists by the Gomory–Hu theorem
`TauCeti.TerminalCut.exists_isCutTree`.

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

/-- A tree is a cut tree as soon as deleting any of its edges leaves a minimum cut between the
ends of that edge, with the edge weighted by their minimum cut value: flow-equivalence then
follows from the ultrametric inequality along tree paths. -/
theorem of_isMinimum_edgeSide (hT : T.IsTree)
    (hmin : ∀ ⦃u v : V⦄, T.Adj u v → IsMinimum f {u} {v} (T.edgeSide u v))
    (hw : ∀ ⦃u v : V⦄, T.Adj u v → w s(u, v) = pairMinimumValue f u v) : IsCutTree f T w := by
  -- An edge on a tree path separates its ends, so its weight bounds their minimum cut value.
  have hle ⦃s t : V⦄ ⦃p : T.Walk s t⦄ (hp : p.IsPath) ⦃e : Sym2 V⦄ (he : e ∈ p.edges) :
      pairMinimumValue f s t ≤ w e := by
    induction e using Sym2.ind with | _ a b => ?_
    have hab := p.adj_of_mem_edges he
    rcases (hT.connected.preconnected a s).mem_edgeSide_or_mem_edgeSide (v := b) with hs | hs
    · rw [hw hab, (hmin hab).pairMinimumValue_eq]
      exact pairMinimumValue_le f hs ((hp.mem_edges_iff_notMem_edgeSide hT.isAcyclic hs).mp he)
    · rw [Sym2.eq_swap] at he ⊢
      rw [hw hab.symm, (hmin hab.symm).pairMinimumValue_eq]
      exact pairMinimumValue_le f hs ((hp.mem_edges_iff_notMem_edgeSide hT.isAcyclic hs).mp he)
  -- Along any walk between distinct vertices, some edge weighs at most their minimum cut value.
  have hex ⦃s t : V⦄ (p : T.Walk s t) (hst : s ≠ t) :
      ∃ e ∈ p.edges, w e ≤ pairMinimumValue f s t := by
    induction p with
    | nil => exact absurd rfl hst
    | @cons s v t hsv q ih =>
      obtain rfl | hvt := eq_or_ne v t
      · exact ⟨s(s, v), by simp, (hw hsv).le⟩
      obtain ⟨e, he, hwe⟩ := ih hvt
      rcases min_le_iff.mp (min_pairMinimumValue_le f hst v) with h | h
      · exact ⟨s(s, v), by simp, (hw hsv).trans_le h⟩
      · exact ⟨e, by simp [he], hwe.trans h⟩
  exact
    { isTree := hT
      le_weight := hle
      exists_weight_eq := fun s t hst p hp ↦
        let ⟨e, he, hwe⟩ := hex p hst
        ⟨e, he, le_antisymm hwe (hle hp he)⟩
      isMinimum_edgeSide := hmin }

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

/-- A minimum-weight edge of a cut tree leaves a side minimizing the set function among all
nonempty proper vertex sets. -/
theorem exists_edgeSide_apply_le (hT : IsCutTree f T w) [Nontrivial V] :
    ∃ u v, T.Adj u v ∧ ∀ S : Finset V, S.Nonempty → S ≠ univ →
      f (T.edgeSide u v) ≤ f S := by
  have hTne : T ≠ ⊥ := by
    intro h
    rw [h] at hT
    exact SimpleGraph.not_preconnected_bot hT.isTree.connected.preconnected
  obtain ⟨u, v, huv, hmin⟩ := T.exists_minimum_weight_edge hTne w
  refine ⟨u, v, huv, fun S hS hSuniv ↦ ?_⟩
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ : ∃ t, t ∉ S := by
    by_contra! h
    exact hSuniv (eq_univ_iff_forall.mpr h)
  exact hT.apply_edgeSide_le huv hmin hs ht

end IsCutTree

end CutTree

end TauCeti.TerminalCut
