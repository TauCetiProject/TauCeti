/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Star
public import TauCeti.Combinatorics.Network.MinimumCut.Graph
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.CutCapacity
import TauCeti.Combinatorics.Network.MinimumCut.Transport

/-!
# Cut trees for finite simple graphs

This file gives the native simple-graph specialization of the Gomory--Hu cut-tree theorem directly
on `V`, without passing through `V(Graph.ofSimpleGraph G)`. Unit cuts are measured by
`G.unitCutCapacity` (counting graph edges crossing to the complement), while general weighted cuts
are represented by `TauCeti.pairCutCapacity (G.edgeSet.indicator c)`.

A unit cut tree records local edge reachability as the minimum weight on each tree path, and a
minimum-weight path edge recovers an actual minimum cut of the original simple graph. Deleting tree
edges of weight below `k` leaves precisely the local `k`-edge-reachability classes, and when the
vertex type has at least two elements, a minimum-weight tree edge records the global edge
connectivity and certifies a minimum disconnecting edge cut.

## Main results

* `SimpleGraph.exists_isCutTree_indicator_edgeSet` and `SimpleGraph.exists_isUnitCutTree`: every
  nonempty finite simple graph admits weighted and unit cut trees directly on `V`.
* `SimpleGraph.isCutTree_ofSimpleGraph_iff` and `SimpleGraph.Iso.isCutTree_unitCutCapacity_iff`:
  equivalence with multigraph cut trees on `V(Graph.ofSimpleGraph G)` and invariance under graph
  isomorphisms.
* `IsFlowEquivalentTree.reachable_deleteEdges_iff_simpleGraph_isEdgeReachable`,
  `IsFlowEquivalentTree.simpleGraph_isEdgeReachable_iff_forall_le_weight`, and
  `IsFlowEquivalentTree.simpleGraph_isEdgeConnected_iff_forall_le_weight`: path-minimum, threshold,
  and global `k`-edge-connectivity characterizations on unit flow-equivalent trees.
* `IsFlowEquivalentTree.exists_edge_simpleGraph_edgeConnectivity_eq_weight` and
  `IsFlowEquivalentTree.simpleGraph_edgeConnectivity_eq_iInf_weight`: global edge connectivity is
  the minimum tree-edge weight.
* `IsCutTree.simpleGraph_edgeReachability_eq_unitCutCapacity_edgeSide`,
  `IsCutTree.not_reachable_deleteEdges_crossing_edgeSide`, `IsCutTree.encard_crossing_edgeSide_le`,
  and `IsCutTree.exists_edgeSide_crossing_eq_simpleGraph_edgeConnectivity`: minimum-cut recovery and
  edge-separator optimality certificates.
* `SimpleGraph.isCutTree_starGraph_top`: star cut trees for complete graphs.

## References

* R. E. Gomory and T. C. Hu, *Multi-terminal network flows*, J. SIAM 9 (1961), 551--570.
* D. Gusfield, *Very Simple Methods for All Pairs Network Flow Analysis*, SIAM J. Comput. 19
  (1990), 143--155.
* B. Korte and J. Vygen, *Combinatorial Optimization: Theory and Algorithms*, Section 8.6.

The simple-graph pairwise minimum-cut interface used here is developed in
`TauCeti.Combinatorics.Graph.Connectivity.Menger.CutValue`, and the multigraph existence and query
interface adapted here is developed in `TauCeti.Combinatorics.Network.MinimumCut.Graph`, especially
`Graph.exists_isUnitCutTree`, `IsFlowEquivalentTree.reachable_deleteEdges_iff_isEdgeReachable`,
and `IsCutTree.edgeReachability_eq_edgeCutCapacity_edgeSide`.
-/

public section

open Finset
open scoped Graph

namespace SimpleGraph

variable {V W K : Type*} (G : SimpleGraph V)

/-! ### Existence and transport of cut trees -/

/-- Every weighted finite simple graph on a nonempty vertex type with nonnegative edge weights
admits a cut tree directly on `V`. -/
theorem exists_isCutTree_indicator_edgeSet [Fintype V] [Nonempty V]
    [AddCommMonoid K] [LinearOrder K] [IsOrderedCancelAddMonoid K]
    (c : Sym2 V → K) (hc : ∀ p ∈ G.edgeSet, 0 ≤ c p) :
    ∃ (T : SimpleGraph V) (w : Sym2 V → K),
      TauCeti.TerminalCut.IsCutTree
        (TauCeti.pairCutCapacity (G.edgeSet.indicator c)) T w :=
  TauCeti.TerminalCut.exists_isCutTree_pairCutCapacity (G.edgeSet.indicator c) fun x y _ ↦ by
    by_cases h : s(x, y) ∈ G.edgeSet
    · rw [Set.indicator_of_mem h]
      exact hc _ h
    · rw [Set.indicator_of_notMem h]

/-- Every nonempty finite simple graph has a cut tree for unit edge capacities. -/
theorem exists_isUnitCutTree [Fintype V] [Nonempty V] (G : SimpleGraph V) :
    ∃ (T : SimpleGraph V) (w : Sym2 V → ℕ),
      TauCeti.TerminalCut.IsCutTree G.unitCutCapacity T w := by
  rw [G.unitCutCapacity_eq_pairCutCapacity]
  exact G.exists_isCutTree_indicator_edgeSet (fun _ ↦ 1) fun _ _ ↦ Nat.zero_le 1

/-- Relabelling along `G.ofSimpleGraphVertexEquiv` identifies flow-equivalent trees on `V` with
flow-equivalent trees on `V(Graph.ofSimpleGraph G)` for weights supported on `G.edgeSet`. -/
theorem isFlowEquivalentTree_ofSimpleGraph_iff [Fintype V] [AddCommMonoid K] [LinearOrder K]
    (c : Sym2 V → K) (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0)
    {T : SimpleGraph V} {w : Sym2 V → K} :
    TauCeti.TerminalCut.IsFlowEquivalentTree
        ((Graph.ofSimpleGraph G).edgeCutCapacity (G.ofSimpleGraphCapacity c))
        (T.map G.ofSimpleGraphVertexEquiv)
        (fun e ↦ w (e.map Subtype.val)) ↔
      TauCeti.TerminalCut.IsFlowEquivalentTree (TauCeti.pairCutCapacity c) T w :=
  TauCeti.TerminalCut.isFlowEquivalentTree_map_iff
    (SimpleGraph.Iso.map G.ofSimpleGraphVertexEquiv T)
    (fun S ↦ by
      have heq : S.map (Iso.map G.ofSimpleGraphVertexEquiv T).toEquiv.toEmbedding =
          G.toOfSimpleGraphFinset S := by
        rw [G.toOfSimpleGraphFinset_eq_map]
        rfl
      rw [heq]
      exact G.edgeCutCapacity_eq_pairCutCapacity c hsupport S)
    (fun a _ ↦ by
      induction a using Sym2.inductionOn with
      | _ x y => simp [Iso.map])

/-- Relabelling along `G.ofSimpleGraphVertexEquiv` identifies cut trees on `V` with cut trees on
`V(Graph.ofSimpleGraph G)` for weights supported on `G.edgeSet`. -/
theorem isCutTree_ofSimpleGraph_iff [Fintype V] [AddCommMonoid K] [LinearOrder K]
    (c : Sym2 V → K) (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0)
    {T : SimpleGraph V} {w : Sym2 V → K} :
    TauCeti.TerminalCut.IsCutTree
        ((Graph.ofSimpleGraph G).edgeCutCapacity (G.ofSimpleGraphCapacity c))
        (T.map G.ofSimpleGraphVertexEquiv)
        (fun e ↦ w (e.map Subtype.val)) ↔
      TauCeti.TerminalCut.IsCutTree (TauCeti.pairCutCapacity c) T w :=
  TauCeti.TerminalCut.isCutTree_map_iff
    (SimpleGraph.Iso.map G.ofSimpleGraphVertexEquiv T)
    (fun S ↦ by
      have heq : S.map (Iso.map G.ofSimpleGraphVertexEquiv T).toEquiv.toEmbedding =
          G.toOfSimpleGraphFinset S := by
        rw [G.toOfSimpleGraphFinset_eq_map]
        rfl
      rw [heq]
      exact G.edgeCutCapacity_eq_pairCutCapacity c hsupport S)
    (fun a _ ↦ by
      induction a using Sym2.inductionOn with
      | _ x y => simp [Iso.map])

/-- A graph isomorphism carries weighted flow-equivalent trees to flow-equivalent trees when edge
weights correspond. -/
theorem Iso.isFlowEquivalentTree_indicator_edgeSet_iff [Fintype V] [Fintype W] [AddCommMonoid K]
    [LinearOrder K] {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (c : Sym2 V → K) (d : Sym2 W → K)
    (hcd : ∀ x y, G.Adj x y → d s(e x, e y) = c s(x, y))
    {T : SimpleGraph V} {w : Sym2 V → K} :
    TauCeti.TerminalCut.IsFlowEquivalentTree
        (TauCeti.pairCutCapacity (H.edgeSet.indicator d))
        (T.map e.toEquiv)
        (fun a ↦ w (a.map e.symm)) ↔
      TauCeti.TerminalCut.IsFlowEquivalentTree
        (TauCeti.pairCutCapacity (G.edgeSet.indicator c)) T w :=
  TauCeti.TerminalCut.isFlowEquivalentTree_map_iff
    (SimpleGraph.Iso.map e.toEquiv T)
    (fun S ↦ e.pairCutCapacity_indicator_edgeSet c d hcd S)
    (fun a _ ↦ by
      induction a using Sym2.inductionOn with
      | _ x y => simp [Iso.map])

/-- A graph isomorphism carries weighted cut trees to cut trees when edge weights correspond. -/
theorem Iso.isCutTree_indicator_edgeSet_iff [Fintype V] [Fintype W] [AddCommMonoid K]
    [LinearOrder K] {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (c : Sym2 V → K) (d : Sym2 W → K)
    (hcd : ∀ x y, G.Adj x y → d s(e x, e y) = c s(x, y))
    {T : SimpleGraph V} {w : Sym2 V → K} :
    TauCeti.TerminalCut.IsCutTree
        (TauCeti.pairCutCapacity (H.edgeSet.indicator d))
        (T.map e.toEquiv)
        (fun a ↦ w (a.map e.symm)) ↔
      TauCeti.TerminalCut.IsCutTree
        (TauCeti.pairCutCapacity (G.edgeSet.indicator c)) T w :=
  TauCeti.TerminalCut.isCutTree_map_iff
    (SimpleGraph.Iso.map e.toEquiv T)
    (fun S ↦ e.pairCutCapacity_indicator_edgeSet c d hcd S)
    (fun a _ ↦ by
      induction a using Sym2.inductionOn with
      | _ x y => simp [Iso.map])

/-- A graph isomorphism carries unit flow-equivalent trees to unit flow-equivalent trees. -/
theorem Iso.isFlowEquivalentTree_unitCutCapacity_iff [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {T : SimpleGraph V} {w : Sym2 V → ℕ} :
    TauCeti.TerminalCut.IsFlowEquivalentTree H.unitCutCapacity
        (T.map e.toEquiv) (fun a ↦ w (a.map e.symm)) ↔
      TauCeti.TerminalCut.IsFlowEquivalentTree G.unitCutCapacity T w :=
  TauCeti.TerminalCut.isFlowEquivalentTree_map_iff
    (SimpleGraph.Iso.map e.toEquiv T) e.unitCutCapacity_map
    (fun a _ ↦ by
      induction a using Sym2.inductionOn with
      | _ x y => simp [Iso.map])

/-- A graph isomorphism carries unit cut trees to unit cut trees. -/
theorem Iso.isCutTree_unitCutCapacity_iff [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    {T : SimpleGraph V} {w : Sym2 V → ℕ} :
    TauCeti.TerminalCut.IsCutTree H.unitCutCapacity
        (T.map e.toEquiv) (fun a ↦ w (a.map e.symm)) ↔
      TauCeti.TerminalCut.IsCutTree G.unitCutCapacity T w :=
  TauCeti.TerminalCut.isCutTree_map_iff
    (SimpleGraph.Iso.map e.toEquiv T) e.unitCutCapacity_map
    (fun a _ ↦ by
      induction a using Sym2.inductionOn with
      | _ x y => simp [Iso.map])

end SimpleGraph

/-! ### Unit cut-tree queries, threshold partitions, and global edge connectivity -/

namespace TauCeti.TerminalCut.IsFlowEquivalentTree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Finite V]
variable {T : SimpleGraph V} {w : Sym2 V → ℕ}

/-- On a unit cut tree of a simple graph, some minimum-weight edge on every nontrivial tree path
has weight equal to the local edge reachability of its endpoints. -/
theorem exists_weight_eq_simpleGraph_edgeReachability
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w)
    {s t : V} (hst : s ≠ t) {p : T.Walk s t} (hp : p.IsPath) :
    ∃ e ∈ p.edges, G.edgeReachability s t = (w e : ℕ∞) ∧
      ∀ e' ∈ p.edges, w e ≤ w e' := by
  obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
  refine ⟨e, he, ?_, fun e' he' ↦ hwe.trans_le (hT.le_weight hp he')⟩
  rw [G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hst, ← hwe]

/-- On a unit flow-equivalent tree of a simple graph, two vertices (possibly equal) are
`k`-edge-reachable in `G` iff every edge on their tree path has weight at least `k`. -/
theorem simpleGraph_isEdgeReachable_iff_forall_le_weight
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w)
    (k : ℕ∞) {s t : V} {p : T.Walk s t} (hp : p.IsPath) :
    G.IsEdgeReachable k s t ↔ ∀ e ∈ p.edges, k ≤ (w e : ℕ∞) := by
  rcases eq_or_ne s t with rfl | hst
  · cases p with
    | nil => simp [SimpleGraph.IsEdgeReachable.rfl]
    | cons _ q =>
      exfalso
      have hdup := hp.support_nodup
      simp only [Walk.support_cons, List.nodup_cons] at hdup
      exact hdup.1 q.end_mem_support
  · rw [G.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity hst k]
    constructor
    · intro hk e he
      exact hk.trans (Nat.cast_le.mpr (hT.le_weight hp he))
    · intro h
      obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
      exact (h e he).trans_eq (congrArg Nat.cast hwe)

/-- Deleting the cut-tree edges of weight below `k` leaves two vertices connected exactly when
they are locally `k`-edge-reachable in the original simple graph. -/
theorem reachable_deleteEdges_iff_simpleGraph_isEdgeReachable
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w) (k : ℕ) {s t : V} :
    (T.deleteEdges {e | w e < k}).Reachable s t ↔
      G.IsEdgeReachable (k : ℕ∞) s t := by
  rw [hT.reachable_deleteEdges_iff_le_iInf_pairMinimumValue,
    SimpleGraph.isEdgeReachable_iff_le_edgeReachability,
    G.edgeReachability_eq_iInf_pairMinimumValue_unitCutCapacity]

/-- A finite simple graph is `k`-edge-connected iff every edge of a unit flow-equivalent tree has
weight at least `k`. This holds for every `k : ℕ∞` (and includes singleton graphs, where
`T.edgeSet = ∅`; empty vertex types admit no tree `T`). -/
theorem simpleGraph_isEdgeConnected_iff_forall_le_weight
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w) (k : ℕ∞) :
    G.IsEdgeConnected k ↔ ∀ e ∈ T.edgeSet, k ≤ (w e : ℕ∞) := by
  constructor
  · intro h e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : T.Adj u v := T.mem_edgeSet.mp he
      rw [hT.weight_eq huv]
      exact (G.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity huv.ne k).mp (h u v)
  · intro h s t
    obtain ⟨p, hp, -⟩ := hT.isTree.existsUnique_path s t
    exact (hT.simpleGraph_isEdgeReachable_iff_forall_le_weight k hp).mpr fun e he ↦
      h e (p.edges_subset_edgeSet he)

/-- A finite simple graph is preconnected iff every edge of a unit flow-equivalent tree has
positive weight. -/
theorem simpleGraph_preconnected_iff_forall_weight_pos
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w) :
    G.Preconnected ↔ ∀ e ∈ T.edgeSet, 0 < w e := by
  rw [← SimpleGraph.isEdgeConnected_one, hT.simpleGraph_isEdgeConnected_iff_forall_le_weight 1]
  refine forall₂_congr fun e _ ↦ ?_
  rw [← Nat.cast_one, Nat.cast_le]
  omega

/-- A finite simple graph has no bridges in Mathlib's sense (`∀ e, ¬G.IsBridge e`) iff every edge
of a unit flow-equivalent tree has weight at least `2`. Note that Mathlib's `SimpleGraph.IsBridge`
does not require `e ∈ G.edgeSet`, so `∀ e, ¬G.IsBridge e` is equivalent to
`G.IsEdgeConnected 2` (including preconnectedness). -/
theorem forall_not_simpleGraph_isBridge_iff_forall_two_le_weight
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w) :
    (∀ e, ¬G.IsBridge e) ↔ ∀ e ∈ T.edgeSet, 2 ≤ w e := by
  rw [← SimpleGraph.isEdgeConnected_two_iff_forall_not_isBridge,
    hT.simpleGraph_isEdgeConnected_iff_forall_le_weight 2]
  refine forall₂_congr fun e _ ↦ ?_
  rw [← Nat.cast_ofNat, Nat.cast_le]

/-- The global edge connectivity of a finite simple graph is the infimum of edge weights in any
unit flow-equivalent tree. On singleton types `T.edgeSet` is empty and both sides equal `⊤`. -/
theorem simpleGraph_edgeConnectivity_eq_iInf_weight
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w) :
    G.edgeConnectivity = ⨅ e ∈ T.edgeSet, (w e : ℕ∞) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun e ↦ le_iInf fun he ↦ ?_
    exact (hT.simpleGraph_isEdgeConnected_iff_forall_le_weight _).mp
      (G.isEdgeConnected_iff_le_edgeConnectivity.mpr le_rfl) e he
  · refine G.isEdgeConnected_iff_le_edgeConnectivity.mp ?_
    rw [hT.simpleGraph_isEdgeConnected_iff_forall_le_weight]
    intro e he
    exact iInf_le_of_le e (iInf_le_of_le he le_rfl)

/-- Every tree edge of a unit flow-equivalent tree has weight at least the global edge
connectivity of `G`. -/
theorem simpleGraph_edgeConnectivity_le_weight
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w) {e : Sym2 V} (he : e ∈ T.edgeSet) :
    G.edgeConnectivity ≤ (w e : ℕ∞) := by
  rw [hT.simpleGraph_edgeConnectivity_eq_iInf_weight]
  exact iInf_le_of_le e (iInf_le_of_le he le_rfl)

/-- The global edge connectivity of a finite simple graph with at least two vertices is the
minimum weight of an edge in any unit flow-equivalent tree. The witness includes the
minimum-weight certificate. -/
theorem exists_edge_simpleGraph_edgeConnectivity_eq_weight [Nontrivial V]
    (hT : IsFlowEquivalentTree G.unitCutCapacity T w) :
    ∃ u v, T.Adj u v ∧ (∀ e ∈ T.edgeSet, w s(u, v) ≤ w e) ∧
      G.edgeConnectivity = (w s(u, v) : ℕ∞) := by
  obtain ⟨u, v, huv, hmin, hvalue⟩ := hT.exists_edge_iInf_pairMinimumValue_eq_weight
    (Nat.castOrderEmbedding : ℕ ↪o ℕ∞).toOrderHom
  refine ⟨u, v, huv, hmin, ?_⟩
  rw [G.edgeConnectivity_eq_iInf_edgeReachability]
  simp_rw [G.edgeReachability_eq_iInf_pairMinimumValue_unitCutCapacity]
  simpa only [OrderEmbedding.toOrderHom_coe, Nat.castOrderEmbedding_apply] using hvalue

end TauCeti.TerminalCut.IsFlowEquivalentTree

namespace TauCeti.TerminalCut.IsCutTree

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V]
variable {T : SimpleGraph V} {w : Sym2 V → ℕ}

/-- A minimum-weight edge on a unit cut-tree path recovers a minimum simple-graph cut. Its unit
cut capacity equals the local edge reachability of the path endpoints. -/
theorem simpleGraph_edgeReachability_eq_unitCutCapacity_edgeSide
    (hT : IsCutTree G.unitCutCapacity T w)
    {s t u v : V} {p : T.Walk s t} (hp : p.IsPath) (huv : s(u, v) ∈ p.edges)
    (hmin : ∀ e ∈ p.edges, w s(u, v) ≤ w e) (hs : s ∈ T.edgeSide u v) :
    G.edgeReachability s t =
      ((G.unitCutCapacity (T.edgeSide u v) : ℕ) : ℕ∞) := by
  have hcut := hT.isMinimum_edgeSide_of_mem_edges hp huv hmin hs
  rw [G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hcut.admissible.ne,
    hcut.pairMinimumValue_eq]

/-- The number of edges of `G` crossing the fundamental side of a tree edge equals that edge's
weight. -/
theorem ncard_crossing_edgeSide (hT : IsCutTree G.unitCutCapacity T w) {u v : V} (huv : T.Adj u v) :
    {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}.ncard = w s(u, v) := by
  rw [← hT.apply_edgeSide huv, G.unitCutCapacity_eq_ncard]
  rfl

/-- The extended cardinality of the crossing edge set of a tree edge's fundamental side equals
that edge's weight. -/
theorem encard_crossing_edgeSide (hT : IsCutTree G.unitCutCapacity T w) {u v : V}
    (huv : T.Adj u v) :
    {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}.encard = (w s(u, v) : ℕ∞) := by
  have hfin : {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}.Finite := Set.toFinite _
  rw [← hfin.cast_ncard_eq, hT.ncard_crossing_edgeSide huv]

/-- Deleting the edges of `G` crossing the fundamental side of an edge on the tree path from `s`
to `t` separates `s` from `t` in `G`. -/
theorem not_reachable_deleteEdges_crossing_edgeSide (hT : IsCutTree G.unitCutCapacity T w)
    {s t u v : V} {p : T.Walk s t} (hp : p.IsPath) (huv : s(u, v) ∈ p.edges)
    (hs : s ∈ T.edgeSide u v) :
    ¬(G.deleteEdges {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}).Reachable s t := by
  have ht : t ∉ T.edgeSide u v :=
    (hp.mem_edges_iff_notMem_edgeSide hT.isTree.isAcyclic hs).mp huv
  exact G.not_reachable_deleteEdges_crossing (mem_coe.mpr hs) (by simpa using ht)

/-- **Query optimality certificate.** For a minimum-weight edge `s(u, v)` on the tree path from `s`
to `t` with `s` on the side of `u`, the edges of `G` crossing `T.edgeSide u v` form a minimum
`s`--`t` edge separator: every `s`--`t` edge separator `F` has at least as many edges. -/
theorem encard_crossing_edgeSide_le (hT : IsCutTree G.unitCutCapacity T w)
    {s t u v : V} {p : T.Walk s t} (hp : p.IsPath) (huv : s(u, v) ∈ p.edges)
    (hmin : ∀ e ∈ p.edges, w s(u, v) ≤ w e) (hs : s ∈ T.edgeSide u v)
    {F : Set (Sym2 V)} (hF : ¬(G.deleteEdges F).Reachable s t) :
    {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}.encard ≤ F.encard := by
  have hcut := hT.isMinimum_edgeSide_of_mem_edges hp huv hmin hs
  have hadj : T.Adj u v := p.adj_of_mem_edges huv
  rw [hT.encard_crossing_edgeSide hadj, ← hT.apply_edgeSide hadj, ← hcut.pairMinimumValue_eq]
  exact G.pairMinimumValue_unitCutCapacity_le_encard_of_not_reachable hF

/-- A minimum-weight edge of a unit cut tree for a finite simple graph with at least two vertices
produces a disconnecting edge cut whose size equals the global edge connectivity of `G`. -/
theorem exists_edgeSide_crossing_eq_simpleGraph_edgeConnectivity [Nontrivial V]
    (hT : IsCutTree G.unitCutCapacity T w) :
    ∃ u v, T.Adj u v ∧ (∀ e ∈ T.edgeSet, w s(u, v) ≤ w e) ∧
      ¬(G.deleteEdges {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}).Preconnected ∧
      {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}.encard = G.edgeConnectivity := by
  obtain ⟨u, v, huv, hmin, heq⟩ :=
    hT.toIsFlowEquivalentTree.exists_edge_simpleGraph_edgeConnectivity_eq_weight
  refine ⟨u, v, huv, hmin, ?_, ?_⟩
  · intro hconn
    have hv : v ∉ T.edgeSide u v :=
      (isAcyclic_iff_forall_adj_isBridge.mp hT.isTree.isAcyclic huv).notMem_edgeSide
    exact G.not_reachable_deleteEdges_crossing
      (mem_coe.mpr (SimpleGraph.self_mem_edgeSide T u v)) (by simpa using hv) (hconn u v)
  · rw [hT.encard_crossing_edgeSide huv, heq]

end TauCeti.TerminalCut.IsCutTree

/-! ### Complete graphs -/

namespace SimpleGraph

variable {V : Type*}

/-- Any star graph on a finite vertex type, weighted constantly by `|V| - 1`, is a unit-capacity
cut tree for the complete graph `⊤`. -/
theorem isCutTree_starGraph_top [Fintype V] (r : V) :
    TauCeti.TerminalCut.IsCutTree (⊤ : SimpleGraph V).unitCutCapacity
      (starGraph r) (fun _ ↦ Fintype.card V - 1) := by
  classical
  refine TauCeti.TerminalCut.IsCutTree.of_isMinimum_edgeSide (isTree_starGraph r) ?_ ?_
  · intro u v huv
    have hbridge : (starGraph r).IsBridge s(u, v) :=
      isAcyclic_iff_forall_adj_isBridge.mp (isAcyclic_starGraph r) huv
    have hleaf : ∀ {a : V}, a ≠ r → (starGraph r).edgeSide a r = {a} := fun ha ↦
      edgeSide_eq_singleton fun y hy ↦ by
        rcases starGraph_adj.mp hy with ⟨-, rfl | rfl⟩
        · exact absurd rfl ha
        · rfl
    have hpre : (starGraph r).Preconnected := (connected_starGraph r).preconnected
    have hval :
        (⊤ : SimpleGraph V).unitCutCapacity ((starGraph r).edgeSide u v) = Fintype.card V - 1 := by
      rcases starGraph_adj.mp huv with ⟨hne, rfl | rfl⟩
      · rw [← unitCutCapacity_compl, hbridge.compl_edgeSide hpre, hleaf hne.symm,
          unitCutCapacity_top]
        simp
      · rw [hleaf hne, unitCutCapacity_top]
        simp
    rw [TauCeti.TerminalCut.isMinimum_singleton_iff_pairMinimumValue_eq,
      pairMinimumValue_unitCutCapacity_top huv.ne]
    exact ⟨self_mem_edgeSide _ u v, hbridge.notMem_edgeSide, hval⟩
  · intro u v huv
    exact (pairMinimumValue_unitCutCapacity_top huv.ne).symm

end SimpleGraph
