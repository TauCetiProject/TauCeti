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
# Cut trees and minimum cuts for finite simple graphs

This file gives the native simple-graph specialization of pairwise minimum cuts and the Gomory--Hu
cut-tree theorem directly on `V`, without passing through `V(Graph.ofSimpleGraph G)`. Unit cuts are
measured by `G.unitCutCapacity` (counting graph edges crossing to the complement), while general
weighted cuts are represented by `TauCeti.pairCutCapacity (G.edgeSet.indicator c)`.

A unit cut tree records local edge reachability as the minimum weight on each tree path, and a
minimum-weight path edge recovers an actual minimum cut of the original simple graph. Deleting tree
edges of weight below `k` leaves precisely the local `k`-edge-reachability classes, and when the
vertex type has at least two elements, a minimum-weight tree edge records the global edge
connectivity and certifies a minimum disconnecting edge cut.

## Main results

* `SimpleGraph.isMinimum_ofSimpleGraph_iff` and `SimpleGraph.pairMinimumValue_ofSimpleGraph`:
  weighted minimum cuts and pairwise minimum cut values on `Graph.ofSimpleGraph G` agree with those
  of `TauCeti.pairCutCapacity` on `V`.
* `SimpleGraph.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity` and
  `SimpleGraph.edgeConnectivity_eq_iInf_pairMinimumValue_unitCutCapacity`: local edge reachability
  and global edge connectivity in terms of `G.unitCutCapacity` minimum cut values.
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
* `SimpleGraph.isCutTree_starGraph_top`, `SimpleGraph.edgeReachability_top`, and
  `SimpleGraph.edgeConnectivity_top`: star cut trees and edge connectivity of complete graphs.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* R. E. Gomory and T. C. Hu, *Multi-terminal network flows*, J. SIAM 9 (1961), 551--570.
* D. Gusfield, *Very Simple Methods for All Pairs Network Flow Analysis*, SIAM J. Comput. 19
  (1990), 143--155.
* B. Korte and J. Vygen, *Combinatorial Optimization: Theory and Algorithms*, Section 8.6.

The multigraph existence and query interface adapted here is developed in
`TauCeti.Combinatorics.Network.MinimumCut.Graph`, especially
`Graph.exists_isUnitCutTree`, `IsFlowEquivalentTree.reachable_deleteEdges_iff_isEdgeReachable`,
and `IsCutTree.edgeReachability_eq_edgeCutCapacity_edgeSide`.
-/

public section

open Finset
open scoped Graph

namespace SimpleGraph

variable {V W K : Type*} (G : SimpleGraph V)

/-! ### Pairwise minimum cuts and local edge reachability -/

/-- Minimum cuts of `Graph.ofSimpleGraph G` correspond to minimum cuts of `TauCeti.pairCutCapacity`
whenever off-diagonal weights vanish away from the edges of `G`. -/
theorem isMinimum_ofSimpleGraph_iff [Fintype V] [AddCommMonoid K] [Preorder K]
    (c : Sym2 V → K) (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0)
    {A B S : Finset V} :
    TauCeti.TerminalCut.IsMinimum
        ((Graph.ofSimpleGraph G).edgeCutCapacity (G.ofSimpleGraphCapacity c))
        (G.toOfSimpleGraphFinset A) (G.toOfSimpleGraphFinset B) (G.toOfSimpleGraphFinset S) ↔
      TauCeti.TerminalCut.IsMinimum (TauCeti.pairCutCapacity c) A B S := by
  simpa only [toOfSimpleGraphFinset_eq_map] using
    TauCeti.TerminalCut.isMinimum_map_iff (f := TauCeti.pairCutCapacity c)
      G.ofSimpleGraphVertexEquiv
      (g := (Graph.ofSimpleGraph G).edgeCutCapacity (G.ofSimpleGraphCapacity c))
      (fun T ↦ by
        rw [← G.toOfSimpleGraphFinset_eq_map T]
        exact G.edgeCutCapacity_eq_pairCutCapacity c hsupport T)

/-- Pairwise minimum cut values of `Graph.ofSimpleGraph G` equal those of `TauCeti.pairCutCapacity`
whenever off-diagonal weights vanish away from the edges of `G`. -/
theorem pairMinimumValue_ofSimpleGraph [Fintype V] [AddCommMonoid K] [LinearOrder K]
    (c : Sym2 V → K) (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0) (s t : V) :
    TauCeti.TerminalCut.pairMinimumValue
        ((Graph.ofSimpleGraph G).edgeCutCapacity (G.ofSimpleGraphCapacity c))
        (G.ofSimpleGraphVertexEquiv s) (G.ofSimpleGraphVertexEquiv t) =
      TauCeti.TerminalCut.pairMinimumValue (TauCeti.pairCutCapacity c) s t :=
  TauCeti.TerminalCut.pairMinimumValue_map (TauCeti.pairCutCapacity c)
    G.ofSimpleGraphVertexEquiv
    ((Graph.ofSimpleGraph G).edgeCutCapacity (G.ofSimpleGraphCapacity c))
    (fun S ↦ by
      rw [← G.toOfSimpleGraphFinset_eq_map S]
      exact G.edgeCutCapacity_eq_pairCutCapacity c hsupport S) s t

/-- Pairwise minimum cut values of `Graph.ofSimpleGraph G` with weights `c` equal those of
`TauCeti.pairCutCapacity (G.edgeSet.indicator c)`. -/
theorem pairMinimumValue_ofSimpleGraph_indicator [Fintype V] [AddCommMonoid K] [LinearOrder K]
    (c : Sym2 V → K) (s t : V) :
    TauCeti.TerminalCut.pairMinimumValue
        ((Graph.ofSimpleGraph G).edgeCutCapacity (G.ofSimpleGraphCapacity c))
        (G.ofSimpleGraphVertexEquiv s) (G.ofSimpleGraphVertexEquiv t) =
      TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity (G.edgeSet.indicator c)) s t := by
  rw [← G.ofSimpleGraphCapacity_indicator_edgeSet c]
  exact G.pairMinimumValue_ofSimpleGraph (G.edgeSet.indicator c)
    (fun p _ hp ↦ Set.indicator_of_notMem hp c) s t

/-- Pairwise minimum cut values of `Graph.ofSimpleGraph G` with constant weight `a` equal those of
`TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ a)`. -/
theorem pairMinimumValue_ofSimpleGraph_const [Fintype V] [AddCommMonoid K] [LinearOrder K]
    (a : K) (s t : V) :
    TauCeti.TerminalCut.pairMinimumValue
        ((Graph.ofSimpleGraph G).edgeCutCapacity fun _ ↦ a)
        (G.ofSimpleGraphVertexEquiv s) (G.ofSimpleGraphVertexEquiv t) =
      TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ a)) s t := by
  rw [← G.ofSimpleGraphCapacity_const a]
  exact G.pairMinimumValue_ofSimpleGraph_indicator (fun _ ↦ a) s t

/-- For distinct vertices of a finite simple graph, local edge reachability at threshold
`k : ℕ∞` holds exactly when `k` is at most the minimum unit cut value between `s` and `t`. -/
theorem isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity [Finite V] {s t : V}
    (hst : s ≠ t) (k : ℕ∞) :
    G.IsEdgeReachable k s t ↔
      k ≤ ((TauCeti.TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) := by
  rw [G.isEdgeReachable_iff_le_edgeReachability,
    G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hst]

/-- Weighted pairwise minimum cut values are monotone in the graph when weights are nonnegative on
edges. -/
theorem pairMinimumValue_indicator_edgeSet_mono [Fintype V] [AddCommMonoid K] [LinearOrder K]
    [AddLeftMono K] {G H : SimpleGraph V} (hGH : G ≤ H) {c : Sym2 V → K}
    (hc : ∀ p ∈ H.edgeSet, 0 ≤ c p) (s t : V) :
    TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity (G.edgeSet.indicator c)) s t ≤
      TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity (H.edgeSet.indicator c)) s t := by
  rcases eq_or_ne s t with rfl | hst
  · simp
  · obtain ⟨S, hS⟩ := TauCeti.TerminalCut.exists_minimum
      (TauCeti.pairCutCapacity (H.edgeSet.indicator c)) (disjoint_singleton.mpr hst)
    obtain ⟨hs, ht⟩ := TauCeti.TerminalCut.isAdmissible_singleton.mp hS.admissible
    rw [hS.pairMinimumValue_eq]
    exact (TauCeti.TerminalCut.pairMinimumValue_le _ hs ht).trans
      (pairCutCapacity_indicator_edgeSet_mono hGH hc S)

/-- Unit pairwise minimum cut values are monotone with respect to subgraph inclusion. -/
theorem pairMinimumValue_unitCutCapacity_mono [Finite V] {G H : SimpleGraph V} (hGH : G ≤ H)
    (s t : V) :
    TauCeti.TerminalCut.pairMinimumValue G.unitCutCapacity s t ≤
      TauCeti.TerminalCut.pairMinimumValue H.unitCutCapacity s t := by
  let _ := Fintype.ofFinite V
  rw [G.unitCutCapacity_eq_pairCutCapacity, H.unitCutCapacity_eq_pairCutCapacity]
  exact pairMinimumValue_indicator_edgeSet_mono hGH (fun _ _ ↦ Nat.zero_le 1) s t

/-- The minimum unit cut value between any two vertices is at most the degree of the first. -/
theorem pairMinimumValue_unitCutCapacity_le_degree [Finite V] (s t : V)
    [Fintype (G.neighborSet s)] :
    TauCeti.TerminalCut.pairMinimumValue G.unitCutCapacity s t ≤ G.degree s := by
  rcases eq_or_ne s t with rfl | hst
  · simp
  · rw [← Nat.cast_le (α := ℕ∞), ← G.edgeReachability_eq_pairMinimumValue_unitCutCapacity hst]
    exact G.edgeReachability_le_degree hst

/-- Distinct vertices have minimum unit cut value zero exactly when they are not reachable. -/
theorem pairMinimumValue_unitCutCapacity_eq_zero_iff [Finite V] {s t : V} (hst : s ≠ t) :
    TauCeti.TerminalCut.pairMinimumValue G.unitCutCapacity s t = 0 ↔ ¬G.Reachable s t := by
  rw [← SimpleGraph.isEdgeReachable_one,
    G.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity hst 1]
  norm_cast
  omega

/-- Every edge separator between `s` and `t` has cardinality at least their minimum unit cut
value. -/
theorem pairMinimumValue_unitCutCapacity_le_encard_of_not_reachable [Finite V]
    {s t : V} {F : Set (Sym2 V)} (hF : ¬(G.deleteEdges F).Reachable s t) :
    ((TauCeti.TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) ≤ F.encard := by
  rcases eq_or_ne s t with rfl | hst
  · exact (hF .rfl).elim
  · by_contra hlt
    push Not at hlt
    have hreach : G.IsEdgeReachable
        ((TauCeti.TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) s t :=
      (G.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity hst _).mpr le_rfl
    exact hF (hreach hlt)

/-- In the complete graph `⊤`, every pair of distinct vertices has minimum unit cut value
`|V| - 1`. -/
theorem pairMinimumValue_unitCutCapacity_top [Fintype V] {s t : V} (hst : s ≠ t) :
    TauCeti.TerminalCut.pairMinimumValue (⊤ : SimpleGraph V).unitCutCapacity s t =
      Fintype.card V - 1 := by
  classical
  have hle :
      TauCeti.TerminalCut.pairMinimumValue (⊤ : SimpleGraph V).unitCutCapacity s t ≤
        Fintype.card V - 1 := by
    refine (TauCeti.TerminalCut.pairMinimumValue_le _ (mem_singleton_self s)
      (notMem_singleton.mpr hst.symm)).trans ?_
    rw [unitCutCapacity_top]
    simp
  refine le_antisymm hle ?_
  obtain ⟨S, hS⟩ := TauCeti.TerminalCut.exists_minimum (⊤ : SimpleGraph V).unitCutCapacity
    (disjoint_singleton.mpr hst)
  obtain ⟨hs, ht⟩ := TauCeti.TerminalCut.isAdmissible_singleton.mp hS.admissible
  rw [hS.pairMinimumValue_eq, unitCutCapacity_top]
  have hpos : 1 ≤ #S := Finset.one_le_card.mpr ⟨s, hs⟩
  have hlt : #S < Fintype.card V := Finset.card_lt_univ_of_notMem ht
  obtain ⟨k, hk⟩ : ∃ k, #S = k + 1 := ⟨#S - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card V - #S = m + 1 := ⟨Fintype.card V - #S - 1, by omega⟩
  rw [hm, hk]
  have hcard : Fintype.card V - 1 = k + m + 1 := by omega
  rw [hcard]
  have hmul : (k + 1) * (m + 1) = k * m + k + m + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
    omega
  omega

/-- A finite simple graph is `k`-edge-connected iff every pair of distinct vertices has minimum
unit cut value at least `k`. -/
theorem isEdgeConnected_iff_forall_le_pairMinimumValue_unitCutCapacity [Finite V] (k : ℕ∞) :
    G.IsEdgeConnected k ↔
      ∀ s t : V, s ≠ t →
        k ≤ ((TauCeti.TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) := by
  constructor
  · intro h s t hst
    exact (G.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity hst k).mp (h s t)
  · intro h s t
    rcases eq_or_ne s t with rfl | hst
    · exact .rfl
    · exact (G.isEdgeReachable_iff_le_pairMinimumValue_unitCutCapacity hst k).mpr (h s t hst)

/-- The global edge connectivity of a finite simple graph is the infimum of pairwise minimum unit
cut values over distinct vertices. On empty and singleton types both sides are `⊤`. -/
theorem edgeConnectivity_eq_iInf_pairMinimumValue_unitCutCapacity [Finite V] :
    G.edgeConnectivity =
      ⨅ (s : V) (t : V) (_ : s ≠ t),
        ((TauCeti.TerminalCut.pairMinimumValue G.unitCutCapacity s t : ℕ) : ℕ∞) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun s ↦ le_iInf fun t ↦ le_iInf fun hst ↦ ?_
    exact (G.isEdgeConnected_iff_forall_le_pairMinimumValue_unitCutCapacity _).mp
      (G.isEdgeConnected_iff_le_edgeConnectivity.mpr le_rfl) s t hst
  · refine G.isEdgeConnected_iff_le_edgeConnectivity.mp ?_
    rw [G.isEdgeConnected_iff_forall_le_pairMinimumValue_unitCutCapacity]
    intro s t hst
    exact iInf_le_of_le s (iInf_le_of_le t (iInf_le_of_le hst le_rfl))

/-- A graph isomorphism preserves weighted pairwise minimum cut values when edge weights
correspond. -/
theorem Iso.pairMinimumValue_indicator_edgeSet [Fintype V] [Fintype W] [AddCommMonoid K]
    [LinearOrder K] {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (c : Sym2 V → K) (d : Sym2 W → K)
    (hcd : ∀ x y, G.Adj x y → d s(e x, e y) = c s(x, y)) (s t : V) :
    TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity (H.edgeSet.indicator d)) (e s) (e t) =
      TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity (G.edgeSet.indicator c)) s t :=
  TauCeti.TerminalCut.pairMinimumValue_map
    (TauCeti.pairCutCapacity (G.edgeSet.indicator c)) e.toEquiv
    (TauCeti.pairCutCapacity (H.edgeSet.indicator d))
    (fun S ↦ e.pairCutCapacity_indicator_edgeSet c d hcd S) s t

/-- A graph isomorphism preserves unit pairwise minimum cut values. -/
theorem Iso.pairMinimumValue_unitCutCapacity [Finite V] [Finite W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (s t : V) :
    TauCeti.TerminalCut.pairMinimumValue H.unitCutCapacity (e s) (e t) =
      TauCeti.TerminalCut.pairMinimumValue G.unitCutCapacity s t :=
  TauCeti.TerminalCut.pairMinimumValue_map G.unitCutCapacity e.toEquiv H.unitCutCapacity
    e.unitCutCapacity_map s t

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

/-- On the complete graph `⊤` over a finite vertex type, any two distinct vertices have local edge
reachability `|V| - 1`. -/
theorem edgeReachability_top [Fintype V] {s t : V} (hst : s ≠ t) :
    (⊤ : SimpleGraph V).edgeReachability s t = ((Fintype.card V - 1 : ℕ) : ℕ∞) := by
  rw [edgeReachability_eq_pairMinimumValue_unitCutCapacity _ hst,
    pairMinimumValue_unitCutCapacity_top hst]

/-- The global edge connectivity of the complete graph on a finite nontrivial vertex type `V` is
`|V| - 1`. -/
theorem edgeConnectivity_top [Fintype V] [Nontrivial V] :
    (⊤ : SimpleGraph V).edgeConnectivity = ((Fintype.card V - 1 : ℕ) : ℕ∞) := by
  obtain ⟨r⟩ := (inferInstance : Nonempty V)
  obtain ⟨_, _, -, -, h⟩ :=
    (isCutTree_starGraph_top r).toIsFlowEquivalentTree
      |>.exists_edge_simpleGraph_edgeConnectivity_eq_weight
  exact h

end SimpleGraph
