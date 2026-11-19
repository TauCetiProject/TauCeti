/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Star
public import TauCeti.Combinatorics.Network.MinimumCut.Graph
import Mathlib.Tactic.FinCases
import TauCeti.Combinatorics.Network.MinimumCut.Transport
import TauCeti.Combinatorics.SimpleGraph.Finite

/-!
# Cut trees and unit-capacity minimum cuts for simple graphs

This file specializes pair-capacity minimum cuts and the Gomory--Hu cut-tree theorem directly to
`SimpleGraph V` on its native vertex type `V`, without passing through the vertex-subtype carrier
`V(Graph.ofSimpleGraph G)`. Edge weights are represented on unordered vertex pairs by
`G.edgeSet.indicator c` (and by `G.edgeSet.indicator fun _ ↦ (1 : ℕ)` for unit capacities),
which agrees with `fun e ↦ if e ∈ G.edgeFinset then c e else 0` when `G.edgeSet` is finite and
vertices have decidable equality.

## Main results

* `SimpleGraph.pairCutCapacity_indicator_edgeSet_one`: unit cut capacity counts crossing edges of
  `G` via `Set.ncard` (and via `Finset.card` in
  `pairCutCapacity_indicator_edgeSet_one_eq_card_filter`).
* `SimpleGraph.pairCutCapacity_indicator_edgeSet_singleton`: the weighted singleton cut is the sum
  of incident edge weights, specializing to `G.degree v` for unit capacities.
* `SimpleGraph.isEdgeReachable_iff_le_pairMinimumValue`: for distinct vertices `s, t` of a finite
  simple graph, `G.IsEdgeReachable k s t` holds exactly when `k` is at most the minimum unit cut
  value between `s` and `t` (viewed in `ℕ∞`).
* `SimpleGraph.edgeConnectivity_eq_iInf_pairMinimumValue`: global edge connectivity is the infimum
  of pairwise minimum unit cut values over distinct vertices.
* `SimpleGraph.exists_isCutTree_indicator_edgeSet`, `SimpleGraph.exists_isUnitCutTree`: every
  nonempty finite simple graph admits weighted and unit-capacity cut trees directly on `V`.
* `SimpleGraph.isCutTree_ofSimpleGraph_iff`: equivalence between cut trees on `V` and cut trees on
  `V(Graph.ofSimpleGraph G)`.
* `TauCeti.TerminalCut.IsFlowEquivalentTree.isEdgeReachable_iff_forall_le_weight`: local edge
  reachability at threshold `k : ℕ∞` holds iff every edge on the tree path has weight at least
  `k`.
* `TauCeti.TerminalCut.IsFlowEquivalentTree.reachable_deleteEdges_iff_isEdgeReachable`: deleting
  tree edges of weight below `k : ℕ` yields the `k`-edge-reachability classes of `G` directly.
* `TauCeti.TerminalCut.IsFlowEquivalentTree.edgeConnectivity_eq_iInf_weight` and
  `exists_adj_edgeConnectivity_eq_weight`: global edge connectivity is the minimum tree-edge
  weight.
* `TauCeti.TerminalCut.IsCutTree.not_reachable_deleteEdges_crossing_edgeSide` and
  `encard_crossing_edgeSide_le`: a minimum-weight edge on a tree path recovers a minimum `s`--`t`
  edge separator of `G` directly on `V`.
* `SimpleGraph.isCutTree_starGraph_top`: any star graph with constant weight `|V| - 1` is a unit
  cut tree for the complete graph `⊤ : SimpleGraph V`.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* R. E. Gomory and T. C. Hu, *Multi-terminal network flows*, J. SIAM 9 (1961), 551--570.
* D. Gusfield, *Very Simple Methods for All Pairs Network Flow Analysis*, SIAM J. Comput. 19
  (1990), 143--155.
* B. Korte and J. Vygen, *Combinatorial Optimization: Theory and Algorithms*, Section 8.6.
-/

public section

open Finset

namespace SimpleGraph

variable {V W K : Type*} (G : SimpleGraph V)

/-! ### Cut capacities of simple graphs -/

/-- On a graph with finitely many edges and decidable equality on vertices, `G.edgeSet.indicator c`
equals the `if`-`then`-`else` expression testing membership in `G.edgeFinset`. -/
theorem indicator_edgeSet_eq_ite_mem_edgeFinset [Fintype G.edgeSet] [DecidableEq V] [Zero K]
    (c : Sym2 V → K) :
    G.edgeSet.indicator c = fun e ↦ if e ∈ G.edgeFinset then c e else 0 := by
  funext e
  by_cases he : e ∈ G.edgeSet
  · simp [Set.indicator_of_mem he, mem_edgeFinset.mpr he]
  · simp [he]

/-- Unit cut capacity of a simple graph equals the number of edges crossing `S`. -/
theorem pairCutCapacity_indicator_edgeSet_one [Fintype V] (S : Finset V) :
    TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ)) S =
      {e ∈ G.edgeSet | e.Crosses (S : Set V)}.ncard := by
  rw [← G.edgeCutCapacity_ofSimpleGraph_const 1 S, Graph.edgeCutCapacity_one,
    G.image_val_toOfSimpleGraphFinset, G.edgeCut_ofSimpleGraph]

/-- Unit cut capacity of a simple graph equals the cardinality of the finset of edges in
`G.edgeFinset` crossing `S`. -/
theorem pairCutCapacity_indicator_edgeSet_one_eq_card_filter [Fintype V] [Fintype G.edgeSet]
    (S : Finset V) [DecidablePred fun e : Sym2 V ↦ e.Crosses (S : Set V)] :
    TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ)) S =
      #{e ∈ G.edgeFinset | e.Crosses (S : Set V)} := by
  rw [pairCutCapacity_indicator_edgeSet_one, ← Set.ncard_coe_finset]
  congr 1
  ext e
  simp

/-- The weighted cut capacity of a singleton `{v}` is the sum of weights of edges incident to
`v`. -/
theorem pairCutCapacity_indicator_edgeSet_singleton [Fintype V] [AddCommMonoid K]
    (c : Sym2 V → K) (v : V) [Fintype (G.neighborSet v)] :
    TauCeti.pairCutCapacity (G.edgeSet.indicator c) {v} =
      ∑ w ∈ G.neighborFinset v, c s(v, w) := by
  classical
  rw [TauCeti.pairCutCapacity_def]
  have hsum :
      (∑ p : Sym2 V, if p.Crosses ({v} : Set V) then G.edgeSet.indicator c p else 0) =
        ∑ p ∈ univ.filter
          (fun p : Sym2 V ↦ p ∈ G.edgeSet ∧ p.Crosses ({v} : Set V)), c p := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    by_cases hp : p ∈ G.edgeSet <;> by_cases hcross : p.Crosses ({v} : Set V) <;>
      simp [hp, hcross, Set.indicator_of_mem, Set.indicator_of_notMem]
  rw [Finset.coe_singleton, hsum]
  symm
  refine Finset.sum_nbij (fun w ↦ s(v, w)) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro w hw
    have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    simp only [mem_filter, mem_univ, true_and, mem_edgeSet, Sym2.crosses_mk_iff,
      Set.mem_singleton_iff]
    exact ⟨hadj, .inl hadj.ne.symm⟩
  · intro w₁ _ w₂ _ h
    rcases Sym2.eq_iff.mp h with ⟨-, rfl⟩ | ⟨hvw, rfl⟩
    · rfl
    · exact hvw
  · intro p hp
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hp
    induction p using Sym2.inductionOn with
    | _ x y =>
      simp only [mem_edgeSet, Sym2.crosses_mk_iff, Set.mem_singleton_iff] at hp
      rcases hp.2 with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨y, mem_coe.mpr ((G.mem_neighborFinset x y).mpr hp.1), rfl⟩
      · exact ⟨x, mem_coe.mpr ((G.mem_neighborFinset y x).mpr hp.1.symm), Sym2.eq_swap⟩

/-- The unit cut capacity of a singleton `{v}` is the degree of `v`. -/
@[simp]
theorem pairCutCapacity_indicator_edgeSet_one_singleton [Fintype V]
    (v : V) [Fintype (G.neighborSet v)] :
    TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ)) {v} = G.degree v := by
  rw [pairCutCapacity_indicator_edgeSet_singleton, Finset.sum_const, smul_eq_mul, mul_one,
    card_neighborFinset_eq_degree]

/-- On the complete graph `⊤`, restricting `c` to `edgeSet` does not change `pairCutCapacity`. -/
theorem pairCutCapacity_indicator_edgeSet_top [Fintype V] [AddCommMonoid K]
    (c : Sym2 V → K) (S : Finset V) :
    TauCeti.pairCutCapacity ((⊤ : SimpleGraph V).edgeSet.indicator c) S =
      TauCeti.pairCutCapacity c S := by
  have h :
      TauCeti.pairCutCapacity ((⊤ : SimpleGraph V).edgeSet.indicator c) =
        TauCeti.pairCutCapacity c :=
    TauCeti.pairCutCapacity_eq_of_offDiagonal_eq _ _ fun x y hxy ↦
      Set.indicator_of_mem (by simpa [mem_edgeSet] using hxy) c
  exact congrFun h S

/-- In the complete graph `⊤`, the number of edges crossing `S` is `|S| * (|V| - |S|)`. -/
theorem pairCutCapacity_indicator_edgeSet_one_top [Fintype V] (S : Finset V) :
    TauCeti.pairCutCapacity ((⊤ : SimpleGraph V).edgeSet.indicator fun _ ↦ (1 : ℕ)) S =
      #S * (Fintype.card V - #S) := by
  classical
  rw [pairCutCapacity_indicator_edgeSet_top, TauCeti.pairCutCapacity_def]
  have hcard :
      (∑ p : Sym2 V, if p.Crosses (S : Set V) then (1 : ℕ) else 0) =
        #(univ.filter fun p : Sym2 V ↦ p.Crosses (S : Set V)) := by
    rw [Finset.card_filter]
  rw [hcard, ← Finset.card_compl, ← Finset.card_product]
  symm
  refine Finset.card_bij (fun xy _ ↦ s(xy.1, xy.2)) ?_ ?_ ?_
  · rintro ⟨x, y⟩ hxy
    simp only [mem_product, mem_compl] at hxy
    simp only [mem_filter, mem_univ, true_and, Sym2.crosses_mk_iff, mem_coe]
    exact .inl hxy
  · rintro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ heq
    simp only [mem_product, mem_compl] at h₁ h₂
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact absurd h₁.1 h₂.2
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    induction p using Sym2.inductionOn with
    | _ x y =>
      simp only [Sym2.crosses_mk_iff, mem_coe] at hp
      rcases hp with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · exact ⟨(x, y), mem_product.mpr ⟨hx, mem_compl.mpr hy⟩, rfl⟩
      · exact ⟨(y, x), mem_product.mpr ⟨hy, mem_compl.mpr hx⟩, Sym2.eq_swap⟩

/-- Deleting a single edge `e` of `G` reduces the cut capacity of `S` by `c e` if `e` crosses `S`,
and leaves it unchanged otherwise. -/
theorem pairCutCapacity_indicator_edgeSet_deleteEdges_singleton [Fintype V] [AddCommMonoid K]
    (c : Sym2 V → K) {e : Sym2 V} (he : e ∈ G.edgeSet) (S : Finset V)
    [Decidable (e.Crosses (S : Set V))] :
    TauCeti.pairCutCapacity ((G.deleteEdges {e}).edgeSet.indicator c) S +
        (if e.Crosses (S : Set V) then c e else 0) =
      TauCeti.pairCutCapacity (G.edgeSet.indicator c) S := by
  classical
  rw [TauCeti.pairCutCapacity_def, TauCeti.pairCutCapacity_def]
  have hsingle :
      (if e.Crosses (S : Set V) then c e else 0) =
        ∑ p : Sym2 V, if p = e then (if p.Crosses (S : Set V) then c p else 0) else 0 := by
    simp
  rw [hsingle, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hpe : p = e
  · subst hpe
    have hnot : p ∉ (G.deleteEdges {p}).edgeSet := by simp [edgeSet_deleteEdges]
    rw [Set.indicator_of_notMem hnot, Set.indicator_of_mem he]
    by_cases hcross : p.Crosses (S : Set V) <;> simp [hcross]
  · have hmem : p ∈ (G.deleteEdges {e}).edgeSet ↔ p ∈ G.edgeSet := by
      simp [edgeSet_deleteEdges, hpe]
    by_cases hp : p ∈ G.edgeSet
    · rw [Set.indicator_of_mem (hmem.mpr hp), Set.indicator_of_mem hp]
      simp [hpe]
    · rw [Set.indicator_of_notMem (mt hmem.mp hp), Set.indicator_of_notMem hp]
      simp [hpe]

/-- Simple-graph cut capacities are monotone in the graph when weights are nonnegative on edges. -/
theorem pairCutCapacity_indicator_edgeSet_mono [Fintype V] [AddCommMonoid K] [Preorder K]
    [AddLeftMono K] {G H : SimpleGraph V} (hGH : G ≤ H) {c : Sym2 V → K}
    (hc : ∀ p ∈ H.edgeSet, 0 ≤ c p) (S : Finset V) :
    TauCeti.pairCutCapacity (G.edgeSet.indicator c) S ≤
      TauCeti.pairCutCapacity (H.edgeSet.indicator c) S := by
  refine TauCeti.pairCutCapacity_mono (fun x y _ ↦ ?_) S
  by_cases hG : s(x, y) ∈ G.edgeSet
  · rw [Set.indicator_of_mem hG, Set.indicator_of_mem (edgeSet_mono hGH hG)]
  · rw [Set.indicator_of_notMem hG]
    by_cases hH : s(x, y) ∈ H.edgeSet
    · rw [Set.indicator_of_mem hH]
      exact hc _ hH
    · rw [Set.indicator_of_notMem hH]

/-- A graph isomorphism preserves simple-graph cut capacities when edge weights correspond. -/
theorem Iso.pairCutCapacity_indicator_edgeSet [Fintype V] [Fintype W] [AddCommMonoid K]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (c : Sym2 V → K) (d : Sym2 W → K)
    (hcd : ∀ x y, G.Adj x y → d s(e x, e y) = c s(x, y)) (S : Finset V) :
    TauCeti.pairCutCapacity (H.edgeSet.indicator d) (S.map e.toEquiv.toEmbedding) =
      TauCeti.pairCutCapacity (G.edgeSet.indicator c) S := by
  refine TauCeti.pairCutCapacity_map e.toEquiv _ _ (fun x y _ ↦ ?_) S
  by_cases h : G.Adj x y
  · have h' : H.Adj (e x) (e y) := e.map_adj_iff.mpr h
    rw [RelIso.coe_fn_toEquiv, Set.indicator_of_mem (H.mem_edgeSet.mpr h'),
      Set.indicator_of_mem (G.mem_edgeSet.mpr h)]
    exact hcd x y h
  · have h' : ¬H.Adj (e x) (e y) := fun hadj ↦ h (e.map_adj_iff.mp hadj)
    rw [RelIso.coe_fn_toEquiv,
      Set.indicator_of_notMem (by simpa [H.mem_edgeSet] using h'),
      Set.indicator_of_notMem (by simpa [G.mem_edgeSet] using h)]

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

/-- Pairwise minimum cut values of `Graph.ofSimpleGraph G` equal those of
`TauCeti.pairCutCapacity` whenever off-diagonal weights vanish away from the edges of `G`. -/
theorem pairMinimumValue_ofSimpleGraph [Fintype V] [AddCommMonoid K] [LinearOrder K]
    (c : Sym2 V → K) (hsupport : ∀ p, ¬p.IsDiag → p ∉ G.edgeSet → c p = 0) (s t : V) :
    TauCeti.TerminalCut.pairMinimumValue
        ((Graph.ofSimpleGraph G).edgeCutCapacity (G.ofSimpleGraphCapacity c))
        (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t) =
      TauCeti.TerminalCut.pairMinimumValue (TauCeti.pairCutCapacity c) s t := by
  rw [← G.ofSimpleGraphVertexEquiv_apply s, ← G.ofSimpleGraphVertexEquiv_apply t]
  exact TauCeti.TerminalCut.pairMinimumValue_map (TauCeti.pairCutCapacity c)
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
        (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t) =
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
        (G.toOfSimpleGraphVertex s) (G.toOfSimpleGraphVertex t) =
      TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ a)) s t := by
  rw [← G.ofSimpleGraphCapacity_const a]
  exact G.pairMinimumValue_ofSimpleGraph_indicator (fun _ ↦ a) s t

/-- For distinct vertices of a finite simple graph, local edge reachability at threshold
`k : ℕ∞` holds exactly when `k` is at most the minimum unit cut value between `s` and `t`. -/
theorem isEdgeReachable_iff_le_pairMinimumValue [Fintype V] {s t : V} (hst : s ≠ t) (k : ℕ∞) :
    G.IsEdgeReachable k s t ↔
      k ≤ ((TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity
          (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) s t : ℕ) : ℕ∞) := by
  have hnat (n : ℕ) :
      G.IsEdgeReachable n s t ↔
        n ≤ TauCeti.TerminalCut.pairMinimumValue
          (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) s t := by
    have hst' : G.toOfSimpleGraphVertex s ≠ G.toOfSimpleGraphVertex t := by
      simpa only [← G.ofSimpleGraphVertexEquiv_apply] using
        G.ofSimpleGraphVertexEquiv.injective.ne hst
    have h1 := Graph.isEdgeReachable_iff_le_pairMinimumValue (G := Graph.ofSimpleGraph G) hst' n
    rw [G.toOfSimpleGraphVertex_val s, G.toOfSimpleGraphVertex_val t,
      Graph.isEdgeReachable_ofSimpleGraph_iff,
      G.pairMinimumValue_ofSimpleGraph_const (1 : ℕ) s t] at h1
    exact h1
  cases k with
  | top =>
    simp only [isEdgeReachable_top_iff_forall_nat, hnat, top_le_iff, ENat.natCast_ne_top,
      iff_false, not_forall, not_le]
    exact ⟨_, Nat.lt_succ_self _⟩
  | coe n =>
    rw [Nat.cast_le]
    exact hnat n

/-- Pairwise minimum cut values are monotone in the graph when weights are nonnegative on edges. -/
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

/-- The minimum unit cut value between any two vertices is at most the degree of the first. -/
theorem pairMinimumValue_indicator_edgeSet_one_le_degree [Fintype V] (s t : V)
    [Fintype (G.neighborSet s)] :
    TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) s t ≤
      G.degree s := by
  rcases eq_or_ne s t with rfl | hst
  · simp
  · calc
      TauCeti.TerminalCut.pairMinimumValue
          (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) s t ≤
        TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ)) {s} :=
          TauCeti.TerminalCut.pairMinimumValue_le _ (mem_singleton_self s)
            (notMem_singleton.mpr hst.symm)
      _ = G.degree s := G.pairCutCapacity_indicator_edgeSet_one_singleton s

/-- Distinct vertices have minimum unit cut value zero exactly when they are not reachable. -/
theorem pairMinimumValue_indicator_edgeSet_one_eq_zero_iff [Fintype V] {s t : V} (hst : s ≠ t) :
    TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) s t = 0 ↔
      ¬G.Reachable s t := by
  rw [← SimpleGraph.isEdgeReachable_one, G.isEdgeReachable_iff_le_pairMinimumValue hst 1]
  norm_cast
  omega

/-- Every edge separator between `s` and `t` has cardinality at least their minimum unit cut
value. -/
theorem pairMinimumValue_indicator_edgeSet_one_le_encard_of_not_reachable [Fintype V]
    {s t : V} {F : Set (Sym2 V)} (hF : ¬(G.deleteEdges F).Reachable s t) :
    ((TauCeti.TerminalCut.pairMinimumValue
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) s t : ℕ) : ℕ∞) ≤
      F.encard := by
  rcases eq_or_ne s t with rfl | hst
  · exact (hF .rfl).elim
  · by_contra hlt
    push Not at hlt
    have hreach : G.IsEdgeReachable
        ((TauCeti.TerminalCut.pairMinimumValue
          (TauCeti.pairCutCapacity
            (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) s t : ℕ) : ℕ∞) s t :=
      (G.isEdgeReachable_iff_le_pairMinimumValue hst _).mpr le_rfl
    exact hF (hreach hlt)

/-- In the complete graph `⊤`, every pair of distinct vertices has minimum unit cut value
`|V| - 1`. -/
theorem pairMinimumValue_indicator_edgeSet_one_top [Fintype V] {s t : V} (hst : s ≠ t) :
    TauCeti.TerminalCut.pairMinimumValue
        (TauCeti.pairCutCapacity
          ((⊤ : SimpleGraph V).edgeSet.indicator fun _ ↦ (1 : ℕ))) s t =
      Fintype.card V - 1 := by
  classical
  have hle :
      TauCeti.TerminalCut.pairMinimumValue
          (TauCeti.pairCutCapacity
            ((⊤ : SimpleGraph V).edgeSet.indicator fun _ ↦ (1 : ℕ))) s t ≤
        Fintype.card V - 1 := by
    refine (TauCeti.TerminalCut.pairMinimumValue_le _ (mem_singleton_self s)
      (notMem_singleton.mpr hst.symm)).trans ?_
    rw [pairCutCapacity_indicator_edgeSet_one_top]
    simp
  refine le_antisymm hle ?_
  obtain ⟨S, hS⟩ := TauCeti.TerminalCut.exists_minimum
    (TauCeti.pairCutCapacity ((⊤ : SimpleGraph V).edgeSet.indicator fun _ ↦ (1 : ℕ)))
    (disjoint_singleton.mpr hst)
  obtain ⟨hs, ht⟩ := TauCeti.TerminalCut.isAdmissible_singleton.mp hS.admissible
  rw [hS.pairMinimumValue_eq, pairCutCapacity_indicator_edgeSet_one_top]
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
theorem isEdgeConnected_iff_forall_le_pairMinimumValue [Fintype V] (k : ℕ∞) :
    G.IsEdgeConnected k ↔
      ∀ s t : V, s ≠ t →
        k ≤ ((TauCeti.TerminalCut.pairMinimumValue
          (TauCeti.pairCutCapacity
            (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) s t : ℕ) : ℕ∞) := by
  constructor
  · intro h s t hst
    exact (G.isEdgeReachable_iff_le_pairMinimumValue hst k).mp (h s t)
  · intro h s t
    rcases eq_or_ne s t with rfl | hst
    · exact .rfl
    · exact (G.isEdgeReachable_iff_le_pairMinimumValue hst k).mpr (h s t hst)

/-- The global edge connectivity of a finite simple graph is the infimum of pairwise minimum unit
cut values over distinct vertices. On empty and singleton types both sides are `⊤`. -/
theorem edgeConnectivity_eq_iInf_pairMinimumValue [Fintype V] :
    G.edgeConnectivity =
      ⨅ (s : V) (t : V) (_ : s ≠ t),
        ((TauCeti.TerminalCut.pairMinimumValue
          (TauCeti.pairCutCapacity
            (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) s t : ℕ) : ℕ∞) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun s ↦ le_iInf fun t ↦ le_iInf fun hst ↦ ?_
    exact (G.isEdgeConnected_iff_forall_le_pairMinimumValue _).mp
      (G.isEdgeConnected_iff_le_edgeConnectivity.mpr le_rfl) s t hst
  · refine G.isEdgeConnected_iff_le_edgeConnectivity.mp ?_
    rw [G.isEdgeConnected_iff_forall_le_pairMinimumValue]
    intro s t hst
    exact iInf_le_of_le s (iInf_le_of_le t (iInf_le_of_le hst le_rfl))

/-- A graph isomorphism preserves pairwise minimum cut values when edge weights correspond. -/
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

/-- Every finite simple graph on a nonempty vertex type admits a unit-capacity cut tree directly
on `V`. -/
theorem exists_isUnitCutTree [Fintype V] [Nonempty V] :
    ∃ (T : SimpleGraph V) (w : Sym2 V → ℕ),
      TauCeti.TerminalCut.IsCutTree
        (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w :=
  G.exists_isCutTree_indicator_edgeSet (fun _ ↦ (1 : ℕ)) fun _ _ ↦ Nat.zero_le 1

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

/-- A graph isomorphism carries flow-equivalent trees to flow-equivalent trees when edge weights
correspond. -/
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

/-- A graph isomorphism carries cut trees to cut trees when edge weights correspond. -/
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

end SimpleGraph

/-! ### Unit cut-tree queries, threshold partitions, and global edge connectivity -/

namespace TauCeti.TerminalCut.IsFlowEquivalentTree

open SimpleGraph

variable {V : Type*} [Fintype V] {G T : SimpleGraph V} {w : Sym2 V → ℕ}

/-- On a unit-capacity simple-graph flow-equivalent tree, two vertices (possibly equal) are
`k`-edge-reachable in `G` iff every edge on their tree path has weight at least `k`. -/
theorem isEdgeReachable_iff_forall_le_weight
    (hT : IsFlowEquivalentTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w)
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
  · rw [G.isEdgeReachable_iff_le_pairMinimumValue hst k]
    constructor
    · intro hk e he
      exact hk.trans (Nat.cast_le.mpr (hT.le_weight hp he))
    · intro h
      obtain ⟨e, he, hwe⟩ := hT.exists_weight_eq hst hp
      exact (h e he).trans_eq (congrArg Nat.cast hwe)

/-- **Threshold partition for simple graphs.** Deleting the tree edges of weight below `k` leaves
two vertices connected exactly when they are `k`-edge-reachable in `G`. -/
theorem reachable_deleteEdges_iff_isEdgeReachable
    (hT : IsFlowEquivalentTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w)
    (k : ℕ) {s t : V} :
    (T.deleteEdges {e | w e < k}).Reachable s t ↔ G.IsEdgeReachable k s t := by
  rw [hT.reachable_deleteEdges_iff]
  rcases eq_or_ne s t with rfl | hst
  · simp [SimpleGraph.IsEdgeReachable.rfl]
  · simp only [hst, false_or, G.isEdgeReachable_iff_le_pairMinimumValue hst k, Nat.cast_le]

/-- A finite simple graph is `k`-edge-connected iff every edge of a unit flow-equivalent tree has
weight at least `k`. This holds for every `k : ℕ∞` (and includes singleton graphs, where
`T.edgeSet = ∅`; empty vertex types admit no tree `T`). -/
theorem isEdgeConnected_iff_forall_le_weight
    (hT : IsFlowEquivalentTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w)
    (k : ℕ∞) :
    G.IsEdgeConnected k ↔ ∀ e ∈ T.edgeSet, k ≤ (w e : ℕ∞) := by
  constructor
  · intro h e he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : T.Adj u v := T.mem_edgeSet.mp he
      rw [hT.weight_eq huv]
      exact (G.isEdgeReachable_iff_le_pairMinimumValue huv.ne k).mp (h u v)
  · intro h s t
    obtain ⟨p, hp, -⟩ := hT.isTree.existsUnique_path s t
    exact (hT.isEdgeReachable_iff_forall_le_weight k hp).mpr fun e he ↦
      h e (p.edges_subset_edgeSet he)

/-- A finite simple graph is preconnected iff every edge of a unit flow-equivalent tree has
positive weight. -/
theorem preconnected_iff_forall_weight_pos
    (hT : IsFlowEquivalentTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w) :
    G.Preconnected ↔ ∀ e ∈ T.edgeSet, 0 < w e := by
  rw [← SimpleGraph.isEdgeConnected_one, hT.isEdgeConnected_iff_forall_le_weight 1]
  refine forall₂_congr fun e _ ↦ ?_
  rw [← Nat.cast_one, Nat.cast_le]
  omega

/-- A finite simple graph has no bridges in Mathlib's sense (`∀ e, ¬G.IsBridge e`) iff every edge
of a unit flow-equivalent tree has weight at least `2`. Note that Mathlib's `SimpleGraph.IsBridge`
does not require `e ∈ G.edgeSet`, so `∀ e, ¬G.IsBridge e` is equivalent to
`G.IsEdgeConnected 2` (including preconnectedness). -/
theorem forall_not_isBridge_iff_forall_two_le_weight
    (hT : IsFlowEquivalentTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w) :
    (∀ e, ¬G.IsBridge e) ↔ ∀ e ∈ T.edgeSet, 2 ≤ w e := by
  rw [← SimpleGraph.isEdgeConnected_two_iff_forall_not_isBridge,
    hT.isEdgeConnected_iff_forall_le_weight 2]
  refine forall₂_congr fun e _ ↦ ?_
  rw [← Nat.cast_ofNat, Nat.cast_le]

/-- The global edge connectivity of a finite simple graph is the infimum of edge weights in any
unit-capacity flow-equivalent tree. On singleton types `T.edgeSet` is empty and both sides equal
`⊤`. -/
theorem edgeConnectivity_eq_iInf_weight
    (hT : IsFlowEquivalentTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w) :
    G.edgeConnectivity = ⨅ e ∈ T.edgeSet, (w e : ℕ∞) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun e ↦ le_iInf fun he ↦ ?_
    exact (hT.isEdgeConnected_iff_forall_le_weight _).mp
      (G.isEdgeConnected_iff_le_edgeConnectivity.mpr le_rfl) e he
  · refine G.isEdgeConnected_iff_le_edgeConnectivity.mp ?_
    rw [hT.isEdgeConnected_iff_forall_le_weight]
    intro e he
    exact iInf_le_of_le e (iInf_le_of_le he le_rfl)

/-- Every tree edge of a unit flow-equivalent tree has weight at least the global edge
connectivity of `G`. -/
theorem edgeConnectivity_le_weight
    (hT : IsFlowEquivalentTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w)
    {e : Sym2 V} (he : e ∈ T.edgeSet) :
    G.edgeConnectivity ≤ (w e : ℕ∞) := by
  rw [hT.edgeConnectivity_eq_iInf_weight]
  exact iInf_le_of_le e (iInf_le_of_le he le_rfl)

/-- The global edge connectivity of a finite simple graph with at least two vertices is attained
as the weight of some edge in any unit-capacity flow-equivalent tree. -/
theorem exists_adj_edgeConnectivity_eq_weight [Nontrivial V]
    (hT : IsFlowEquivalentTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w) :
    ∃ u v, T.Adj u v ∧ G.edgeConnectivity = (w s(u, v) : ℕ∞) := by
  have hTne : T ≠ ⊥ := by
    intro h
    rw [h] at hT
    exact SimpleGraph.not_preconnected_bot hT.isTree.connected.preconnected
  obtain ⟨u, v, huv, hmin⟩ := T.exists_minimum_weight_edge hTne w
  refine ⟨u, v, huv, le_antisymm (hT.edgeConnectivity_le_weight (T.mem_edgeSet.mpr huv)) ?_⟩
  rw [hT.edgeConnectivity_eq_iInf_weight]
  exact le_iInf fun e ↦ le_iInf fun he ↦ Nat.cast_le.mpr (hmin e he)

end TauCeti.TerminalCut.IsFlowEquivalentTree

namespace TauCeti.TerminalCut.IsCutTree

open SimpleGraph

variable {V : Type*} [Fintype V] {G T : SimpleGraph V} {w : Sym2 V → ℕ}

/-- The number of edges of `G` crossing the fundamental side of a tree edge equals that edge's
weight. -/
theorem ncard_crossing_edgeSide
    (hT : IsCutTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w)
    {u v : V} (huv : T.Adj u v) :
    {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}.ncard = w s(u, v) := by
  rw [← G.pairCutCapacity_indicator_edgeSet_one, hT.apply_edgeSide huv]

/-- The extended cardinality of the crossing edge set of a tree edge's fundamental side equals
that edge's weight. -/
theorem encard_crossing_edgeSide
    (hT : IsCutTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w)
    {u v : V} (huv : T.Adj u v) :
    {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}.encard = (w s(u, v) : ℕ∞) := by
  have hfin : {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}.Finite := Set.toFinite _
  rw [← hfin.cast_ncard_eq, hT.ncard_crossing_edgeSide huv]

/-- Deleting the edges of `G` crossing the fundamental side of an edge on the tree path from `s`
to `t` separates `s` from `t` in `G`. -/
theorem not_reachable_deleteEdges_crossing_edgeSide
    (hT : IsCutTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w)
    {s t u v : V} {p : T.Walk s t} (hp : p.IsPath) (huv : s(u, v) ∈ p.edges)
    (hs : s ∈ T.edgeSide u v) :
    ¬(G.deleteEdges {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}).Reachable s t := by
  have ht : t ∉ T.edgeSide u v :=
    (hp.mem_edges_iff_notMem_edgeSide hT.isTree.isAcyclic hs).mp huv
  exact G.not_reachable_deleteEdges_crossing (mem_coe.mpr hs) (by simpa using ht)

/-- **Query optimality certificate.** For a minimum-weight edge `s(u, v)` on the tree path from `s`
to `t` with `s` on the side of `u`, the edges of `G` crossing `T.edgeSide u v` form a minimum
`s`--`t` edge separator: every `s`--`t` edge separator `F` has at least as many edges. -/
theorem encard_crossing_edgeSide_le
    (hT : IsCutTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w)
    {s t u v : V} {p : T.Walk s t} (hp : p.IsPath) (huv : s(u, v) ∈ p.edges)
    (hmin : ∀ e ∈ p.edges, w s(u, v) ≤ w e) (hs : s ∈ T.edgeSide u v)
    {F : Set (Sym2 V)} (hF : ¬(G.deleteEdges F).Reachable s t) :
    {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}.encard ≤ F.encard := by
  have hcut := hT.isMinimum_edgeSide_of_mem_edges hp huv hmin hs
  have hadj : T.Adj u v := p.adj_of_mem_edges huv
  rw [hT.encard_crossing_edgeSide hadj, ← hT.apply_edgeSide hadj, ← hcut.pairMinimumValue_eq]
  exact G.pairMinimumValue_indicator_edgeSet_one_le_encard_of_not_reachable hF

/-- A minimum-weight edge of a unit cut tree for a finite simple graph with at least two vertices
produces a disconnecting edge cut whose size equals the global edge connectivity of `G`. -/
theorem exists_edgeSide_crossing_eq_edgeConnectivity [Nontrivial V]
    (hT : IsCutTree
      (TauCeti.pairCutCapacity (G.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w) :
    ∃ u v, T.Adj u v ∧
      ¬(G.deleteEdges {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}).Preconnected ∧
      {e ∈ G.edgeSet | e.Crosses (T.edgeSide u v : Set V)}.encard = G.edgeConnectivity := by
  obtain ⟨u, v, huv, heq⟩ := hT.toIsFlowEquivalentTree.exists_adj_edgeConnectivity_eq_weight
  refine ⟨u, v, huv, ?_, ?_⟩
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
    TauCeti.TerminalCut.IsCutTree
      (TauCeti.pairCutCapacity ((⊤ : SimpleGraph V).edgeSet.indicator fun _ ↦ (1 : ℕ)))
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
        TauCeti.pairCutCapacity ((⊤ : SimpleGraph V).edgeSet.indicator fun _ ↦ (1 : ℕ))
          ((starGraph r).edgeSide u v) = Fintype.card V - 1 := by
      rcases starGraph_adj.mp huv with ⟨hne, rfl | rfl⟩
      · rw [← TauCeti.pairCutCapacity_compl,
          hbridge.compl_edgeSide hpre,
          hleaf hne.symm, pairCutCapacity_indicator_edgeSet_one_top]
        simp
      · rw [hleaf hne, pairCutCapacity_indicator_edgeSet_one_top]
        simp
    rw [TauCeti.TerminalCut.isMinimum_singleton_iff_pairMinimumValue_eq,
      pairMinimumValue_indicator_edgeSet_one_top huv.ne]
    exact ⟨self_mem_edgeSide _ u v, hbridge.notMem_edgeSide, hval⟩
  · intro u v huv
    exact (pairMinimumValue_indicator_edgeSet_one_top huv.ne).symm

/-- The global edge connectivity of the complete graph on a finite nontrivial vertex type `V` is
`|V| - 1`. -/
theorem edgeConnectivity_top [Fintype V] [Nontrivial V] :
    (⊤ : SimpleGraph V).edgeConnectivity = ((Fintype.card V - 1 : ℕ) : ℕ∞) := by
  obtain ⟨r⟩ := (inferInstance : Nonempty V)
  obtain ⟨u, v, -, h⟩ :=
    (isCutTree_starGraph_top r).toIsFlowEquivalentTree.exists_adj_edgeConnectivity_eq_weight
  exact h

end SimpleGraph

/-! ### Concrete examples -/

namespace TauCeti.TerminalCut

open SimpleGraph

/-! #### A disconnected simple graph on `Fin 3` -/

private abbrev disconnectedSimpleGraph : SimpleGraph (Fin 3) :=
  SimpleGraph.fromEdgeSet {s(0, 1)}

/-- Every unit-capacity cut tree for the graph with edge `s(0, 1)` and isolated vertex `2` has a
zero-weight edge, and its global edge connectivity is zero. -/
example (T : SimpleGraph (Fin 3)) (w : Sym2 (Fin 3) → ℕ)
    (hT : IsCutTree
      (pairCutCapacity (disconnectedSimpleGraph.edgeSet.indicator fun _ ↦ (1 : ℕ))) T w) :
    (∃ e ∈ T.edgeSet, w e = 0) ∧ disconnectedSimpleGraph.edgeConnectivity = 0 := by
  have hnot : ¬disconnectedSimpleGraph.Preconnected := by
    intro hconn
    obtain ⟨p⟩ := hconn 2 0
    cases p with
    | cons hadj _ =>
      simp only [disconnectedSimpleGraph, fromEdgeSet_adj, Set.mem_singleton_iff] at hadj
      rcases Sym2.eq_iff.mp hadj.1 with ⟨h, -⟩ | ⟨h, -⟩ <;> simp at h
  have hex : ∃ e ∈ T.edgeSet, w e = 0 := by
    by_contra h
    push Not at h
    exact hnot (hT.toIsFlowEquivalentTree.preconnected_iff_forall_weight_pos.mpr
      fun e he ↦ Nat.pos_of_ne_zero (h e he))
  refine ⟨hex, le_antisymm ?_ bot_le⟩
  obtain ⟨e, he, hwe⟩ := hex
  simpa [hwe] using hT.toIsFlowEquivalentTree.edgeConnectivity_le_weight he

/-! #### Separating flow-equivalent trees from cut trees on `K₄` -/

/-- On the complete graph `K₄`, the path `pathGraph 4` with constant weight `3` is flow-equivalent
for unit cut capacity, because every pair of distinct vertices has minimum cut value `3`. -/
example :
    IsFlowEquivalentTree
      (pairCutCapacity ((⊤ : SimpleGraph (Fin 4)).edgeSet.indicator fun _ ↦ (1 : ℕ)))
      (pathGraph 4) (fun _ ↦ 3) where
  isTree := isTree_pathGraph_add_one 3
  le_weight s t _ _ _ _ := by
    rcases eq_or_ne s t with rfl | hst
    · simp
    · rw [pairMinimumValue_indicator_edgeSet_one_top hst]
      simp
  exists_weight_eq s t hst p _ := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges
      (by rw [Ne, Walk.edges_eq_nil]; exact Walk.not_nil_of_ne hst)
    refine ⟨e, he, ?_⟩
    rw [pairMinimumValue_indicator_edgeSet_one_top hst]
    simp

private theorem pathGraph_four_edgeSide_one_two :
    (pathGraph 4).edgeSide 1 2 = {0, 1} := by
  have h12 : (pathGraph 4).Adj 1 2 := by simp [pathGraph_adj]
  have hbridge : (pathGraph 4).IsBridge s(1, 2) :=
    isAcyclic_iff_forall_adj_isBridge.mp (isAcyclic_pathGraph 4) h12
  have h0 : (0 : Fin 4) ∈ (pathGraph 4).edgeSide 1 2 :=
    mem_edgeSide.mpr (deleteEdges_adj.mpr ⟨by simp [pathGraph_adj], by decide⟩).reachable
  have h3 : (3 : Fin 4) ∈ (pathGraph 4).edgeSide 2 1 :=
    mem_edgeSide.mpr (deleteEdges_adj.mpr ⟨by simp [pathGraph_adj], by decide⟩).reachable
  ext x
  fin_cases x
  · simpa using h0
  · simp
  · simpa using hbridge.notMem_edgeSide
  · simpa using fun h ↦ Finset.disjoint_left.mp hbridge.disjoint_edgeSide h h3

/-- On `K₄`, `pathGraph 4` with constant weight `3` is not a cut tree: deleting its middle edge
`s(1, 2)` leaves the side `{0, 1}`, across which four edges of `K₄` cross. -/
example :
    ¬IsCutTree
      (pairCutCapacity ((⊤ : SimpleGraph (Fin 4)).edgeSet.indicator fun _ ↦ (1 : ℕ)))
      (pathGraph 4) (fun _ ↦ 3) := by
  intro hT
  have h12 : (pathGraph 4).Adj 1 2 := by simp [pathGraph_adj]
  have happly := hT.apply_edgeSide h12
  rw [pathGraph_four_edgeSide_one_two, pairCutCapacity_indicator_edgeSet_one_top] at happly
  have hcard : #({0, 1} : Finset (Fin 4)) = 2 := by decide
  rw [hcard, Fintype.card_fin] at happly
  omega

/-! #### The diamond graph `K₄ - s(0, 3)`: multi-level threshold partitions -/

/-- The diamond graph obtained by deleting the edge `s(0, 3)` from `K₄`. Vertices `0` and `3`
have degree `2`, while `1` and `2` have degree `3` and local edge connectivity `3`. -/
private def diamondGraph : SimpleGraph (Fin 4) :=
  (⊤ : SimpleGraph (Fin 4)).deleteEdges {s(0, 3)}

private theorem diamondGraph_cut (S : Finset (Fin 4)) [Decidable (s((0 : Fin 4), 3).Crosses S)] :
    pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ)) S +
        (if s((0 : Fin 4), 3).Crosses (S : Set (Fin 4)) then 1 else 0) =
      #S * (4 - #S) := by
  have he : s((0 : Fin 4), 3) ∈ (⊤ : SimpleGraph (Fin 4)).edgeSet := by decide
  have h := pairCutCapacity_indicator_edgeSet_deleteEdges_singleton (⊤ : SimpleGraph (Fin 4))
    (fun _ ↦ (1 : ℕ)) he S
  rw [pairCutCapacity_indicator_edgeSet_one_top, Fintype.card_fin] at h
  exact h

private theorem diamondGraph_cut_ge_two {S : Finset (Fin 4)} {s t : Fin 4}
    (hs : s ∈ S) (ht : t ∉ S) :
    2 ≤ pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ)) S := by
  classical
  have h := diamondGraph_cut S
  have hpos : 1 ≤ #S := Finset.one_le_card.mpr ⟨s, hs⟩
  have hlt : #S < 4 := by simpa using Finset.card_lt_univ_of_notMem ht
  have hprod : 3 ≤ #S * (4 - #S) := by
    have hcases : #S = 1 ∨ #S = 2 ∨ #S = 3 := by omega
    rcases hcases with hS | hS | hS <;> simp [hS]
  split_ifs at h <;> omega

private theorem diamondGraph_cut_singleton_zero :
    pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ)) {0} = 2 := by
  classical
  have h := diamondGraph_cut {0}
  have hcross : s((0 : Fin 4), 3).Crosses (({0} : Finset (Fin 4)) : Set (Fin 4)) := by
    simp [Sym2.crosses_mk_iff]
  simp only [hcross, ↓reduceIte, card_singleton] at h
  omega

private theorem diamondGraph_cut_singleton_three :
    pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ)) {3} = 2 := by
  classical
  have h := diamondGraph_cut {3}
  have hcross : s((0 : Fin 4), 3).Crosses (({3} : Finset (Fin 4)) : Set (Fin 4)) := by
    simp [Sym2.crosses_mk_iff]
  simp only [hcross, ↓reduceIte, card_singleton] at h
  omega

private theorem diamondGraph_cut_pair_zero_one :
    pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ)) {0, 1} = 3 := by
  classical
  have h := diamondGraph_cut {0, 1}
  have hcross : s((0 : Fin 4), 3).Crosses (({0, 1} : Finset (Fin 4)) : Set (Fin 4)) := by
    simp [Sym2.crosses_mk_iff]
  have hcard : #({0, 1} : Finset (Fin 4)) = 2 := by decide
  simp only [hcross, ↓reduceIte, hcard] at h
  omega

private theorem diamondGraph_minCut_zero_one :
    pairMinimumValue
        (pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ))) 0 1 = 2 := by
  let f := pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ))
  refine le_antisymm ?_ ?_
  · calc
      pairMinimumValue f 0 1 ≤ f {0} :=
        pairMinimumValue_le f (mem_singleton_self 0) (by decide)
      _ = 2 := diamondGraph_cut_singleton_zero
  · obtain ⟨S, hS⟩ := exists_minimum f (disjoint_singleton.mpr (by decide : (0 : Fin 4) ≠ 1))
    obtain ⟨hs, ht⟩ := isAdmissible_singleton.mp hS.admissible
    rw [hS.pairMinimumValue_eq]
    exact diamondGraph_cut_ge_two hs ht

private theorem diamondGraph_minCut_two_three :
    pairMinimumValue
        (pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ))) 2 3 = 2 := by
  let f := pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ))
  refine le_antisymm ?_ ?_
  · calc
      pairMinimumValue f 2 3 ≤ f ({3}ᶜ : Finset (Fin 4)) :=
        pairMinimumValue_le f (by decide) (by decide)
      _ = f {3} := pairCutCapacity_compl _ {3}
      _ = 2 := diamondGraph_cut_singleton_three
  · obtain ⟨S, hS⟩ := exists_minimum f (disjoint_singleton.mpr (by decide : (2 : Fin 4) ≠ 3))
    obtain ⟨hs, ht⟩ := isAdmissible_singleton.mp hS.admissible
    rw [hS.pairMinimumValue_eq]
    exact diamondGraph_cut_ge_two hs ht

private theorem diamondGraph_minCut_one_two :
    pairMinimumValue
        (pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ))) 1 2 = 3 := by
  classical
  let f := pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ))
  refine le_antisymm ?_ ?_
  · calc
      pairMinimumValue f 1 2 ≤ f {0, 1} :=
        pairMinimumValue_le f (by decide) (by decide)
      _ = 3 := diamondGraph_cut_pair_zero_one
  · obtain ⟨S, hS⟩ := exists_minimum f (disjoint_singleton.mpr (by decide : (1 : Fin 4) ≠ 2))
    obtain ⟨h1, h2⟩ := isAdmissible_singleton.mp hS.admissible
    rw [hS.pairMinimumValue_eq]
    dsimp only [f]
    have h := diamondGraph_cut S
    have hpos : 1 ≤ #S := Finset.one_le_card.mpr ⟨1, h1⟩
    have hlt : #S < 4 := by simpa using Finset.card_lt_univ_of_notMem h2
    by_cases hcross : s((0 : Fin 4), 3).Crosses (S : Set (Fin 4))
    · simp only [hcross, ↓reduceIte] at h
      have hcard2 : #S = 2 := by
        rcases (Sym2.crosses_mk_iff.mp hcross) with ⟨h0, h3⟩ | ⟨h3, h0⟩
        · have hsub : S = {0, 1} := by
            ext x; fin_cases x <;> simp_all
          rw [hsub]; decide
        · have hsub : S = {1, 3} := by
            ext x; fin_cases x <;> simp_all
          rw [hsub]; decide
      rw [hcard2] at h
      omega
    · simp only [hcross, ↓reduceIte, add_zero] at h
      have hprod : 3 ≤ #S * (4 - #S) := by
        have hcases : #S = 1 ∨ #S = 2 ∨ #S = 3 := by omega
        rcases hcases with hS | hS | hS <;> simp [hS]
      omega

private theorem isCutTree_pathGraph_diamondGraph :
    IsCutTree
      (pairCutCapacity (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ)))
      (pathGraph 4) (fun e ↦ if e = s(1, 2) then 3 else 2) := by
  have hbr := isAcyclic_iff_forall_adj_isBridge.mp (isAcyclic_pathGraph 4)
  have hpre : (pathGraph 4).Preconnected := (isTree_pathGraph_add_one 3).connected.preconnected
  have hcomm := fun u v ↦ pairMinimumValue_comm
    (pairCutCapacity_compl (diamondGraph.edgeSet.indicator fun _ ↦ (1 : ℕ))) u v
  have hadj : ∀ {u v : Fin 4}, (pathGraph 4).Adj u v →
      (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨
      (u = 2 ∧ v = 1) ∨ (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp [pathGraph_adj] at huv ⊢
  have hside01 : (pathGraph 4).edgeSide 0 1 = {0} :=
    edgeSide_eq_singleton fun y hy ↦ by
      fin_cases y <;> simp [pathGraph_adj] at hy ⊢
  have hside32 : (pathGraph 4).edgeSide 3 2 = {3} :=
    edgeSide_eq_singleton fun y hy ↦ by
      fin_cases y <;> simp [pathGraph_adj] at hy ⊢
  refine IsCutTree.of_isMinimum_edgeSide (isTree_pathGraph_add_one 3) ?_ ?_
  · intro u v huv
    rw [isMinimum_singleton_iff_pairMinimumValue_eq]
    refine ⟨self_mem_edgeSide _ u v, (hbr huv).notMem_edgeSide, ?_⟩
    rcases hadj huv with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hside01, diamondGraph_cut_singleton_zero, diamondGraph_minCut_zero_one]
    · rw [← pairCutCapacity_compl, (hbr huv).compl_edgeSide hpre, hside01,
        diamondGraph_cut_singleton_zero, hcomm 1 0, diamondGraph_minCut_zero_one]
    · rw [pathGraph_four_edgeSide_one_two, diamondGraph_cut_pair_zero_one,
        diamondGraph_minCut_one_two]
    · rw [← pairCutCapacity_compl, (hbr huv).compl_edgeSide hpre,
        pathGraph_four_edgeSide_one_two, diamondGraph_cut_pair_zero_one, hcomm 2 1,
        diamondGraph_minCut_one_two]
    · rw [← pairCutCapacity_compl, (hbr huv).compl_edgeSide hpre, hside32,
        diamondGraph_cut_singleton_three, diamondGraph_minCut_two_three]
    · rw [hside32, diamondGraph_cut_singleton_three, hcomm 3 2, diamondGraph_minCut_two_three]
  · intro u v huv
    rcases hadj huv with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [diamondGraph_minCut_zero_one]; decide
    · rw [hcomm 1 0, diamondGraph_minCut_zero_one]; decide
    · rw [diamondGraph_minCut_one_two]; decide
    · rw [hcomm 2 1, diamondGraph_minCut_one_two]; decide
    · rw [diamondGraph_minCut_two_three]; decide
    · rw [hcomm 3 2, diamondGraph_minCut_two_three]; decide

/-- On the diamond graph `K₄ - s(0, 3)`, the cut tree
`(pathGraph 4, fun e ↦ if e = s(1, 2) then 3 else 2)` exhibits two distinct nonzero local
edge-connectivity levels (`2` and `3`), yields global edge connectivity `2`, realizes the
threshold-`3` partition by deleting edges of weight `< 3`, and matches the `edgeFinset` indicator
formulation. -/
example :
    diamondGraph.edgeConnectivity = 2 ∧
    diamondGraph.IsEdgeConnected 2 ∧
    ¬diamondGraph.IsEdgeConnected 3 ∧
    diamondGraph.IsEdgeReachable 3 1 2 ∧
    ¬diamondGraph.IsEdgeReachable 3 0 1 ∧
    ¬diamondGraph.IsEdgeReachable 4 1 2 ∧
    ((pathGraph 4).deleteEdges {e | (if e = s(1, 2) then 3 else 2) < 3}).Reachable 1 2 ∧
    ¬((pathGraph 4).deleteEdges {e | (if e = s(1, 2) then 3 else 2) < 3}).Reachable 0 1 ∧
    (∀ [Fintype diamondGraph.edgeSet],
      diamondGraph.IsEdgeReachable (3 : ℕ) 1 2 ↔
        3 ≤ pairMinimumValue
          (pairCutCapacity fun e ↦
            if e ∈ diamondGraph.edgeFinset then (1 : ℕ) else 0) 1 2) := by
  have hT := isCutTree_pathGraph_diamondGraph.toIsFlowEquivalentTree
  have hne : s((0 : Fin 4), 1) ≠ s(1, 2) := by decide
  have h2 : diamondGraph.IsEdgeConnected 2 := by
    rw [hT.isEdgeConnected_iff_forall_le_weight]
    intro e _
    split_ifs <;> decide
  have hnot3 : ¬diamondGraph.IsEdgeConnected 3 := by
    rw [hT.isEdgeConnected_iff_forall_le_weight]
    push Not
    refine ⟨s(0, 1), by simp [pathGraph_adj], ?_⟩
    simp only [hne, ↓reduceIte]
    exact_mod_cast (by decide : 2 < 3)
  have hec : diamondGraph.edgeConnectivity = 2 := by
    refine le_antisymm ?_ (diamondGraph.isEdgeConnected_iff_le_edgeConnectivity.mp h2)
    have h01 : s((0 : Fin 4), 1) ∈ (pathGraph 4).edgeSet := by simp [pathGraph_adj]
    simpa [hne] using hT.edgeConnectivity_le_weight h01
  have h12_3 : diamondGraph.IsEdgeReachable 3 1 2 := by
    rw [diamondGraph.isEdgeReachable_iff_le_pairMinimumValue (by decide : (1 : Fin 4) ≠ 2) 3,
      diamondGraph_minCut_one_two]
    norm_cast
  have h01_3 : ¬diamondGraph.IsEdgeReachable 3 0 1 := by
    rw [diamondGraph.isEdgeReachable_iff_le_pairMinimumValue (by decide : (0 : Fin 4) ≠ 1) 3,
      diamondGraph_minCut_zero_one]
    decide
  have h12_4 : ¬diamondGraph.IsEdgeReachable 4 1 2 := by
    rw [diamondGraph.isEdgeReachable_iff_le_pairMinimumValue (by decide : (1 : Fin 4) ≠ 2) 4,
      diamondGraph_minCut_one_two]
    decide
  refine ⟨hec, h2, hnot3, h12_3, h01_3, h12_4,
    (hT.reachable_deleteEdges_iff_isEdgeReachable 3).mpr h12_3,
    mt (hT.reachable_deleteEdges_iff_isEdgeReachable 3).mp h01_3, fun {_} ↦ ?_⟩
  rw [← diamondGraph.indicator_edgeSet_eq_ite_mem_edgeFinset (fun _ ↦ (1 : ℕ)),
    diamondGraph.isEdgeReachable_iff_le_pairMinimumValue (by decide : (1 : Fin 4) ≠ 2) (3 : ℕ),
    Nat.cast_le]

end TauCeti.TerminalCut
