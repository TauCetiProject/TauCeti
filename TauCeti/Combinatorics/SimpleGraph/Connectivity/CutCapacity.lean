/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Combinatorics.Graph.Connectivity.CutCapacity
import TauCeti.Combinatorics.SimpleGraph.Bipartite

/-!
# Cut capacities of simple graphs

This file develops elementary formulas and functoriality properties for weighted and unit cut
capacities on `SimpleGraph V`, without importing minimum-cut or Gomory--Hu cut-tree theory.
Weighted cuts are represented on unordered vertex pairs by `G.edgeSet.indicator c`, while unit cuts
use `G.unitCutCapacity`.

## Main results

* `SimpleGraph.unitCutCapacity_eq_card_filter`: unit cut capacity as the cardinality of the finset
  of edges in `G.edgeFinset` crossing `S`.
* `SimpleGraph.pairCutCapacity_indicator_edgeSet_singleton` and
  `SimpleGraph.unitCutCapacity_singleton`: singleton cut capacity sums incident edge weights and
  equals `G.degree v` for unit weights.
* `SimpleGraph.pairCutCapacity_indicator_edgeSet_top` and `SimpleGraph.unitCutCapacity_top`:
  complete-graph cut capacities, with `#S * (Fintype.card V - #S)` crossing edges for unit weights.
* `SimpleGraph.pairCutCapacity_indicator_edgeSet_deleteEdges_singleton` and
  `SimpleGraph.unitCutCapacity_deleteEdges_singleton`: effect of deleting a single edge of `G`.
* `SimpleGraph.pairCutCapacity_indicator_edgeSet_mono` and `SimpleGraph.unitCutCapacity_mono`:
  monotonicity with respect to subgraph inclusion `G ≤ H`.
* `SimpleGraph.Iso.pairCutCapacity_indicator_edgeSet` and `SimpleGraph.Iso.unitCutCapacity_map`:
  invariance under graph isomorphisms.
-/

public section

open Finset

namespace SimpleGraph

variable {V W K : Type*}

/-- Unit cut capacity of a simple graph with finitely many edges equals the cardinality of the
finset of edges in `G.edgeFinset` crossing `S`. -/
theorem unitCutCapacity_eq_card_filter (G : SimpleGraph V) [Fintype G.edgeSet]
    (S : Finset V) [DecidablePred fun e : Sym2 V ↦ e.Crosses (S : Set V)] :
    G.unitCutCapacity S = #{e ∈ G.edgeFinset | e.Crosses (S : Set V)} := by
  rw [unitCutCapacity_eq_ncard, ← Set.ncard_coe_finset]
  congr 1
  ext e
  simp

/-- The weighted cut capacity of a singleton `{v}` is the sum of weights of edges incident to
`v`. -/
theorem pairCutCapacity_indicator_edgeSet_singleton [Fintype V] [AddCommMonoid K]
    (G : SimpleGraph V) (c : Sym2 V → K) (v : V) [Fintype (G.neighborSet v)] :
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
theorem unitCutCapacity_singleton (G : SimpleGraph V) [Finite G.edgeSet]
    (v : V) [Fintype (G.neighborSet v)] :
    G.unitCutCapacity {v} = G.degree v := by
  rw [unitCutCapacity_eq_ncard, ← card_neighborFinset_eq_degree, ← Set.ncard_coe_finset,
    coe_neighborFinset]
  symm
  refine Set.ncard_congr (fun w _ ↦ s(v, w)) ?_ ?_ ?_
  · intro w hw
    exact ⟨G.mem_edgeSet.mpr hw, by simp [Sym2.crosses_mk_iff, hw.ne.symm]⟩
  · intro w₁ w₂ _ _ h
    rcases Sym2.eq_iff.mp h with ⟨-, rfl⟩ | ⟨hvw, rfl⟩
    · rfl
    · exact hvw
  · rintro e ⟨heG, hev⟩
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [Set.mem_ofPred_eq, Sym2.crosses_mk_iff, Finset.coe_singleton,
        Set.mem_singleton_iff] at hev
      rcases hev with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨y, G.mem_edgeSet.mp heG, rfl⟩
      · exact ⟨x, (G.mem_edgeSet.mp heG).symm, Sym2.eq_swap⟩

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

/-- In the complete graph `⊤`, the number of edges crossing `S` is `#S * (Fintype.card V - #S)`. -/
theorem unitCutCapacity_top [Fintype V] (S : Finset V) :
    (⊤ : SimpleGraph V).unitCutCapacity S = #S * (Fintype.card V - #S) := by
  classical
  have hset :
      (⊤ : SimpleGraph V).edgeSet ∩ {e | e.Crosses (S : Set V)} =
        (((⊤ : SimpleGraph V).between (S : Set V) (S : Set V)ᶜ).edgeFinset : Set (Sym2 V)) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [Set.mem_inter_iff, mem_edgeSet, top_adj, Set.mem_ofPred_eq, Sym2.crosses_mk_iff,
        coe_edgeFinset, between_adj, Set.mem_compl_iff]
      tauto
  rw [unitCutCapacity_eq_ncard, hset, Set.ncard_coe_finset,
    card_edgeFinset_top_between disjoint_compl_right]
  simp only [Set.toFinset_compl, Finset.toFinset_coe, Finset.card_compl]

/-- Deleting a single edge `e` of `G` reduces the weighted cut capacity of `S` by `c e` if `e`
crosses `S`, and leaves it unchanged otherwise. -/
theorem pairCutCapacity_indicator_edgeSet_deleteEdges_singleton [Fintype V] [AddCommMonoid K]
    (G : SimpleGraph V) (c : Sym2 V → K) {e : Sym2 V} (he : e ∈ G.edgeSet) (S : Finset V)
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

/-- Deleting a single edge `e` of `G` reduces the unit cut capacity of `S` by `1` if `e` crosses
`S`, and leaves it unchanged otherwise. -/
theorem unitCutCapacity_deleteEdges_singleton [Finite V] (G : SimpleGraph V)
    {e : Sym2 V} (he : e ∈ G.edgeSet) (S : Finset V) [Decidable (e.Crosses (S : Set V))] :
    (G.deleteEdges {e}).unitCutCapacity S + (if e.Crosses (S : Set V) then 1 else 0) =
      G.unitCutCapacity S := by
  let _ := Fintype.ofFinite V
  rw [unitCutCapacity_apply_eq_pairCutCapacity, G.unitCutCapacity_apply_eq_pairCutCapacity]
  exact G.pairCutCapacity_indicator_edgeSet_deleteEdges_singleton (fun _ ↦ 1) he S

/-- Weighted simple-graph cut capacities are monotone in the graph when weights are nonnegative on
edges. -/
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

/-- Unit cut capacities are monotone with respect to subgraph inclusion. -/
theorem unitCutCapacity_mono {G H : SimpleGraph V} [Finite G.edgeSet] [Finite H.edgeSet]
    (hGH : G ≤ H) (S : Finset V) :
    G.unitCutCapacity S ≤ H.unitCutCapacity S := by
  rw [unitCutCapacity_eq_ncard, unitCutCapacity_eq_ncard]
  exact Set.ncard_le_ncard (Set.inter_subset_inter_left _ (edgeSet_mono hGH)) (Set.toFinite _)

/-- A graph isomorphism preserves weighted simple-graph cut capacities when edge weights
correspond. -/
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

/-- A graph isomorphism preserves unit cut capacities. -/
theorem Iso.unitCutCapacity_map [Finite V] [Finite W] {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (S : Finset V) :
    H.unitCutCapacity (S.map e.toEquiv.toEmbedding) = G.unitCutCapacity S := by
  let _ := Fintype.ofFinite V
  let _ := Fintype.ofFinite W
  rw [H.unitCutCapacity_apply_eq_pairCutCapacity, G.unitCutCapacity_apply_eq_pairCutCapacity]
  exact e.pairCutCapacity_indicator_edgeSet (fun _ ↦ 1) (fun _ ↦ 1) (fun _ _ _ ↦ rfl) S

end SimpleGraph
