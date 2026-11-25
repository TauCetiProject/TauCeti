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

private theorem edgeSet_inter_crosses_singleton (G : SimpleGraph V) (v : V) :
    G.edgeSet ∩ {e | e.Crosses (({v} : Finset V) : Set V)} = G.incidenceSet v := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [Set.mem_inter_iff, mem_edgeSet, Set.mem_ofPred_eq, Finset.coe_singleton,
      Sym2.crosses_mk_iff, Set.mem_singleton_iff, mk'_mem_incidenceSet_iff]
    exact ⟨fun ⟨hxy, hv⟩ ↦ ⟨hxy, hv.elim (fun h ↦ .inl h.1.symm) (fun h ↦ .inr h.1.symm)⟩,
      fun ⟨hxy, hv⟩ ↦ ⟨hxy, hv.elim (fun h ↦ .inl ⟨h.symm, h ▸ hxy.ne.symm⟩)
        (fun h ↦ .inr ⟨h.symm, h ▸ hxy.ne⟩)⟩⟩

/-- The weighted cut capacity of a singleton `{v}` is the sum of weights of edges incident to
`v`. -/
theorem pairCutCapacity_indicator_edgeSet_singleton [Fintype V] [AddCommMonoid K]
    (G : SimpleGraph V) (c : Sym2 V → K) (v : V) [Fintype (G.neighborSet v)] :
    TauCeti.pairCutCapacity (G.edgeSet.indicator c) {v} =
      ∑ w ∈ G.neighborFinset v, c s(v, w) := by
  classical
  have hmem (p : Sym2 V) :
      p ∈ G.edgeSet ∧ p.Crosses (({v} : Finset V) : Set V) ↔ p ∈ G.incidenceFinset v := by
    rw [mem_incidenceFinset, ← G.edgeSet_inter_crosses_singleton v, Set.mem_inter_iff]
    rfl
  rw [TauCeti.pairCutCapacity_def]
  have hsum :
      (∑ p : Sym2 V, if p.Crosses (({v} : Finset V) : Set V) then G.edgeSet.indicator c p else 0) =
        ∑ p ∈ G.incidenceFinset v, c p := by
    have hfilt : G.incidenceFinset v = univ.filter (· ∈ G.incidenceFinset v) := by ext; simp
    rw [hfilt, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    by_cases hp : p ∈ G.edgeSet <;> by_cases hcross : p.Crosses (({v} : Finset V) : Set V)
    · have hinc : p ∈ G.incidenceFinset v := (hmem p).mp ⟨hp, hcross⟩
      simp only [hcross, hinc, ↓reduceIte, Set.indicator_of_mem hp]
    · have hinc : p ∉ G.incidenceFinset v := fun h ↦ hcross ((hmem p).mpr h).2
      simp only [hcross, hinc, ↓reduceIte]
    · have hinc : p ∉ G.incidenceFinset v := fun h ↦ hp ((hmem p).mpr h).1
      simp only [hcross, hinc, ↓reduceIte, Set.indicator_of_notMem hp]
    · have hinc : p ∉ G.incidenceFinset v := fun h ↦ hp ((hmem p).mpr h).1
      simp only [hcross, hinc, ↓reduceIte]
  have hinc_sub : ∑ p ∈ G.incidenceFinset v, c p = ∑ e : G.incidenceSet v, c e.val :=
    Finset.sum_subtype (G.incidenceFinset v) (fun _ ↦ mem_incidenceFinset) c
  have hnb_sub :
      ∑ w ∈ G.neighborFinset v, c s(v, w) = ∑ w : G.neighborSet v, c s(v, w.val) :=
    Finset.sum_subtype (G.neighborFinset v) (fun _ ↦ G.mem_neighborFinset v _) (fun w ↦ c s(v, w))
  rw [hsum, hinc_sub, hnb_sub]
  exact (Fintype.sum_equiv (G.incidenceSetEquivNeighborSet v).symm
    (fun w ↦ c s(v, w.val)) (fun e ↦ c e.val) fun _ ↦ rfl).symm

/-- The unit cut capacity of a singleton `{v}` is the degree of `v`. -/
@[simp]
theorem unitCutCapacity_singleton (G : SimpleGraph V) [Finite G.edgeSet]
    (v : V) [Fintype (G.neighborSet v)] :
    G.unitCutCapacity {v} = G.degree v := by
  rw [unitCutCapacity_eq_ncard, G.edgeSet_inter_crosses_singleton v, G.ncard_incidenceSet]

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
