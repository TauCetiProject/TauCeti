/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.OddTriple.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.SimpleGraph.Degree

/-!
# Counting triples spanning an odd number of edges

This file counts `G.oddTripleFinset` in terms of vertex degrees, edge counts, and triangles:

* `#G.oddTripleFinset + 2 * ∑ v, (G.degree v).choose 2 = (card V - 2) * #G.edgeFinset +
  4 * #(G.cliqueFinset 3)` (`SimpleGraph.card_oddTripleFinset_add_two_mul_sum_degree_choose_two`).
* In a `3`-clique-free graph, `#G.oddTripleFinset + ∑ v, G.degree v ^ 2 = card V * #G.edgeFinset`
  (`SimpleGraph.card_oddTripleFinset_add_sum_degree_sq`), derived from the choose-two identity via
  `d ^ 2 = d + 2 * d.choose 2` and the degree sum (Kozlov, arXiv:1610.07136v2, equation (2.5)).
* When every vertex has degree at most `1`,
  `#G.oddTripleFinset = (card V - 2) * #G.edgeFinset`
  (`SimpleGraph.card_oddTripleFinset_of_degree_le_one`).

## References

* D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136v2, equation (2.5) and
  Lemma 3.10.
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V]

section EdgeSet

variable (G : SimpleGraph V) [Fintype G.edgeSet]

/-- Every edge lies in `card V - 2` triples, so the edges spanned by the triples add up to
`card V - 2` times the number of edges. -/
theorem sum_powersetCard_three_card_edgeFinset_inter_sym2 :
    ∑ t ∈ univ.powersetCard 3, #(G.edgeFinset ∩ t.sym2) =
      (Fintype.card V - 2) * #G.edgeFinset := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := univ.powersetCard 3) (t := G.edgeFinset) (r := fun t e ↦ e ∈ t.sym2)
  simp only [bipartiteAbove, bipartiteBelow, filter_mem_eq_inter] at h
  rw [h, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun e he ↦ ?_
  have he2 : #e.toFinset = 2 :=
    Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp he))
  have hsub : {t ∈ (univ : Finset V).powersetCard 3 | e ∈ t.sym2} =
      {t ∈ (univ : Finset V).powersetCard 3 | e.toFinset ⊆ t} := by
    ext t
    simp [mem_sym2_iff, subset_iff]
  rw [hsub, card_filter_powersetCard_subset _ _ _ (subset_univ _) (by omega), he2, card_univ]
  simp

end EdgeSet

section Counting

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The triples containing `v` whose other two vertices are neighbours of `v` correspond to
the pairs of neighbours of `v`. -/
private theorem card_filter_erase_subset_neighborFinset (v : V) :
    #{t ∈ (univ : Finset V).powersetCard 3 | v ∈ t ∧ t.erase v ⊆ G.neighborFinset v} =
      (G.degree v).choose 2 := by
  have hv : v ∉ G.neighborFinset v := by simp
  have h : {t ∈ (univ : Finset V).powersetCard 3 | v ∈ t ∧ t.erase v ⊆ G.neighborFinset v} =
      {t ∈ (insert v (G.neighborFinset v)).powersetCard 3 | {v} ⊆ t} := by
    ext t
    simp only [mem_filter, mem_powersetCard, subset_univ, true_and, singleton_subset_iff,
      subset_insert_iff]
    tauto
  rw [h, card_filter_powersetCard_subset _ _ _ (by simp) (by simp), card_insert_of_notMem hv,
    card_neighborFinset_eq_degree]
  simp

/-- In a triple spanning `k` edges, exactly `k.choose 2` vertices are joined to both others. -/
private theorem card_filter_erase_subset_neighborFinset_of_card_eq_three {t : Finset V}
    (ht : #t = 3) :
    #{v ∈ t | t.erase v ⊆ G.neighborFinset v} = (#(G.edgeFinset ∩ t.sym2)).choose 2 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht
  have ea : ({a, b, c} : Finset V).erase a = {b, c} := by ext; simp; grind
  have eb : ({a, b, c} : Finset V).erase b = {a, c} := by ext; simp; grind
  have ec : ({a, b, c} : Finset V).erase c = {a, b} := by ext; simp; grind
  rw [card_edgeFinset_inter_sym2_triple hab hac hbc, card_filter, sum_insert, sum_insert,
    sum_singleton, ea, eb, ec]
  · by_cases h₁ : G.Adj a b <;> by_cases h₂ : G.Adj a c <;> by_cases h₃ : G.Adj b c <;>
      simp [h₁, h₂, h₃, insert_subset_iff, G.adj_comm b a, G.adj_comm c a, G.adj_comm c b]
  · simp [hbc]
  · simp [hab, hac]

/-- Summing `k.choose 2` over all triples, where `k` is the number of edges a triple spans,
gives `∑ v, (G.degree v).choose 2`: both count the pairs of edges that share a vertex. -/
theorem sum_powersetCard_three_card_edgeFinset_inter_sym2_choose_two :
    ∑ t ∈ univ.powersetCard 3, (#(G.edgeFinset ∩ t.sym2)).choose 2 =
      ∑ v, (G.degree v).choose 2 := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset V)) (t := univ.powersetCard 3)
    (r := fun v t ↦ v ∈ t ∧ t.erase v ⊆ G.neighborFinset v)
  simp only [bipartiteAbove, bipartiteBelow, card_filter_erase_subset_neighborFinset] at h
  rw [h]
  refine sum_congr rfl fun t ht ↦ ?_
  rw [← card_filter_erase_subset_neighborFinset_of_card_eq_three G (mem_powersetCard.mp ht).2]
  congr 1
  ext v
  simp

/-- The odd-triple count for a single triple: if it spans `k` edges, then
`[k odd] + 2 * k.choose 2 = k + 4 * [k = 3]`, and `k = 3` exactly when it is a triangle of `G`. -/
private theorem odd_add_two_mul_choose_two_of_card_eq_three {t : Finset V} (ht : #t = 3) :
    (if Odd #(G.edgeFinset ∩ t.sym2) then 1 else 0) + 2 * (#(G.edgeFinset ∩ t.sym2)).choose 2 =
      #(G.edgeFinset ∩ t.sym2) + 4 * (if G.IsNClique 3 t then 1 else 0) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht
  rw [card_edgeFinset_inter_sym2_triple hab hac hbc]
  by_cases h₁ : G.Adj a b <;> by_cases h₂ : G.Adj a c <;> by_cases h₃ : G.Adj b c <;>
    simp [h₁, h₂, h₃, Nat.odd_iff, is3Clique_triple_iff]

/-- **Odd-triple count.** The number of triples spanning an odd number of edges of `G`,
plus twice the number of pairs of edges at a common vertex, is `card V - 2` times the number
of edges plus four times the number of triangles of `G`. -/
theorem card_oddTripleFinset_add_two_mul_sum_degree_choose_two :
    #G.oddTripleFinset + 2 * ∑ v, (G.degree v).choose 2 =
      (Fintype.card V - 2) * #G.edgeFinset + 4 * #(G.cliqueFinset 3) := by
  have hclique : G.cliqueFinset 3 =
      {t ∈ (univ : Finset V).powersetCard 3 | G.IsNClique 3 t} := by
    ext t
    simp only [mem_cliqueFinset_iff, mem_filter, mem_powersetCard, subset_univ, true_and]
    exact ⟨fun h ↦ ⟨h.card_eq, h⟩, And.right⟩
  rw [← sum_powersetCard_three_card_edgeFinset_inter_sym2,
    ← sum_powersetCard_three_card_edgeFinset_inter_sym2_choose_two, hclique, oddTripleFinset_def,
    card_filter, card_filter, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun t ht ↦
    odd_add_two_mul_choose_two_of_card_eq_three G (mem_powersetCard.mp ht).2

variable {G} in
/-- The odd-triple count of a triangle-free graph, for instance a bipartite one. -/
theorem CliqueFree.card_oddTripleFinset_add_two_mul_sum_degree_choose_two
    (hG : G.CliqueFree 3) :
    #G.oddTripleFinset + 2 * ∑ v, (G.degree v).choose 2 =
      (Fintype.card V - 2) * #G.edgeFinset := by
  rw [G.card_oddTripleFinset_add_two_mul_sum_degree_choose_two, hG.cliqueFinset, card_empty,
    mul_zero, add_zero]

/-- **Kozlov's odd-triangle identity**: in a `3`-clique-free finite graph, the number of `3`-vertex
subsets spanning an odd number of edges plus the sum of squared vertex degrees equals
`Fintype.card V * #G.edgeFinset` (Kozlov, arXiv:1610.07136v2, equation (2.5)). -/
theorem card_oddTripleFinset_add_sum_degree_sq (hG : G.CliqueFree 3) :
    #G.oddTripleFinset + ∑ v : V, G.degree v ^ 2 = Fintype.card V * #G.edgeFinset := by
  by_cases hV : Fintype.card V < 2
  · have hodd : #G.oddTripleFinset = 0 := by
      refine card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr fun t ht ↦ ?_)
      have ht3 := (mem_oddTripleFinset.mp ht).1
      have hle : #t ≤ Fintype.card V := card_le_univ t
      omega
    have hsub : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hbot : G = ⊥ := by
      ext u v
      simp [hsub.allEq u v]
    have hedge : #G.edgeFinset = 0 := by
      rw [card_eq_zero, edgeFinset_eq_empty]
      exact hbot
    rw [hodd, hedge, mul_zero, zero_add]
    exact sum_eq_zero fun v _ ↦ by simp [hbot]
  · have hsq (d : ℕ) : d ^ 2 = d + 2 * d.choose 2 := by
      rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self d).two_dvd]
      cases d with
      | zero => simp
      | succ n => simp [sq]; ring
    have hsum_sq : ∑ v : V, G.degree v ^ 2 =
        2 * #G.edgeFinset + 2 * ∑ v : V, (G.degree v).choose 2 := by
      simp_rw [hsq, sum_add_distrib, ← mul_sum, G.sum_degrees_eq_twice_card_edges]
    have hchoose := hG.card_oddTripleFinset_add_two_mul_sum_degree_choose_two
    rw [hsum_sq, ← add_assoc, add_right_comm _ (2 * #G.edgeFinset), hchoose]
    have h2 : 2 ≤ Fintype.card V := by omega
    calc (Fintype.card V - 2) * #G.edgeFinset + 2 * #G.edgeFinset
        = ((Fintype.card V - 2) + 2) * #G.edgeFinset := by ring
      _ = Fintype.card V * #G.edgeFinset := by rw [Nat.sub_add_cancel h2]

/-- Explicit formula for `#G.oddTripleFinset` in a `3`-clique-free finite graph. -/
theorem card_oddTripleFinset_eq_of_cliqueFree (hG : G.CliqueFree 3) :
    #G.oddTripleFinset = Fintype.card V * #G.edgeFinset - ∑ v : V, G.degree v ^ 2 := by
  have h := G.card_oddTripleFinset_add_sum_degree_sq hG
  omega

/-- In a finite graph of maximum degree at most `1`, the number of `3`-vertex subsets spanning an
odd number of edges equals `(Fintype.card V - 2) * #G.edgeFinset`. -/
theorem card_oddTripleFinset_of_degree_le_one [Fintype G.edgeSet] (hdeg : ∀ v, G.degree v ≤ 1) :
    #G.oddTripleFinset = (Fintype.card V - 2) * #G.edgeFinset := by
  have hchoose : ∑ v : V, (G.degree v).choose 2 = 0 :=
    sum_eq_zero fun v _ ↦ Nat.choose_eq_zero_of_lt (Nat.lt_succ_of_le (hdeg v))
  have hcf := G.cliqueFree_add_two_of_degree_le hdeg
  have h := hcf.card_oddTripleFinset_add_two_mul_sum_degree_choose_two
  rw [hchoose, mul_zero, add_zero, G.card_edgeFinset_congr G.fintypeEdgeSet _] at h
  exact h

end Counting

end SimpleGraph
