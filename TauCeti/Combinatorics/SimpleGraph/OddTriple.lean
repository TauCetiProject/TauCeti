/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Combinatorics.SimpleGraph.SymmDiff
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Sym
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.SimpleGraph.Degree
import TauCeti.Combinatorics.SimpleGraph.Finite
import TauCeti.Order.Hom.PowersetCard

/-!
# Triples spanning an odd number of edges

For a graph `G` on a finite vertex type, `G.oddTripleFinset` is the set of three-element
vertex sets spanning an odd number of edges of `G`. Reading `G` as a binary one-cochain on the
full simplex on its vertices, these are the two-dimensional faces of the simplex on which the
coboundary is nonzero, so its cardinality is the size of the coboundary of `G`. They need not
be triangles of `G` in the sense of `G.cliqueFinset 3`: a triple spanning a single edge is odd.
On a linearly ordered vertex type,
`SimpleGraph.card_filter_lt_xor_adj_triple_eq_card_powersetCard_three_odd` and
`SimpleGraph.card_oddTripleFinset_eq_card_filter_lt` identify these three-element sets bijectively
with the strictly increasing triples `(u, v, w)` satisfying
`Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u))`.

The main results count these triples by vertex degrees and establish cut-switching invariance:
`#G.oddTripleFinset + 2 * ∑ v, (G.degree v).choose 2 = (card V - 2) * #G.edgeFinset +
4 * #(G.cliqueFinset 3)`, `#G.oddTripleFinset + ∑ v, G.degree v ^ 2 = card V * #G.edgeFinset` for
triangle-free graphs (Kozlov, equation (2.5)), `#G.oddTripleFinset = (card V - 2) * #G.edgeFinset`
when every vertex has degree at most `1`, and
`(G ∆ (⊤ : SimpleGraph V).between S Sᶜ).oddTripleFinset = G.oddTripleFinset`.

The identity is the general counting step behind the odd-triangle counts of binary cochains
on a simplex in D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136v2,
cf. (2.5) and Lemma 3.10, where the graphs are bipartite and the clique term is absent.
-/

public section

open Finset
open scoped symmDiff

namespace SimpleGraph

section DecidableEq

variable {V : Type*} [DecidableEq V]

section EdgeSet

variable {G : SimpleGraph V} [Fintype G.edgeSet]

/-- The edges spanned by three distinct vertices are counted pair by pair. -/
theorem card_edgeFinset_inter_sym2_triple [DecidableRel G.Adj] {a b c : V} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    #(G.edgeFinset ∩ ({a, b, c} : Finset V).sym2) =
      (if G.Adj a b then 1 else 0) + (if G.Adj a c then 1 else 0) +
        (if G.Adj b c then 1 else 0) := by
  have h : G.edgeFinset ∩ ({a, b, c} : Finset V).sym2 =
      ({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V)).filter (· ∈ G.edgeSet) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [mem_inter, mem_edgeFinset, mem_sym2_iff, Sym2.mem_iff, mem_filter,
        mem_insert, mem_singleton, mem_edgeSet, Sym2.eq_iff]
      constructor
      · rintro ⟨hxy, hx⟩
        have hx' := hx x (Or.inl rfl)
        have hy' := hx y (Or.inr rfl)
        refine ⟨?_, hxy⟩
        rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;> simp_all
      · grind
  rw [h, card_filter, sum_insert, sum_insert, sum_singleton]
  · simp [add_assoc]
  · simp [hab, hbc.symm]
  · simp [hbc, hab.symm, hac]

variable [Fintype V]

variable (G) in
/-- Every edge lies in `card V - 2` triples, so the edges spanned by the triples add up to
`card V - 2` times the number of edges. -/
theorem sum_powersetCard_three_card_edgeFinset_inter_sym2 :
    ∑ t ∈ univ.powersetCard 3, #(G.edgeFinset ∩ t.sym2) =
      (Fintype.card V - 2) * #G.edgeFinset := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := univ.powersetCard 3) (t := G.edgeFinset) (r := fun t e => e ∈ t.sym2)
  simp only [bipartiteAbove, bipartiteBelow, filter_mem_eq_inter] at h
  rw [h, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun e he => ?_
  have he2 : #e.toFinset = 2 :=
    Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp he))
  have hsub : {t ∈ (univ : Finset V).powersetCard 3 | e ∈ t.sym2} =
      {t ∈ (univ : Finset V).powersetCard 3 | e.toFinset ⊆ t} := by
    ext t
    simp [mem_sym2_iff, subset_iff]
  rw [hsub, card_filter_powersetCard_subset _ _ _ (subset_univ _) (by omega), he2, card_univ]
  simp

end EdgeSet

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The three-element vertex sets spanning an odd number of edges of `G`. -/
def oddTripleFinset : Finset (Finset V) :=
  {t ∈ univ.powersetCard 3 | Odd #(G.edgeFinset ∩ t.sym2)}

/-- Characterization of `G.oddTripleFinset` as the `3`-element subsets of `univ` spanning an odd
number of edges of `G`. -/
theorem oddTripleFinset_def :
    G.oddTripleFinset = {t ∈ (univ : Finset V).powersetCard 3 | Odd #(G.edgeFinset ∩ t.sym2)} :=
  (rfl)

variable {G}

/-- A set of vertices is an odd triple when it has three elements spanning an odd number of
edges. -/
@[simp, grind =]
theorem mem_oddTripleFinset {t : Finset V} :
    t ∈ G.oddTripleFinset ↔ #t = 3 ∧ Odd #(G.edgeFinset ∩ t.sym2) := by
  simp [oddTripleFinset]

/-- Three vertices span an odd number of edges exactly when an odd number of the three pairs
are adjacent. If two of the vertices coincide, both sides are false. -/
@[simp 1100, grind =]
theorem triple_mem_oddTripleFinset_iff {a b c : V} :
    {a, b, c} ∈ G.oddTripleFinset ↔ Xor (G.Adj a b) (Xor (G.Adj a c) (G.Adj b c)) := by
  by_cases h : a ≠ b ∧ a ≠ c ∧ b ≠ c
  · obtain ⟨hab, hac, hbc⟩ := h
    rw [mem_oddTripleFinset, card_edgeFinset_inter_sym2_triple hab hac hbc]
    have h3 : #({a, b, c} : Finset V) = 3 := card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
    by_cases h₁ : G.Adj a b <;> by_cases h₂ : G.Adj a c <;> by_cases h₃ : G.Adj b c <;>
      simp [h₁, h₂, h₃, h3, xor_def, Nat.odd_iff]
  · simp only [not_and_or, not_not] at h
    have hlt : #({a, b, c} : Finset V) < 3 := by
      rcases h with rfl | rfl | rfl
      · rw [card_insert_of_mem (by simp)]
        exact card_le_two.trans_lt (by omega)
      · rw [card_insert_of_mem (by simp)]
        exact card_le_two.trans_lt (by omega)
      · rw [insert_eq_of_mem (mem_singleton_self b)]
        exact card_le_two.trans_lt (by omega)
    rw [mem_oddTripleFinset, iff_false_intro fun h3 : _ ∧ _ => hlt.ne h3.1]
    rcases h with rfl | rfl | rfl <;> simp [G.adj_comm, xor_def]

/-- Cyclic-orientation form of `SimpleGraph.triple_mem_oddTripleFinset_iff`: three vertices span an
odd number of edges iff an odd number of the cyclic pairs `(a, b)`, `(b, c)`, and `(c, a)` are
adjacent. -/
theorem triple_mem_oddTripleFinset_iff_cyclic {a b c : V} :
    {a, b, c} ∈ G.oddTripleFinset ↔ Xor (G.Adj a b) (Xor (G.Adj b c) (G.Adj c a)) := by
  rw [triple_mem_oddTripleFinset_iff, G.adj_comm a c, xor_comm (G.Adj c a)]

/-- Membership in `G.oddTripleFinset` in terms of the induced subgraph on `s`. -/
theorem mem_oddTripleFinset_iff_induce {s : Finset V} :
    s ∈ G.oddTripleFinset ↔ #s = 3 ∧ Odd #(G.induce (s : Set V)).edgeFinset := by
  rw [mem_oddTripleFinset, ← filter_edgeFinset_toFinset_subset,
    card_filter_edgeFinset_toFinset_subset]

/-- The empty graph has no odd triples. -/
@[simp]
theorem oddTripleFinset_bot : (⊥ : SimpleGraph V).oddTripleFinset = ∅ := by
  ext s
  simp only [mem_oddTripleFinset, notMem_empty, iff_false, not_and, Nat.not_odd_iff_even]
  intro _
  rw [card_eq_zero.mpr (by ext; simp)]
  simp

/-- In a `3`-clique-free graph, a vertex subset belongs to `G.oddTripleFinset` iff it has
`3` vertices and spans a single edge of `G`. -/
theorem mem_oddTripleFinset_iff_of_cliqueFree (hG : G.CliqueFree 3) {s : Finset V} :
    s ∈ G.oddTripleFinset ↔ #s = 3 ∧ #(G.edgeFinset ∩ s.sym2) = 1 := by
  rw [mem_oddTripleFinset]
  refine and_congr_right fun hs3 ↦ ⟨fun hodd ↦ ?_, fun h1 ↦ h1 ▸ odd_one⟩
  obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.mp hs3
  have hsub := G.edgeFinset_inter_sym2_triple_subset a b c
  have hcard_pairs : #({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V)) ≤ 3 :=
    (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))
  have hle3 : #(G.edgeFinset ∩ ({a, b, c} : Finset V).sym2) ≤ 3 :=
    (card_le_card hsub).trans hcard_pairs
  obtain ⟨k, hk⟩ := hodd
  have hk1 : k ≤ 1 := by omega
  rcases Nat.eq_or_lt_of_le hk1 with rfl | hk0
  · exfalso
    have heq := eq_of_subset_of_card_le hsub (hk ▸ hcard_pairs)
    have mem_of (e : Sym2 V) (he : e ∈ ({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 V))) :
        e ∈ G.edgeSet := by
      rw [← mem_edgeFinset]
      exact (mem_inter.mp (heq ▸ he)).1
    exact hG {a, b, c} (is3Clique_triple_iff.mpr
      ⟨mem_of s(a, b) (by simp), mem_of s(a, c) (by simp), mem_of s(b, c) (by simp)⟩)
  · omega

/-- Switching a finite graph by a complete-graph cut preserves `oddTripleFinset`. -/
@[simp]
theorem oddTripleFinset_symmDiff_top_between (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] :
    (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).oddTripleFinset = G.oddTripleFinset := by
  ext s
  by_cases hs : #s = 3
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.mp hs
    simp only [triple_mem_oddTripleFinset_iff_cyclic]
    exact G.xor_symmDiff_top_between_compl_adj S a b c
  · simp [mem_oddTripleFinset, hs]

variable (G)

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
    (r := fun v t => v ∈ t ∧ t.erase v ⊆ G.neighborFinset v)
  simp only [bipartiteAbove, bipartiteBelow, card_filter_erase_subset_neighborFinset] at h
  rw [h]
  refine sum_congr rfl fun t ht => ?_
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
    exact ⟨fun h => ⟨h.card_eq, h⟩, And.right⟩
  rw [← sum_powersetCard_three_card_edgeFinset_inter_sym2,
    ← sum_powersetCard_three_card_edgeFinset_inter_sym2_choose_two, hclique, oddTripleFinset,
    card_filter, card_filter, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun t ht =>
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
      | succ n => rw [Nat.succ_sub_one]; ring
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

end DecidableEq

section Iso

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- Graph isomorphisms transport `oddTripleFinset` by mapping each `3`-element vertex subset. -/
theorem Iso.map_oddTripleFinset (f : G ≃g H) :
    G.oddTripleFinset.map (mapEmbedding f.toEquiv.toEmbedding).toEmbedding =
      H.oddTripleFinset := by
  have hmap : G.map f.toEquiv.toEmbedding = H := by
    ext u v
    obtain ⟨x, rfl⟩ := f.surjective u
    obtain ⟨y, rfl⟩ := f.surjective v
    rw [map_adj]
    simp [f.apply_eq_iff_eq, f.map_adj_iff]
  have hedge : H.edgeFinset = G.edgeFinset.map f.toEquiv.toEmbedding.sym2Map := by
    rw [← edgeFinset_inj.mpr hmap, edgeFinset_map]
  have hcard (s : Finset V) :
      #(H.edgeFinset ∩ (s.map f.toEquiv.toEmbedding).sym2) = #(G.edgeFinset ∩ s.sym2) := by
    rw [hedge, sym2_map, ← map_inter, card_map]
  have huniv : (univ : Finset V).map f.toEquiv.toEmbedding = univ := by
    ext w
    obtain ⟨x, rfl⟩ := f.surjective w
    simp
  ext t
  simp only [oddTripleFinset, mem_map, mem_filter, mem_powersetCard, subset_univ, true_and,
    RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
  constructor
  · rintro ⟨s, ⟨hs3, hodd⟩, rfl⟩
    rwa [card_map, and_iff_right hs3, hcard]
  · rintro ⟨ht3, hodd⟩
    have htsub : t ∈ ((univ : Finset V).map f.toEquiv.toEmbedding).powersetCard 3 := by
      rw [huniv, mem_powersetCard]
      exact ⟨subset_univ _, ht3⟩
    rw [powersetCard_map, mem_map] at htsub
    obtain ⟨s, hs, rfl⟩ := htsub
    rw [mem_powersetCard] at hs
    rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, hcard] at hodd
    exact ⟨s, ⟨hs.2, hodd⟩, by rw [RelEmbedding.coe_toEmbedding, mapEmbedding_apply]⟩

/-- Isomorphic finite graphs have the same number of odd triples. -/
theorem Iso.card_oddTripleFinset_eq (f : G ≃g H) :
    #G.oddTripleFinset = #H.oddTripleFinset := by
  rw [← f.map_oddTripleFinset, card_map]

end Iso

section LinearOrder

variable {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- On a finite linear order, strictly increasing triples `(u, v, w)` with odd edge parity around
the triangle correspond bijectively to `3`-element subsets of `V` spanning an odd number of edges
in `G`. -/
theorem card_filter_lt_xor_adj_triple_eq_card_powersetCard_three_odd :
    #{t : V × V × V | t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
        Xor (G.Adj t.1 t.2.1) (Xor (G.Adj t.2.1 t.2.2) (G.Adj t.2.2 t.1))} =
      #{s ∈ (univ : Finset V).powersetCard 3 |
        Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s}} := by
  have hfinset : {s ∈ (univ : Finset V).powersetCard 3 |
      Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s}} = G.oddTripleFinset := by
    simp only [oddTripleFinset, filter_edgeFinset_toFinset_subset]
  rw [hfinset]
  refine card_bij
    (fun t ht =>
      (Set.powersetCard.ofLtTriple ⟨t, (mem_filter.mp ht).2.1, (mem_filter.mp ht).2.2.1⟩).val)
    (fun t ht => ?_) (fun _ _ _ _ heq => ?_) (fun s hs => ?_)
  · obtain ⟨-, h₁, h₂, hxor⟩ := mem_filter.mp ht
    rw [Set.powersetCard.val_ofLtTriple, triple_mem_oddTripleFinset_iff,
      xor_comm (G.Adj t.1 t.2.2), G.adj_comm t.1 t.2.2]
    exact hxor
  · exact congrArg Subtype.val
      (Set.powersetCard.ofLtTriple.injective (Subtype.ext heq))
  · let u := Set.powersetCard.ofLtTriple.symm ⟨s, (mem_oddTripleFinset.mp hs).1⟩
    have hval : (Set.powersetCard.ofLtTriple u).val = s :=
      congrArg Subtype.val (Set.powersetCard.ofLtTriple.apply_symm_apply _)
    refine ⟨u.val, mem_filter.mpr ⟨mem_univ _, u.property.1, u.property.2, ?_⟩, hval⟩
    have hmem : (Set.powersetCard.ofLtTriple u).val ∈ G.oddTripleFinset := hval.symm ▸ hs
    rwa [Set.powersetCard.val_ofLtTriple, triple_mem_oddTripleFinset_iff,
      xor_comm (G.Adj u.val.1 u.val.2.2), G.adj_comm u.val.1 u.val.2.2] at hmem

/-- On a finite linearly ordered vertex type, `#G.oddTripleFinset` counts the strictly increasing
vertex triples `(u, v, w)` around which an odd number of pairs are adjacent in `G`. -/
theorem card_oddTripleFinset_eq_card_filter_lt :
    #G.oddTripleFinset =
      #{p : V × V × V | p.1 < p.2.1 ∧ p.2.1 < p.2.2 ∧
        Xor (G.Adj p.1 p.2.1) (Xor (G.Adj p.2.1 p.2.2) (G.Adj p.2.2 p.1))} := by
  rw [← Set.powersetCard.card_filter_lt_triple_eq_card_of_card_eq_three G.oddTripleFinset
    fun _ ht ↦ (mem_oddTripleFinset.mp ht).1]
  simp only [triple_mem_oddTripleFinset_iff_cyclic]

/-- Over a linear order, the odd triples are counted by their increasing triples `u < v < w`:
each odd triple is `{u, v, w}` for exactly one such triple. -/
theorem card_oddTripleFinset_eq_sum :
    #G.oddTripleFinset = ∑ u : V, ∑ v : V, ∑ w : V,
      if u < v ∧ v < w ∧ Xor (G.Adj u v) (Xor (G.Adj u w) (G.Adj v w)) then 1 else 0 := by
  rw [card_oddTripleFinset_eq_card_filter_lt, card_filter]
  simp_rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ ↦ sum_congr rfl fun v _ ↦ sum_congr rfl fun w _ ↦ ?_
  simp only [G.adj_comm w u, xor_comm (G.Adj v w)]

end LinearOrder

end SimpleGraph
