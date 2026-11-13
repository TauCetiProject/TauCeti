/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Sym

/-!
# Triples spanning an odd number of edges

For a graph `G` on a finite vertex type, `G.oddTriangleFinset` is the set of three-element
vertex sets spanning an odd number of edges of `G`. Reading `G` as a binary one-cochain on the
full simplex on its vertices, these are the triangles on which the coboundary is nonzero, so
its cardinality is the size of the coboundary of `G`.

The main result counts these triples by vertex degrees:
`#G.oddTriangleFinset + 2 * ∑ v, (G.degree v).choose 2 = (card V - 2) * #G.edgeFinset +
4 * #(G.cliqueFinset 3)`. It follows from two double counts over all triples: every edge lies
in `card V - 2` triples, and every pair of edges at a common vertex spans exactly one triple.
For a triangle-free graph, such as a bipartite one, the clique term vanishes.

The identity is the general counting step behind the odd-triangle counts of binary cochains
on a simplex in D. N. Kozlov, *The first Cheeger constant of a simplex*, arXiv:1610.07136v2,
cf. (2.5) and Lemma 3.10, where the graphs are bipartite and the clique term is absent.
-/

public section

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The three-element vertex sets spanning an odd number of edges of `G`. -/
def oddTriangleFinset : Finset (Finset V) :=
  {t ∈ univ.powersetCard 3 | Odd #(G.edgeFinset ∩ t.sym2)}

variable {G}

/-- A set of vertices is an odd triangle when it has three elements spanning an odd number of
edges. -/
@[simp]
theorem mem_oddTriangleFinset {t : Finset V} :
    t ∈ G.oddTriangleFinset ↔ #t = 3 ∧ Odd #(G.edgeFinset ∩ t.sym2) := by
  simp [oddTriangleFinset]

/-- The edges spanned by three distinct vertices are counted pair by pair. -/
theorem card_edgeFinset_inter_sym2_triple {a b c : V} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
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

/-- Three distinct vertices span an odd number of edges exactly when an odd number of the
three pairs are adjacent. -/
theorem triple_mem_oddTriangleFinset_iff {a b c : V} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) :
    {a, b, c} ∈ G.oddTriangleFinset ↔ Xor (G.Adj a b) (Xor (G.Adj a c) (G.Adj b c)) := by
  rw [mem_oddTriangleFinset, card_edgeFinset_inter_sym2_triple hab hac hbc]
  have h3 : #({a, b, c} : Finset V) = 3 := card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  by_cases h₁ : G.Adj a b <;> by_cases h₂ : G.Adj a c <;> by_cases h₃ : G.Adj b c <;>
    simp [h₁, h₂, h₃, h3, xor_def, Nat.odd_iff]

variable (G)

/-- Every edge lies in `card V - 2` triples, so the edges spanned by the triples add up to
`card V - 2` times the number of edges. -/
theorem sum_card_edgeFinset_inter_sym2 :
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

/-- The triples containing `v` whose other two vertices are neighbours of `v` correspond to
the pairs of neighbours of `v`. -/
private theorem card_filter_erase_subset_neighborFinset (v : V) :
    #{t ∈ (univ : Finset V).powersetCard 3 | v ∈ t ∧ t.erase v ⊆ G.neighborFinset v} =
      (G.degree v).choose 2 := by
  rw [← card_neighborFinset_eq_degree, ← card_powersetCard]
  have hv : v ∉ G.neighborFinset v := by simp
  apply card_nbij' (fun t => t.erase v) (fun s => insert v s)
  · intro t ht
    simp only [mem_coe, mem_filter, mem_powersetCard, subset_univ, true_and] at ht
    simp only [mem_coe, mem_powersetCard]
    exact ⟨ht.2.2, by rw [card_erase_of_mem ht.2.1, ht.1]⟩
  · intro s hs
    simp only [mem_coe, mem_powersetCard] at hs
    have hvs : v ∉ s := fun h => hv (hs.1 h)
    simp [card_insert_of_notMem hvs, hs.2, erase_insert hvs, hs.1]
  · intro t ht
    exact insert_erase (mem_filter.mp (mem_coe.mp ht)).2.1
  · intro s hs
    exact erase_insert fun h => hv ((mem_powersetCard.mp (mem_coe.mp hs)).1 h)

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

/-- The two edges at a vertex of degree `d` can be chosen in `d.choose 2` ways, and each such
pair spans a unique triple, which contains exactly `(#(G.edgeFinset ∩ t.sym2)).choose 2`
such pairs. -/
theorem sum_card_edgeFinset_inter_sym2_choose_two :
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

/-- The odd-triangle count for a single triple: if it spans `k` edges, then
`[k odd] + 2 * k.choose 2 = k + 4 * [k = 3]`, and `k = 3` exactly when it is a triangle of `G`. -/
private theorem odd_add_two_mul_choose_two_of_card_eq_three {t : Finset V} (ht : #t = 3) :
    (if Odd #(G.edgeFinset ∩ t.sym2) then 1 else 0) + 2 * (#(G.edgeFinset ∩ t.sym2)).choose 2 =
      #(G.edgeFinset ∩ t.sym2) + 4 * (if G.IsNClique 3 t then 1 else 0) := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp ht
  rw [card_edgeFinset_inter_sym2_triple hab hac hbc]
  by_cases h₁ : G.Adj a b <;> by_cases h₂ : G.Adj a c <;> by_cases h₃ : G.Adj b c <;>
    simp [h₁, h₂, h₃, Nat.odd_iff, is3Clique_triple_iff]

/-- **Odd-triangle count.** The number of triples spanning an odd number of edges of `G`,
plus twice the number of pairs of edges at a common vertex, is `card V - 2` times the number
of edges plus four times the number of triangles of `G`. -/
theorem card_oddTriangleFinset_add_two_mul_sum_degree_choose_two :
    #G.oddTriangleFinset + 2 * ∑ v, (G.degree v).choose 2 =
      (Fintype.card V - 2) * #G.edgeFinset + 4 * #(G.cliqueFinset 3) := by
  have hclique : G.cliqueFinset 3 =
      {t ∈ (univ : Finset V).powersetCard 3 | G.IsNClique 3 t} := by
    ext t
    simp only [mem_cliqueFinset_iff, mem_filter, mem_powersetCard, subset_univ, true_and]
    exact ⟨fun h => ⟨h.card_eq, h⟩, And.right⟩
  rw [← sum_card_edgeFinset_inter_sym2, ← sum_card_edgeFinset_inter_sym2_choose_two, hclique,
    oddTriangleFinset, card_filter, card_filter, mul_sum, mul_sum, ← sum_add_distrib,
    ← sum_add_distrib]
  exact sum_congr rfl fun t ht =>
    odd_add_two_mul_choose_two_of_card_eq_three G (mem_powersetCard.mp ht).2

/-- The odd-triangle count of a triangle-free graph, for instance a bipartite one. -/
theorem CliqueFree.card_oddTriangleFinset_add_two_mul_sum_degree_choose_two
    (hG : G.CliqueFree 3) :
    #G.oddTriangleFinset + 2 * ∑ v, (G.degree v).choose 2 =
      (Fintype.card V - 2) * #G.edgeFinset := by
  rw [G.card_oddTriangleFinset_add_two_mul_sum_degree_choose_two, hG.cliqueFinset, card_empty,
    mul_zero, add_zero]

end SimpleGraph
