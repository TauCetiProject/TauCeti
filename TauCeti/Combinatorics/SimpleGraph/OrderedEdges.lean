/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Sym2
public import TauCeti.Combinatorics.SimpleGraph.Bipartite

/-!
# Symmetric differences, cuts, and ordered edge enumerations of simple graphs

On a linearly ordered finite vertex type `V`, every edge `e ∈ G.edgeFinset` has a unique strictly
increasing orientation `(e.inf, e.sup)` with `e.inf < e.sup`. This file establishes the algebra of
graph symmetric differences with complete-graph cuts together with the bijections identifying edge
sums, edge counts, and cut-toggled edge counts with sums and filters over strictly increasing pairs.

## Main results

* `SimpleGraph.fromRel_adj_self`, `SimpleGraph.fromRel_ite_ne_one`, `SimpleGraph.symmDiff_adj`,
  `SimpleGraph.edgeSet_symmDiff`, and `SimpleGraph.edgeFinset_symmDiff`: round-trips
  `fromRel G.Adj = G` and `fromRel (fun u v => (if G.Adj u v then t else 1) ≠ 1) = G`, and
  adjacency, edge sets, and edge finsets of the symmetric difference `G₁ ∆ G₂`.
* `SimpleGraph.top_between_compl_adj` and `SimpleGraph.symmDiff_top_between_compl_adj`: adjacency in
  the complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ` and in `G ∆ (⊤ : SimpleGraph V).between
  S Sᶜ` is given unconditionally by `Xor`.
* `SimpleGraph.prod_edgeFinset_eq_prod_filter_lt`, `SimpleGraph.sum_edgeFinset_eq_sum_filter_lt`,
  `SimpleGraph.prod_filter_lt_adj_eq_prod_edgeFinset`,
  `SimpleGraph.sum_filter_lt_adj_eq_sum_edgeFinset`,
  `SimpleGraph.card_filter_lt_adj_eq_card_edgeFinset`, and
  `SimpleGraph.card_filter_lt_xor_adj_eq_card_symmDiff_edgeFinset`: products, sums, and
  cardinalities of edges and cut-toggled edges enumerated by strictly increasing pairs `p.1 < p.2`.
-/

public section

open Finset
open scoped symmDiff

namespace SimpleGraph

variable {V : Type*}

/-! ### Symmetric differences and complete-graph cuts -/

/-- Constructing a simple graph via `SimpleGraph.fromRel` from its own adjacency relation recovers
the graph. -/
@[simp]
theorem fromRel_adj_self (G : SimpleGraph V) : fromRel G.Adj = G := by
  ext u v
  exact ⟨fun ⟨_, h⟩ => h.elim id (G.adj_comm v u).mp, fun h => ⟨G.ne_of_adj h, Or.inl h⟩⟩

/-- Recovering a simple graph from its `{1, t}` edge indicator (`t ≠ 1`) returns the original
graph. -/
theorem fromRel_ite_ne_one {M : Type*} [One M] (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : M} (ht : t ≠ 1) :
    fromRel (fun u v => (if G.Adj u v then t else 1) ≠ 1) = G := by
  simp [ht]

/-- Two vertices are adjacent in `G₁ ∆ G₂` if and only if they are adjacent in exactly one of `G₁`
and `G₂`. -/
@[simp]
theorem symmDiff_adj (G₁ G₂ : SimpleGraph V) (u v : V) :
    (G₁ ∆ G₂).Adj u v ↔ Xor (G₁.Adj u v) (G₂.Adj u v) := by
  simp only [symmDiff_def, sup_adj, sdiff_adj, Xor]

/-- The edge set of `G₁ ∆ G₂` is the symmetric difference of their edge sets. -/
@[simp]
theorem edgeSet_symmDiff (G₁ G₂ : SimpleGraph V) :
    (G₁ ∆ G₂).edgeSet = G₁.edgeSet ∆ G₂.edgeSet := by
  simp only [symmDiff_def, edgeSet_sup, edgeSet_sdiff]

/-- The edge finset of `G₁ ∆ G₂` is the symmetric difference of their edge finsets. -/
@[simp]
theorem edgeFinset_symmDiff {G₁ G₂ : SimpleGraph V} [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]
    [Fintype (edgeSet (G₁ ∆ G₂))] [DecidableEq V] :
    (G₁ ∆ G₂).edgeFinset = G₁.edgeFinset ∆ G₂.edgeFinset := by
  ext e
  simp only [mem_edgeFinset, edgeSet_symmDiff, Finset.mem_symmDiff, Set.mem_symmDiff]

/-- Two vertices are adjacent in the complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ` if and
only if exactly one of them belongs to `S`. -/
@[simp]
theorem top_between_compl_adj (S : Set V) {u v : V} :
    ((⊤ : SimpleGraph V).between S Sᶜ).Adj u v ↔ Xor (u ∈ S) (v ∈ S) := by
  rw [between_adj, top_adj, Set.mem_compl_iff, Set.mem_compl_iff, Xor]
  refine ⟨?_, fun h => ⟨by rintro rfl; tauto, ?_⟩⟩ <;> tauto

/-- Adjacency in `G` after toggling the cut `(⊤ : SimpleGraph V).between S Sᶜ` is given by `Xor`.
-/
theorem symmDiff_top_between_compl_adj (G : SimpleGraph V) (S : Set V) {u v : V} :
    (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).Adj u v ↔
      Xor (G.Adj u v) (Xor (u ∈ S) (v ∈ S)) := by
  rw [symmDiff_adj, top_between_compl_adj]

/-! ### Ordered-pair enumerations of edges -/

section LinearOrder

variable [Fintype V] [LinearOrder V]

/-- Multiplying a function of unordered edges over `G.edgeFinset` is multiplying over the strictly
increasing adjacent pairs `p.1 < p.2`. -/
@[to_additive /-- Summing a function of unordered edges over `G.edgeFinset` is summing over the
strictly increasing adjacent pairs `p.1 < p.2`. -/]
theorem prod_edgeFinset_eq_prod_filter_lt {M : Type*} [CommMonoid M] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : Sym2 V → M) :
    ∏ e ∈ G.edgeFinset, f e = ∏ p : V × V with p.1 < p.2 ∧ G.Adj p.1 p.2, f s(p.1, p.2) := by
  refine prod_nbij' (fun e => (e.inf, e.sup)) (fun p => s(p.1, p.2))
    (fun e he => ?_) (fun p hp => ?_) (fun e _ => ?_) (fun p hp => ?_) (fun e _ => ?_)
  · simp only [mem_edgeFinset] at he
    simp only [mem_filter, mem_univ, true_and]
    induction e using Sym2.ind with | _ a b =>
    rcases lt_trichotomy a b with hab | rfl | hba
    · simp [inf_eq_left.mpr hab.le, sup_eq_right.mpr hab.le, hab, G.mem_edgeSet.mp he]
    · exact (G.loopless.irrefl a (G.mem_edgeSet.mp he)).elim
    · simp [inf_eq_right.mpr hba.le, sup_eq_left.mpr hba.le, hba, (G.mem_edgeSet.mp he).symm]
  · simp only [mem_filter, mem_univ, true_and] at hp
    exact mem_edgeFinset.mpr (G.mem_edgeSet.mpr hp.2)
  · exact Sym2.sortEquiv.left_inv e
  · simp only [mem_filter, mem_univ, true_and] at hp
    exact Prod.ext (inf_eq_left.mpr hp.1.le) (sup_eq_right.mpr hp.1.le)
  · exact congrArg f (Sym2.sortEquiv.left_inv e).symm

/-- Multiplying a binary vertex function over the strictly increasing adjacent pairs `p.1 < p.2` is
multiplying `f e.inf e.sup` over `G.edgeFinset`. -/
@[to_additive /-- Summing a binary vertex function over the strictly increasing adjacent pairs
`p.1 < p.2` is summing `f e.inf e.sup` over `G.edgeFinset`. -/]
theorem prod_filter_lt_adj_eq_prod_edgeFinset {M : Type*} [CommMonoid M] (G : SimpleGraph V)
    [DecidableRel G.Adj] (f : V → V → M) :
    (∏ p : V × V with p.1 < p.2 ∧ G.Adj p.1 p.2, f p.1 p.2) =
      ∏ e ∈ G.edgeFinset, f e.inf e.sup := by
  rw [G.prod_edgeFinset_eq_prod_filter_lt fun e => f e.inf e.sup]
  refine prod_congr rfl fun p hp => ?_
  have hlt : p.1 < p.2 := (mem_filter.mp hp).2.1
  simp [inf_eq_left.mpr hlt.le, sup_eq_right.mpr hlt.le]

/-- On a finite linear order, the number of strictly increasing adjacent pairs equals
`#G.edgeFinset`. -/
theorem card_filter_lt_adj_eq_card_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] :
    #{p : V × V | p.1 < p.2 ∧ G.Adj p.1 p.2} = #G.edgeFinset := by
  simpa using (G.sum_edgeFinset_eq_sum_filter_lt fun _ => (1 : ℕ)).symm

/-- On a finite linear order, the number of strictly increasing pairs whose adjacency in `G`
differs from membership across `S` equals the size of `G.edgeFinset ∆ ((⊤ : SimpleGraph V).between
S Sᶜ).edgeFinset`. -/
theorem card_filter_lt_xor_adj_eq_card_symmDiff_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] :
    #{p : V × V | p.1 < p.2 ∧ Xor (G.Adj p.1 p.2) (Xor (p.1 ∈ S) (p.2 ∈ S))} =
      #(G.edgeFinset ∆ ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset) := by
  let H : SimpleGraph V := G ∆ (⊤ : SimpleGraph V).between S Sᶜ
  have : DecidableRel H.Adj := Classical.decRel H.Adj
  have hfilter : #{p : V × V | p.1 < p.2 ∧ Xor (G.Adj p.1 p.2) (Xor (p.1 ∈ S) (p.2 ∈ S))} =
      #{p : V × V | p.1 < p.2 ∧ H.Adj p.1 p.2} := by
    refine congrArg card (ext fun p => ?_)
    simp [H, G.symmDiff_top_between_compl_adj S]
  rw [hfilter, H.card_filter_lt_adj_eq_card_edgeFinset, edgeFinset_symmDiff]

end LinearOrder

end SimpleGraph
