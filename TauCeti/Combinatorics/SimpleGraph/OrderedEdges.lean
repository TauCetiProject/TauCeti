/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Order.Sym2
import TauCeti.Combinatorics.SimpleGraph.Bipartite
import TauCeti.Combinatorics.SimpleGraph.Finite

/-!
# Ordered edge enumerations of simple graphs

On a linearly ordered finite vertex type `V`, every edge `e ∈ G.edgeFinset` has a unique strictly
increasing orientation `(e.inf, e.sup)` with `e.inf < e.sup`. This file establishes the bijections
identifying edge products, sums, counts, and cut-toggled edge counts with products, sums, and
filters over strictly increasing vertex pairs.

## Main results

* `SimpleGraph.prod_edgeFinset_eq_prod_filter_lt`, `SimpleGraph.sum_edgeFinset_eq_sum_filter_lt`,
  `SimpleGraph.prod_filter_lt_adj_eq_prod_edgeFinset`,
  `SimpleGraph.sum_filter_lt_adj_eq_sum_edgeFinset`: products and sums of unordered or oriented edge
  weights enumerated by strictly increasing adjacent pairs `p.1 < p.2`.
* `SimpleGraph.card_filter_lt_adj_eq_card_edgeFinset` and
  `SimpleGraph.card_filter_lt_xor_adj_eq_card_symmDiff_edgeFinset`: cardinalities of edges and
  cut-toggled edges enumerated by strictly increasing pairs `p.1 < p.2`.
-/

public section

open Finset
open scoped symmDiff

namespace SimpleGraph

variable {V : Type*} [Fintype V] [LinearOrder V]

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

end SimpleGraph
