/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Sym2
public import TauCeti.Combinatorics.SimpleGraph.CutMinimal
import Mathlib.Algebra.Order.Group.CompleteLattice
import TauCeti.Order.Hom.PowersetCard

/-!
# Symmetric differences, cuts, and ordered edge enumerations of simple graphs

On a linearly ordered finite vertex type `V`, every edge `e ∈ G.edgeFinset` has a unique strictly
increasing orientation `(e.inf, e.sup)` with `e.inf < e.sup`. This file establishes the algebra of
graph symmetric differences with complete-graph cuts together with the bijections identifying edge
sums, edge counts, cut-toggled edge counts, and odd-edge induced triangles with sums and filters
over strictly increasing tuples.

## Main results

* `SimpleGraph.fromRel_adj_self`, `SimpleGraph.symmDiff_adj`, `SimpleGraph.edgeSet_symmDiff`, and
  `SimpleGraph.edgeFinset_symmDiff`: round-trip `fromRel G.Adj = G` and adjacency, edge sets, and
  edge finsets of the symmetric difference `G₁ ∆ G₂`.
* `SimpleGraph.top_between_compl_adj` and `SimpleGraph.symmDiff_top_between_compl_adj`: adjacency in
  the complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ` and in `G ∆ (⊤ : SimpleGraph V).between
  S Sᶜ` is given unconditionally by `Xor`.
* `SimpleGraph.isCutMinimal_iff_forall_finset`, `SimpleGraph.ciInf_card_symmDiff_edgeFinset_le`, and
  `SimpleGraph.ciInf_card_symmDiff_edgeFinset_eq_iff`: finset-cut and real-infimum characterizations
  of `SimpleGraph.IsCutMinimal`.
* `SimpleGraph.prod_edgeFinset_eq_prod_filter_lt`, `SimpleGraph.sum_edgeFinset_eq_sum_filter_lt`,
  `SimpleGraph.prod_filter_lt_adj_eq_prod_edgeFinset`,
  `SimpleGraph.sum_filter_lt_adj_eq_sum_edgeFinset`,
  `SimpleGraph.card_filter_lt_adj_eq_card_edgeFinset`, and
  `SimpleGraph.card_filter_lt_xor_adj_eq_card_symmDiff_edgeFinset`: products, sums, and
  cardinalities of edges and cut-toggled edges enumerated by strictly increasing pairs `p.1 < p.2`.
* `SimpleGraph.card_filter_edgeFinset_triple_of_lt`,
  `SimpleGraph.odd_card_filter_edgeFinset_triple_iff_of_lt`, and
  `SimpleGraph.card_filter_lt_xor_adj_triple_eq_card_powersetCard_three_odd`: edge count and parity
  of a `3`-element vertex set `{u, v, w}` (`u < v < w`), identifying increasing triples of odd edge
  parity with `3`-element vertex sets spanning an odd number of edges.
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

/-- On a finite vertex type, a graph is cut-minimal if and only if toggling any finset cut does not
decrease its edge count. -/
theorem isCutMinimal_iff_forall_finset [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    G.IsCutMinimal ↔
      ∀ S : Finset V, #G.edgeFinset ≤
        #(G.edgeFinset ∆ ((⊤ : SimpleGraph V).between (S : Set V) (S : Set V)ᶜ).edgeFinset) := by
  rw [isCutMinimal_iff_card_le_card_symmDiff]
  refine ⟨fun h S => h (S : Set V), fun h S _ => ?_⟩
  have heq :
      ((⊤ : SimpleGraph V).between (S.toFinset : Set V) (S.toFinset : Set V)ᶜ).edgeFinset =
        ((⊤ : SimpleGraph V).between S Sᶜ).edgeFinset := by
    ext e
    simp
  simpa only [heq] using h S.toFinset

/-- The infimum of cut-toggled edge counts over all finsets `S : Finset V` never exceeds
`#G.edgeFinset`, since `S = ∅` toggles the empty cut. -/
theorem ciInf_card_symmDiff_edgeFinset_le [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (⨅ S : Finset V,
        (#(G.edgeFinset ∆
          ((⊤ : SimpleGraph V).between (S : Set V) (S : Set V)ᶜ).edgeFinset) : ℝ)) ≤
      #G.edgeFinset := by
  have hbdd : BddBelow (Set.range fun S : Finset V =>
      (#(G.edgeFinset ∆
        ((⊤ : SimpleGraph V).between (S : Set V) (S : Set V)ᶜ).edgeFinset) : ℝ)) :=
    ⟨0, by rintro _ ⟨S, rfl⟩; exact Nat.cast_nonneg _⟩
  refine (ciInf_le hbdd ∅).trans_eq ?_
  have hempty : ((⊤ : SimpleGraph V).between (↑(∅ : Finset V) : Set V)
      (↑(∅ : Finset V) : Set V)ᶜ).edgeFinset = ∅ := by
    ext e
    induction e using Sym2.ind
    simp [between_adj]
  simp [hempty, symmDiff_def]

/-- The infimum of cut-toggled edge counts equals `#G.edgeFinset` if and only if `G` is
cut-minimal. -/
theorem ciInf_card_symmDiff_edgeFinset_eq_iff [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    (⨅ S : Finset V,
        (#(G.edgeFinset ∆
          ((⊤ : SimpleGraph V).between (S : Set V) (S : Set V)ᶜ).edgeFinset) : ℝ)) =
      #G.edgeFinset ↔ G.IsCutMinimal := by
  rw [isCutMinimal_iff_forall_finset]
  have hbdd : BddBelow (Set.range fun S : Finset V =>
      (#(G.edgeFinset ∆
        ((⊤ : SimpleGraph V).between (S : Set V) (S : Set V)ᶜ).edgeFinset) : ℝ)) :=
    ⟨0, by rintro _ ⟨S, rfl⟩; exact Nat.cast_nonneg _⟩
  constructor
  · intro h S
    exact_mod_cast h ▸ ciInf_le hbdd S
  · intro h
    refine le_antisymm G.ciInf_card_symmDiff_edgeFinset_le ?_
    exact le_ciInf fun S => by exact_mod_cast h S

/-! ### Ordered-pair enumerations of edges and induced triangles -/

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

/-- For `u < v < w`, the number of edges of `G` contained in `{u, v, w}` equals the number of
adjacent pairs among `(u, v)`, `(v, w)`, and `(w, u)`. -/
theorem card_filter_edgeFinset_triple_of_lt (G : SimpleGraph V) [DecidableRel G.Adj] {u v w : V}
    (huv : u < v) (hvw : v < w) :
    #{e ∈ G.edgeFinset | e.toFinset ⊆ {u, v, w}} =
      (if G.Adj u v then 1 else 0) + (if G.Adj v w then 1 else 0) +
        (if G.Adj w u then 1 else 0) := by
  have huw : u < w := huv.trans hvw
  rw [card_filter, G.sum_edgeFinset_eq_sum_filter_lt]
  have hmem (p : V × V) :
      s(p.1, p.2).toFinset ⊆ ({u, v, w} : Finset V) ↔
        p.1 ∈ ({u, v, w} : Finset V) ∧ p.2 ∈ ({u, v, w} : Finset V) := by
    simp [subset_iff]
  simp_rw [hmem, ← card_filter, filter_filter]
  have hcomm : ({p : V × V | (p.1 < p.2 ∧ G.Adj p.1 p.2) ∧
        p.1 ∈ ({u, v, w} : Finset V) ∧ p.2 ∈ ({u, v, w} : Finset V)} : Finset (V × V)) =
      {p ∈ ({(u, v), (v, w), (u, w)} : Finset (V × V)) | G.Adj p.1 p.2} := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hab, hadj⟩, ha, hb⟩
      refine ⟨?_, hadj⟩
      rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
      all_goals first | exact (lt_irrefl _ hab).elim | exact (lt_asymm hab ‹_›).elim | tauto
    · rintro ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, hadj⟩
      · exact ⟨⟨huv, hadj⟩, by simp, by simp⟩
      · exact ⟨⟨hvw, hadj⟩, by simp, by simp⟩
      · exact ⟨⟨huw, hadj⟩, by simp, by simp⟩
  rw [hcomm, card_filter]
  have h12 : (u, v) ∉ ({(v, w), (u, w)} : Finset (V × V)) := by
    simp [huv.ne, hvw.ne]
  have h23 : (v, w) ≠ (u, w) := by
    simp [huv.ne']
  rw [sum_insert h12, sum_pair h23]
  simp only [G.adj_comm u w, add_assoc]

/-- For `u < v < w`, the set `{u, v, w}` spans an odd number of edges of `G` if and only if
`Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u))` holds. -/
theorem odd_card_filter_edgeFinset_triple_iff_of_lt (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : u < v) (hvw : v < w) :
    Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ {u, v, w}} ↔
      Xor (G.Adj u v) (Xor (G.Adj v w) (G.Adj w u)) := by
  rw [G.card_filter_edgeFinset_triple_of_lt huv hvw]
  by_cases h₁ : G.Adj u v <;> by_cases h₂ : G.Adj v w <;> by_cases h₃ : G.Adj w u <;>
    simp only [h₁, h₂, h₃, ↓reduceIte] <;> decide

/-- On a finite linear order, strictly increasing triples `(u, v, w)` with odd edge parity around
the triangle correspond bijectively to `3`-element subsets of `V` spanning an odd number of edges
in `G`. -/
theorem card_filter_lt_xor_adj_triple_eq_card_powersetCard_three_odd (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    #{t : V × V × V | t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧
        Xor (G.Adj t.1 t.2.1) (Xor (G.Adj t.2.1 t.2.2) (G.Adj t.2.2 t.1))} =
      #{s ∈ (univ : Finset V).powersetCard 3 |
        Odd #{e ∈ G.edgeFinset | e.toFinset ⊆ s}} := by
  refine card_bij
    (fun t ht =>
      (Set.powersetCard.ofLtTriple ⟨t, (mem_filter.mp ht).2.1, (mem_filter.mp ht).2.2.1⟩).val)
    (fun t ht => ?_) (fun _ _ _ _ heq => ?_) (fun s hs => ?_)
  · obtain ⟨-, h₁, h₂, hxor⟩ := mem_filter.mp ht
    refine mem_filter.mpr ⟨mem_powersetCard_univ.mpr
      (Set.powersetCard.ofLtTriple ⟨t, h₁, h₂⟩).2, ?_⟩
    rw [Set.powersetCard.val_ofLtTriple]
    exact (G.odd_card_filter_edgeFinset_triple_iff_of_lt h₁ h₂).mpr hxor
  · exact congrArg Subtype.val
      (Set.powersetCard.ofLtTriple.injective (Subtype.ext heq))
  · obtain ⟨hs3, hodd⟩ := mem_filter.mp hs
    let u := Set.powersetCard.ofLtTriple.symm ⟨s, mem_powersetCard_univ.mp hs3⟩
    have hval : (Set.powersetCard.ofLtTriple u).val = s :=
      congrArg Subtype.val (Set.powersetCard.ofLtTriple.apply_symm_apply _)
    refine ⟨u.1, mem_filter.mpr ⟨mem_univ _, u.2.1, u.2.2, ?_⟩, hval⟩
    rw [← G.odd_card_filter_edgeFinset_triple_iff_of_lt u.2.1 u.2.2,
      ← Set.powersetCard.val_ofLtTriple u, hval]
    exact hodd

end LinearOrder

end SimpleGraph
