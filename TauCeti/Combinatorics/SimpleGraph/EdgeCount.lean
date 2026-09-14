/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.Data.Set.Card

/-!
# Alternating edge-count signs over an interval of graphs

For a finite vertex type the graphs on it form a finite Boolean algebra, graded by the number of
edges.  This file records how the sign `(-1) ^ (number of edges)` behaves on that lattice: it is
multiplicative along the grading, and it sums to zero over any interval `[F, K]` with more than one
element.  That vanishing is the Möbius function of the graph lattice, and it is what makes the
inclusion-exclusion transform of a function of graphs invertible.

## Main results

* `SimpleGraph.card_edgeSet_mono` — the edge count is monotone in the graph;
* `SimpleGraph.neg_one_pow_card_edgeSet_sub` — for `F ≤ G` the sign of the edge-count difference is
  the product of the two signs;
* `SimpleGraph.sum_neg_one_pow_card_edgeSet` — the signs cancel over the interval `[F, K]` unless
  `F = K`.

## Implementation

Edges are counted by `Nat.card` of the edge set rather than by the cardinality of
`SimpleGraph.edgeFinset`, so that no `Fintype` instance on the edge set of each summand has to be
manufactured; finiteness of the vertex type is all that is assumed.

Mathlib's `IncidenceAlgebra.mu` is not what is computed here: it needs a `LocallyFiniteOrder`
instance, which `SimpleGraph V` does not carry, and identifying it with the sign below would in any
case require the same cancellation.

The interval `[F, K]` is in bijection with the powerset of the edges of `K` missing from `F`, which
would reduce the cancellation to `Finset.sum_powerset_neg_one_pow_card`.  Setting up that bijection
costs more than the direct argument used here: pairing each graph in the interval with the graph
obtained by toggling one fixed edge of `K` absent from `F` is a fixed-point-free involution of the
interval that flips the sign.
-/

public section

open scoped symmDiff

namespace SimpleGraph

variable {V : Type*} {F G K : SimpleGraph V} {u v : V} {R : Type*} [Ring R]

/-- The number of edges of a graph on a finite vertex type is monotone in the graph. -/
theorem card_edgeSet_mono [Finite V] (h : F ≤ G) :
    Nat.card F.edgeSet ≤ Nat.card G.edgeSet := by
  simp only [Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard (edgeSet_mono h) (Set.toFinite _)

/-- Adding an absent edge increases the edge count by one.  This is the `Nat.card` reading of
Mathlib's `SimpleGraph.card_edgeFinset_sup_edge`, which needs a `Fintype` instance on the edge set
of the enlarged graph. -/
private theorem card_edgeSet_sup_edge [Finite V] (hn : ¬G.Adj u v) (huv : u ≠ v) :
    Nat.card (G ⊔ edge u v).edgeSet = Nat.card G.edgeSet + 1 := by
  have hset : (G ⊔ edge u v).edgeSet = insert s(u, v) G.edgeSet := by
    rw [edgeSet_sup, edgeSet_edge_of_ne huv, Set.union_comm, Set.insert_eq]
  rw [hset]
  simp only [Nat.card_coe_set_eq]
  exact Set.ncard_insert_of_notMem (by simpa using hn) (Set.toFinite _)

/-- Toggling an edge that `F` does not have keeps a supergraph of `F` a supergraph of `F`. -/
private theorem le_symmDiff_edge (hFuv : ¬F.Adj u v) (hFG : F ≤ G) : F ≤ G ∆ edge u v := by
  rw [symmDiff_eq_sup_sdiff_inf, le_sdiff]
  exact ⟨le_sup_of_le_left hFG, ((disjoint_edge F).2 hFuv).mono_right inf_le_right⟩

/-- Toggling one edge changes the parity of the edge count, hence flips the sign
`(-1) ^ (edge count)`. -/
private theorem neg_one_pow_card_edgeSet_symmDiff_edge [Finite V] (huv : u ≠ v) :
    (-1 : R) ^ Nat.card (G ∆ edge u v).edgeSet = -(-1 : R) ^ Nat.card G.edgeSet := by
  rcases em (G.Adj u v) with hadj | hadj
  · have hle : edge u v ≤ G := (edge_le_iff G).2 (Or.inr hadj)
    have hsup : (G ∆ edge u v) ⊔ edge u v = G := by
      rw [symmDiff_of_ge hle]; exact sdiff_sup_cancel hle
    have hnadj : ¬(G ∆ edge u v).Adj u v := by
      rw [symmDiff_of_ge hle, sdiff_adj, not_and_not_right]
      exact fun _ => by simp [edge_adj, huv]
    have hcard : Nat.card G.edgeSet = Nat.card (G ∆ edge u v).edgeSet + 1 := by
      conv_lhs => rw [← hsup]
      exact card_edgeSet_sup_edge hnadj huv
    rw [hcard, pow_succ, mul_neg_one, neg_neg]
  · rw [((disjoint_edge G).2 hadj).symmDiff_eq_sup, card_edgeSet_sup_edge hadj huv, pow_succ,
      mul_neg_one]

/-- For nested graphs the sign of the difference of the edge counts is the product of the two
signs. -/
theorem neg_one_pow_card_edgeSet_sub [Finite V] (h : F ≤ G) :
    (-1 : R) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet)
      = (-1 : R) ^ Nat.card G.edgeSet * (-1 : R) ^ Nat.card F.edgeSet := by
  have hle := card_edgeSet_mono h
  rw [← pow_add]
  have hsplit : Nat.card G.edgeSet + Nat.card F.edgeSet
      = Nat.card G.edgeSet - Nat.card F.edgeSet + 2 * Nat.card F.edgeSet := by omega
  rw [hsplit, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

variable [Fintype V] [DecidableEq V]

open scoped Classical in
/-- The cancellation, in the case where the interval has more than one element. -/
private theorem sum_neg_one_pow_card_edgeSet_of_ne (hne : F ≠ K) :
    ∑ G ∈ Finset.univ.filter fun G : SimpleGraph V => F ≤ G ∧ G ≤ K,
        (-1 : R) ^ Nat.card G.edgeSet = 0 := by
  by_cases hFK : F ≤ K
  · obtain ⟨u, v, hKuv, hFuv⟩ : ∃ u v, K.Adj u v ∧ ¬F.Adj u v := by
      by_contra hc
      refine hne (le_antisymm hFK fun a b hab => ?_)
      by_contra hFab
      exact hc ⟨a, b, hab, hFab⟩
    have huv : u ≠ v := hKuv.ne
    have hedge : (edge u v).Adj u v := by simp [edge_adj, huv]
    refine Finset.sum_involution (fun G _ => G ∆ edge u v)
      (fun a _ => by rw [neg_one_pow_card_edgeSet_symmDiff_edge huv, add_neg_cancel])
      (fun a _ _ => ?_) (fun a ha => ?_) (fun a _ => symmDiff_symmDiff_cancel_right _ a)
    · rw [Ne, symmDiff_eq_left]
      exact fun h => by simp [h] at hedge
    · obtain ⟨hFa, haK⟩ := (Finset.mem_filter.1 ha).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, le_symmDiff_edge hFuv hFa,
        symmDiff_le_sup.trans (sup_le haK ((edge_le_iff K).2 (Or.inr hKuv)))⟩
  · have hempty : (Finset.univ.filter fun G : SimpleGraph V => F ≤ G ∧ G ≤ K) = ∅ := by
      ext G
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
        not_and]
      exact fun h1 h2 => hFK (h1.trans h2)
    rw [hempty, Finset.sum_empty]

open scoped Classical in
/-- **The Möbius function of the lattice of graphs.**  Summed over the graphs between `F` and `K`,
the signs `(-1) ^ (number of edges)` cancel unless the interval is a single point. -/
theorem sum_neg_one_pow_card_edgeSet (F K : SimpleGraph V) :
    ∑ G ∈ Finset.univ.filter fun G : SimpleGraph V => F ≤ G ∧ G ≤ K,
        (-1 : R) ^ Nat.card G.edgeSet = if F = K then (-1 : R) ^ Nat.card F.edgeSet else 0 := by
  rcases eq_or_ne F K with rfl | hne
  · have hsingle : (Finset.univ.filter fun G : SimpleGraph V => F ≤ G ∧ G ≤ F) = {F} := by
      ext G
      simp [le_antisymm_iff, and_comm]
    simp [hsingle]
  · rw [sum_neg_one_pow_card_edgeSet_of_ne hne]
    simp [hne]

end SimpleGraph
