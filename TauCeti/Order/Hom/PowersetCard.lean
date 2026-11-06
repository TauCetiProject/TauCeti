/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.PowersetCard

import Mathlib.Tactic.FinCases

/-!
# Fixed-cardinality subsets of linear orders

This file collects two enumerations of fixed-cardinality subsets through Mathlib's
`Set.powersetCard.ofFinEmbEquiv`, together with the sum and product formulas for its increasing
enumeration.

In a linear order, a three-element finite set is listed exactly once as an increasing triple
`a < b < c`. `Set.powersetCard.ofLtTriple` is this enumeration, an equivalence between the
increasing triples and `Set.powersetCard I 3`. It is the case `n = 3` of Mathlib's
`Set.powersetCard.ofFinEmbEquiv`, stated for triples so that sums and products over the
increasing triples `{t : I × I × I // t.1 < t.2.1 ∧ t.2.1 < t.2.2}` can be compared with sums over
three-element sets. For instance, a finite linear order with `n` elements has `n.choose 3`
increasing triples.

For `k + p = N`, the indices `k, …, N - 1` of `Fin N` form the `p`-subset `TauCeti.topBlock h`,
built through `Set.powersetCard.ofFinEmbEquiv` from the order embedding `a ↦ k + a`. Its increasing
enumeration is `a ↦ k + a`, an index lies in it exactly when it is at least `k`, and every other
`p`-subset meets the first `k` indices.
-/

public section

open Finset

namespace Set.powersetCard

variable {I : Type*} [LinearOrder I]

/-- A product over the increasing enumeration of a fixed-cardinality subset is the product
over that subset. -/
@[to_additive (attr := simp) /-- Summing over the increasing enumeration of a fixed-cardinality
subset is the same as summing over that subset. -/]
theorem prod_comp_ofFinEmbEquiv_symm {n : ℕ} (s : powersetCard I n)
    {M : Type*} [CommMonoid M] (f : I → M) :
    ∏ a, f (ofFinEmbEquiv.symm s a) = ∏ i ∈ (s : Finset I), f i := by
  -- Both sides enumerate the subset using its order isomorphism with `Fin n`.
  exact (Fintype.prod_equiv (orderIsoOfFin s).toEquiv
    (fun a ↦ f (ofFinEmbEquiv.symm s a)) (fun i ↦ f i.val) fun _ ↦ rfl).trans
    (Finset.prod_coe_sort s.val f)

/-- An increasing triple, as an order embedding of `Fin 3`. -/
private def ltTripleEmb (t : {t : I × I × I // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) : Fin 3 ↪o I :=
  OrderEmbedding.ofStrictMono ![t.1.1, t.1.2.1, t.1.2.2]
    (Fin.strictMono_iff_lt_succ.2 fun m ↦ by fin_cases m; exacts [t.2.1, t.2.2])

private theorem ltTripleEmb_apply (t : {t : I × I × I // t.1 < t.2.1 ∧ t.2.1 < t.2.2})
    (m : Fin 3) : ltTripleEmb t m = ![t.1.1, t.1.2.1, t.1.2.2] m :=
  rfl

/-- The increasing triples `a < b < c` of a linear order enumerate its three-element sets, by
`(a, b, c) ↦ {a, b, c}`. -/
noncomputable def ofLtTriple : {t : I × I × I // t.1 < t.2.1 ∧ t.2.1 < t.2.2} ≃ powersetCard I 3 :=
  { toFun := ltTripleEmb
    invFun e := ⟨(e 0, e 1, e 2), e.strictMono (by decide), e.strictMono (by decide)⟩
    left_inv _ := rfl
    right_inv e := by ext m; fin_cases m <;> rfl : _ ≃ (Fin 3 ↪o I)}.trans ofFinEmbEquiv

private theorem ofLtTriple_apply (t : {t : I × I × I // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) :
    ofLtTriple t = ofFinEmb 3 I (ltTripleEmb t).toEmbedding :=
  rfl

/-- The three-element set enumerated by an increasing triple consists of its three entries. -/
@[simp]
theorem val_ofLtTriple (t : {t : I × I × I // t.1 < t.2.1 ∧ t.2.1 < t.2.2}) :
    (ofLtTriple t).val = {t.1.1, t.1.2.1, t.1.2.2} := by
  ext a
  simp [ofLtTriple_apply, val_ofFinEmb, ltTripleEmb_apply, Fin.exists_fin_succ, eq_comm]

/-- Every three-element set of a linear order is `{a, b, c}` for some `a < b < c`. -/
theorem exists_lt_lt_val_eq (s : powersetCard I 3) :
    ∃ a b c, a < b ∧ b < c ∧ s.val = {a, b, c} := by
  obtain ⟨t, rfl⟩ := ofLtTriple.surjective s
  exact ⟨_, _, _, t.2.1, t.2.2, val_ofLtTriple t⟩

/-- A finite linear order with `n` elements has `n.choose 3` increasing triples. -/
theorem card_lt_triple [Fintype I] :
    Fintype.card {t : I × I × I // t.1 < t.2.1 ∧ t.2.1 < t.2.2} = (Fintype.card I).choose 3 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_congr ofLtTriple, Set.powersetCard.card,
    Nat.card_eq_fintype_card]

end Set.powersetCard

open Set.powersetCard

namespace TauCeti

variable {p N : ℕ}

/-- **The top block** `{k, …, N - 1}` of the indices of `Fin N`, for `k + p = N`, as a
`p`-subset. -/
def topBlock {k : ℕ} (h : k + p = N) : Set.powersetCard (Fin N) p :=
  ofFinEmbEquiv ((Fin.natAddOrderEmb k).trans (Fin.castOrderIso h).toOrderEmbedding)

/-- The `a`-th index of the top block, in increasing order, is `k + a`. -/
@[simp]
theorem val_ofFinEmbEquiv_symm_topBlock {k : ℕ} (h : k + p = N) (a : Fin p) :
    (ofFinEmbEquiv.symm (topBlock h) a : ℕ) = k + a := by
  simp [topBlock]

/-- An index lies in the top block exactly when it is at least `k`. -/
@[simp]
theorem mem_topBlock {k : ℕ} (h : k + p = N) {j : Fin N} : j ∈ topBlock h ↔ k ≤ (j : ℕ) := by
  rw [← mem_range_ofFinEmbEquiv_symm_iff_mem]
  refine ⟨?_, fun hj ↦ ⟨⟨j - k, by omega⟩, Fin.ext ?_⟩⟩
  · rintro ⟨a, rfl⟩
    simp
  · simp only [val_ofFinEmbEquiv_symm_topBlock]
    omega

/-- **A `p`-subset other than the top block meets the first `k` indices.** -/
theorem exists_lt_of_ne_topBlock {k : ℕ} (h : k + p = N) {J : Set.powersetCard (Fin N) p}
    (hJ : J ≠ topBlock h) : ∃ j ∈ J, (j : ℕ) < k := by
  by_contra! hc
  exact hJ (eq_iff_subset.2 fun j hj ↦ (mem_topBlock h).2 (hc j hj))

end TauCeti
