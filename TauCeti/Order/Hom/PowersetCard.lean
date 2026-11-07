/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.PowersetCard

import Mathlib.Tactic.FinCases
import TauCeti.Data.Finset.Sort

/-!
# Fixed-cardinality subsets of linear orders

This file collects two enumerations of fixed-cardinality subsets through Mathlib's
`Set.powersetCard.ofFinEmbEquiv`.

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

The shuffle of two disjoint fixed-cardinality subsets lists the increasing enumeration of the first
followed by that of the second. The shuffle of a singleton `{i}` with `s.erase i` lists `i` first
and then `s.erase i`, and in the presentation `Fin (n + 1)` it is the inverse cycle moving the
position of `i` in `s` to the front.
-/

public section

open Finset

namespace Set.powersetCard

variable {I : Type*} [LinearOrder I]

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

/-- The shuffle of two disjoint fixed-cardinality subsets `u` and `t` lists the increasing
enumeration of `u`, followed by the increasing enumeration of `t`, inside the increasing
enumeration of their union. -/
theorem orderEmbOfFin_permOfDisjoint {m n : ℕ} (u : powersetCard I m) (t : powersetCard I n)
    (hdisj : Disjoint u.val t.val) (j : Fin (m + n)) :
    (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin (Set.powersetCard.disjUnion hdisj).prop
      (Set.powersetCard.permOfDisjoint hdisj j) =
    Sum.elim (u.val.orderEmbOfFin u.prop) (t.val.orderEmbOfFin t.prop) (finSumFinEquiv.symm j) := by
  have hx : (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
      (Set.powersetCard.disjUnion hdisj).prop (Set.powersetCard.permOfDisjoint hdisj j) =
      Equiv.Finset.disjUnionEquiv u.val t.val hdisj
        (((Set.powersetCard.orderIsoOfFin u).sumCongr
          (Set.powersetCard.orderIsoOfFin t)) (finSumFinEquiv.symm j)) :=
    congrArg Subtype.val ((Set.powersetCard.orderIsoOfFin
      (Set.powersetCard.disjUnion hdisj)).apply_symm_apply _)
  rw [hx]
  generalize finSumFinEquiv.symm j = z
  rcases z with a | b
  · rw [Sum.elim_inl]
    exact (congrArg Subtype.val (Equiv.Finset.disjUnionEquiv_inl _ _)).trans rfl
  · rw [Sum.elim_inr]
    exact (congrArg Subtype.val (Equiv.Finset.disjUnionEquiv_inr _ _)).trans rfl

/-- The shuffle of the singleton `{i}` and `s.erase i` places `i` first, followed by the
increasing enumeration of `s.erase i`. -/
theorem orderEmbOfFin_permOfDisjoint_singleton_erase (i : I) (s : Finset I) {n : ℕ}
    (hn : (s.erase i).card = n)
    (hdisj : Disjoint (⟨{i}, Finset.card_singleton i⟩ : Set.powersetCard I 1).val
      (⟨s.erase i, hn⟩ : Set.powersetCard I n).val) (j : Fin (n + 1)) :
    (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin (Set.powersetCard.disjUnion hdisj).prop
      (Set.powersetCard.permOfDisjoint hdisj ((finCongr (Nat.add_comm 1 n)).symm j)) =
    (Fin.cons i ((s.erase i).orderEmbOfFin hn) : Fin (n + 1) → I) j := by
  rw [orderEmbOfFin_permOfDisjoint]
  cases j using Fin.cases with
  | zero =>
      have hzero : finSumFinEquiv.symm ((finCongr (Nat.add_comm 1 n)).symm 0) =
          Sum.inl (0 : Fin 1) := by
        apply finSumFinEquiv.injective
        apply Fin.ext
        rfl
      rw [hzero, Fin.cons_zero, Sum.elim_inl]
      -- The unique increasing enumeration of a singleton is constant at its element.
      exact Finset.orderEmbOfFin_singleton i 0
  | succ q =>
      have hsucc : finSumFinEquiv.symm ((finCongr (Nat.add_comm 1 n)).symm q.succ) =
          Sum.inr q := by
        apply finSumFinEquiv.injective
        rw [finSumFinEquiv.apply_symm_apply]
        apply Fin.ext
        simp
        omega
      rw [hsucc, Fin.cons_succ, Sum.elim_inr]

/-- The shuffle of the singleton `{i}` and `s.erase i`, in the presentation `Fin (n + 1)`, is the
inverse cycle moving the position of `i` in the increasing enumeration of `s` to the front. -/
theorem conj_permOfDisjoint_singleton_erase (i : I) (s : Finset I) (hi : i ∈ s) {n : ℕ}
    (hn : (s.erase i).card = n) (hsCard : s.card = n + 1)
    (hdisj : Disjoint (⟨{i}, Finset.card_singleton i⟩ : Set.powersetCard I 1).val
      (⟨s.erase i, hn⟩ : Set.powersetCard I n).val) :
    (finCongr (Nat.add_comm 1 n)).symm.trans
      ((Set.powersetCard.permOfDisjoint hdisj).trans (finCongr (Nat.add_comm 1 n))) =
    ((s.orderIsoOfFin hsCard).symm ⟨i, hi⟩).cycleRange.symm := by
  classical
  let e : Fin (n + 1) ↪o I := s.orderEmbOfFin hsCard
  let k : Fin (n + 1) := (s.orderIsoOfFin hsCard).symm ⟨i, hi⟩
  have hek : e k = i :=
    congrArg Subtype.val ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨i, hi⟩)
  have hremove : k.removeNth (fun j ↦ e j) = (s.erase i).orderEmbOfFin hn := by
    subst hn
    exact Finset.removeNth_orderEmbOfFin_symm_eq i s hi hsCard
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I n := ⟨s.erase i, hn⟩
  have hdval : (Set.powersetCard.disjUnion hdisj).val = s := by
    simp [hi]
  let p : Equiv.Perm (Fin (1 + n)) := Set.powersetCard.permOfDisjoint hdisj
  let c : Fin (1 + n) ≃ Fin (n + 1) := finCongr (Nat.add_comm 1 n)
  have hec : ∀ q : Fin (1 + n), e (c q) =
      (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop q := by
    intro q
    have key : ∀ (V : Finset I) (hV : V = s) (pf : V.card = 1 + n),
        s.orderEmbOfFin hsCard (c q) = V.orderEmbOfFin pf q := by
      rintro V rfl pf
      exact Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr (by simp [c])
    exact key _ hdval _
  apply Equiv.ext
  intro j
  apply e.injective
  -- Unfold the conjugated shuffle so both sides are compared in the increasing enumeration.
  change e (c (p (c.symm j))) = e (k.cycleRange.symm j)
  have hrhs : e (k.cycleRange.symm j) =
      (Fin.cons (e k) (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j := by
    simpa only [Function.comp_apply] using
      congrFun (Fin.cons_removeNth_eq_comp_cycleRange_symm e k) j |>.symm
  rw [hrhs, hek]
  -- The disjoint-union permutation enumerates the singleton first and the erased set second.
  change e (c (p (c.symm j))) =
    (Fin.cons i (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j
  rw [hremove]
  rw [hec]
  exact orderEmbOfFin_permOfDisjoint_singleton_erase i s hn hdisj j

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
