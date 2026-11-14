/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Hom.PowersetCard
public import TauCeti.Data.Set.PowersetCard

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FinCases
import TauCeti.Data.Finset.Sort
import TauCeti.GroupTheory.Perm.Inversion

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

The shuffle of two disjoint fixed-cardinality subsets lists the increasing enumeration of the first
followed by that of the second, and mapping along an order embedding or order isomorphism commutes
with increasing enumerations and preserves shuffle signs. The shuffle of a singleton `{i}` with
`s.erase i` lists `i` first and then `s.erase i`, and in the presentation `Fin (n + 1)` it is the
inverse cycle moving the position of `i` in `s` to the front. For an `r`-subset `T` of `Fin m`, the
shuffle sorting `T` followed by its complement `Tᶜ` has sign
`(-1) ^ (∑ i ∈ T, i - r * (r - 1) / 2)`, so the product of the shuffle signs of two `r`-subsets
`S` and `T` is `(-1) ^ (∑ i ∈ S, i + ∑ j ∈ T, j)`.
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
    (fun a ↦ f (ofFinEmbEquiv.symm s a)) (fun i ↦ f i.val) (fun a ↦ by
      rw [ofFinEmbEquiv_symm_apply]
      exact congrArg f (Finset.coe_orderIsoOfFin_apply s.1 s.2 a).symm)).trans
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
  have hremove : k.removeNth (fun j ↦ e j) = (s.erase i).orderEmbOfFin hn :=
    Finset.removeNth_orderEmbOfFin_symm_eq i s hi hsCard hn
  have hdval : (Set.powersetCard.disjUnion hdisj).val = s := by
    simp [hi]
  let p : Equiv.Perm (Fin (1 + n)) := Set.powersetCard.permOfDisjoint hdisj
  let c : Fin (1 + n) ≃ Fin (n + 1) := finCongr (Nat.add_comm 1 n)
  have hec : ∀ q : Fin (1 + n), e (c q) =
      (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop q := by
    intro q
    have key : ∀ (V : Finset I) (_ : V = s) (pf : V.card = 1 + n),
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

/-- The unique increasing enumeration of `Set.powersetCard.ofSingleton a` is constant at `a`. -/
@[simp]
theorem ofFinEmbEquiv_symm_ofSingleton (a : I) (i : Fin 1) :
    ofFinEmbEquiv.symm (ofSingleton a) i = a :=
  _root_.Finset.orderEmbOfFin_singleton a i

/-- The increasing enumeration of a two-element subset `{a, b}` with `a < b` is `![a, b]`. -/
theorem coe_ofFinEmbEquiv_symm_pair {s : powersetCard I 2} {a b : I} (hab : a < b)
    (hs : s.val = {a, b}) : ⇑(ofFinEmbEquiv.symm s) = ![a, b] := by
  rw [ofFinEmbEquiv_symm_apply]
  exact (_root_.Finset.orderEmbOfFin_unique s.prop
    (fun x ↦ by fin_cases x <;> simp [hs])
    (Fin.strictMono_iff_lt_succ.mpr fun x ↦ by fin_cases x; exact hab)).symm

/-- Mapping a fixed-cardinality subset along an order embedding composes its increasing
enumeration with that order embedding. -/
@[simp]
theorem ofFinEmbEquiv_symm_map_orderEmbedding {J : Type*} [LinearOrder J] {n : ℕ}
    (e : I ↪o J) (s : powersetCard I n) :
    ofFinEmbEquiv.symm (map n e.toEmbedding s) = (ofFinEmbEquiv.symm s).trans e := by
  apply ofFinEmbEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  have hs : Subtype.val (ofFinEmbEquiv (ofFinEmbEquiv.symm s)) = s.val :=
    congrArg Subtype.val (ofFinEmbEquiv.apply_symm_apply s)
  rw [ofFinEmbEquiv_apply, val_ofFinEmb, val_map, ← hs, ofFinEmbEquiv_apply, val_ofFinEmb,
    _root_.Finset.map_map]
  rfl

/-- An order isomorphism preserves the shuffle sign of a fixed-cardinality subset. -/
@[simp]
theorem sign_map_orderIso {J : Type*} [LinearOrder J] [Fintype I] [Fintype J] {n : ℕ}
    (e : I ≃o J) (s : powersetCard I n) :
    powersetCard.sign (map n e.toEmbedding s) = powersetCard.sign s := by
  have hm := sub_add_eq_card s
  have hmn : n + (Fintype.card I - n) = Fintype.card I := Nat.add_comm _ n ▸ hm
  have hmn' : n + (Fintype.card I - n) = Fintype.card J :=
    hmn.trans (Fintype.card_congr e.toEquiv)
  let t := compl hm s
  have hst : Disjoint s.val t.val := disjoint_compl_right
  have hst' : Disjoint (map n e.toEmbedding s).val
      (map (Fintype.card I - n) e.toEmbedding t).val := by
    rw [show e.toEmbedding = e.toEquiv.toEmbedding from rfl, map_compl_equiv hm e.toEquiv]
    exact disjoint_compl_right
  have hunion : disjUnion hst' =
      map (n + (Fintype.card I - n)) e.toOrderEmbedding.toEmbedding (disjUnion hst) := by
    refine eq_iff_subset.mpr fun x hx ↦ ?_
    obtain ⟨a, rfl⟩ := e.surjective x
    simpa [show e.toOrderEmbedding.toEmbedding = e.toEmbedding from rfl] using hx
  rw [sign_eq_permOfDisjoint_sign hmn s t hst, sign_eq_permOfDisjoint_sign hmn' _ _ hst']
  congr 1
  apply Equiv.ext
  intro j
  apply (ofFinEmbEquiv.symm (disjUnion hst')).injective
  have hlhs := orderEmbOfFin_permOfDisjoint (map n e.toEmbedding s)
    (map (Fintype.card I - n) e.toEmbedding t) hst' j
  have hrhs := congrArg e (orderEmbOfFin_permOfDisjoint s t hst j)
  simp only [← ofFinEmbEquiv_symm_apply] at hlhs hrhs
  refine hlhs.trans ?_
  rw [hunion, ofFinEmbEquiv_symm_map_orderEmbedding, RelEmbedding.trans_apply,
    OrderIso.coe_toOrderEmbedding, hrhs]
  rcases finSumFinEquiv.symm j with a | b <;>
    simp [show e.toEmbedding = e.toOrderEmbedding.toEmbedding from rfl]

section Fin

variable {m r : ℕ}

/-- The increasing enumeration of `{i}ᶜ` inside `Fin (n + 1)` is `i.succAboveOrderEmb`. -/
@[simp]
theorem ofFinEmbEquiv_symm_compl_ofSingleton {n : ℕ}
    (hk : n + 1 = Fintype.card (Fin (n + 1))) (i : Fin (n + 1)) :
    ofFinEmbEquiv.symm (compl hk (ofSingleton i)) = i.succAboveOrderEmb := by
  simp [ofFinEmbEquiv_symm_apply]

/-- The sum of the elements of an `r`-subset of `Fin m`, as natural numbers, is at least
`r * (r - 1) / 2`. -/
theorem mul_pred_div_two_le_sum_fin (T : powersetCard (Fin m) r) :
    r * (r - 1) / 2 ≤ ∑ i ∈ (T : _root_.Finset (Fin m)), (i : ℕ) := by
  rw [← sum_comp_ofFinEmbEquiv_symm T (fun i : Fin m ↦ (i : ℕ)), ← _root_.Finset.sum_range_id,
    ← Fin.sum_univ_eq_sum_range]
  exact _root_.Finset.sum_le_sum fun a _ ↦ T.val.val_le_val_orderEmbOfFin T.prop a

/-- The shuffle sign of an `r`-subset `T` of `Fin m`, written without natural-number subtraction as
`(-1) ^ (∑ i ∈ T, i + r * (r - 1) / 2)`. -/
theorem sign_fin_eq_neg_one_pow_add (T : powersetCard (Fin m) r) :
    powersetCard.sign T =
      (-1 : ℤˣ) ^ (∑ i ∈ (T : _root_.Finset (Fin m)), (i : ℕ) + r * (r - 1) / 2) := by
  have hr : r + (m - r) = m := Nat.add_sub_of_le (le_of_fin T)
  let T' := compl (sub_add_eq_card_fin T) T
  have hdisj : Disjoint T.val T'.val := disjoint_compl_right
  have huniv : (disjUnion hdisj).val = _root_.Finset.univ := by
    simp [T']
  let p : Equiv.Perm (Fin (r + (m - r))) := permOfDisjoint hdisj
  let c : Fin (r + (m - r)) ≃ Fin m := finCongr hr
  -- The increasing enumeration of `univ` is `finCongr hr`.
  have hcMono : StrictMono c := fun _ _ hxy ↦ hxy
  have hunivEmb : ⇑((disjUnion hdisj).val.orderEmbOfFin (disjUnion hdisj).prop) = c :=
    (_root_.Finset.orderEmbOfFin_unique (disjUnion hdisj).prop
      (fun q ↦ huniv.symm ▸ _root_.Finset.mem_univ (c q)) hcMono).symm
  -- Read through `finSumFinEquiv` and `finCongr hr`, `p` lists `T` followed by `T'`.
  let e : Fin r ⊕ Fin (m - r) ≃ Fin m := finSumFinEquiv.trans (p.trans c)
  have he (z : Fin r ⊕ Fin (m - r)) :
      e z = Sum.elim (ofFinEmbEquiv.symm T) (ofFinEmbEquiv.symm T') z := by
    have hperm := orderEmbOfFin_permOfDisjoint T T' hdisj (finSumFinEquiv z)
    have hfun := congrFun hunivEmb (p (finSumFinEquiv z))
    rw [hfun, Equiv.symm_apply_apply] at hperm
    simpa [e, p, ofFinEmbEquiv_symm_apply] using hperm
  have hconj : (finSumFinEquiv.trans c).symm.trans e = c.permCongr p := by
    ext x
    simp [e]
  have hsign := TauCeti.sign_shuffle hr e
    (by simpa [Function.comp_def, he] using (ofFinEmbEquiv.symm T).strictMono)
    (by simpa [Function.comp_def, he] using (ofFinEmbEquiv.symm T').strictMono)
  rw [hconj, Equiv.Perm.sign_permCongr] at hsign
  rw [sign_eq_permOfDisjoint_sign (by simp [hr]) T T' hdisj, hsign]
  congr 1
  simp only [he, Sum.elim_inl, sum_comp_ofFinEmbEquiv_symm T (fun i : Fin m ↦ (i : ℕ)),
    Fin.sum_univ_eq_sum_range (fun a : ℕ ↦ a), _root_.Finset.sum_range_id]

/-- For an `r`-subset `T` of `Fin m`, the shuffle sign `Set.powersetCard.sign T` is
`(-1) ^ (∑ i ∈ T, i - r * (r - 1) / 2)`. -/
theorem sign_fin (T : powersetCard (Fin m) r) :
    powersetCard.sign T =
      (-1 : ℤˣ) ^ (∑ i ∈ (T : _root_.Finset (Fin m)), (i : ℕ) - r * (r - 1) / 2) := by
  have hle := mul_pred_div_two_le_sum_fin T
  have hadd : ∑ i ∈ (T : _root_.Finset (Fin m)), (i : ℕ) + r * (r - 1) / 2 =
      (∑ i ∈ (T : _root_.Finset (Fin m)), (i : ℕ) - r * (r - 1) / 2) + 2 * (r * (r - 1) / 2) := by
    omega
  rw [sign_fin_eq_neg_one_pow_add T, hadd, pow_add, pow_mul]
  simp

/-- **The sign of the complement shuffle.** For an `r`-subset `T` of `Fin m`, the shuffle
`Set.powersetCard.permOfDisjoint` sorting `T` followed by `Tᶜ` has sign
`(-1) ^ (∑ i ∈ T, i - r * (r - 1) / 2)`. -/
theorem sign_permOfDisjoint_compl {k : ℕ} (hk : k + r = Fintype.card (Fin m))
    (T : powersetCard (Fin m) r)
    (hdisj : Disjoint T.val (compl hk T).val := disjoint_compl_right) :
    (permOfDisjoint hdisj).sign =
      (-1 : ℤˣ) ^ (∑ i ∈ (T : _root_.Finset (Fin m)), (i : ℕ) - r * (r - 1) / 2) := by
  rw [← sign_eq_permOfDisjoint_sign (Nat.add_comm k r ▸ hk) T (compl hk T) hdisj, sign_fin]

/-- The shuffle signs of two `r`-subsets `S` and `T` of `Fin m` multiply to
`(-1) ^ (∑ i ∈ S, i + ∑ j ∈ T, j)`. -/
theorem sign_mul_sign_fin (S T : powersetCard (Fin m) r) :
    powersetCard.sign S * powersetCard.sign T =
      (-1 : ℤˣ) ^ (∑ i ∈ (S : _root_.Finset (Fin m)), (i : ℕ) +
        ∑ j ∈ (T : _root_.Finset (Fin m)), (j : ℕ)) := by
  have hsum : (∑ i ∈ (S : _root_.Finset (Fin m)), (i : ℕ) + r * (r - 1) / 2) +
      (∑ j ∈ (T : _root_.Finset (Fin m)), (j : ℕ) + r * (r - 1) / 2) =
      (∑ i ∈ (S : _root_.Finset (Fin m)), (i : ℕ) + ∑ j ∈ (T : _root_.Finset (Fin m)), (j : ℕ)) +
        2 * (r * (r - 1) / 2) := by
    ring
  rw [sign_fin_eq_neg_one_pow_add S, sign_fin_eq_neg_one_pow_add T, ← pow_add, hsum,
    pow_add, pow_mul]
  simp

end Fin

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
