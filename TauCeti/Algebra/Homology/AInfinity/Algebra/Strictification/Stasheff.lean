/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.CohomologicalUnit
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Gauge
public import TauCeti.LinearAlgebra.TensorCoalgebra.Degenerate

/-!
# The Stasheff identity on duplicated-unit words

Let `𝒜` be a minimal `A∞` algebra with cohomological unit `e`, and suppose the suspended Taylor map
of `𝒜` already vanishes on every word of length `k ≠ 2` with `k ≤ m + 2` containing `e`, as well as
on every `(m + 3)`-letter word carrying `e` in a slot strictly before `j`.

Given an `(m + 3)`-tuple `w` with `w j = e`, duplicating `e` at slot `j` produces an `(m + 4)`-tuple
`duplicateAt e j w` carrying two adjacent copies of `e` at positions `j` and `j + 1`.  In the
Stasheff identity `0 = m(b(duplicateAt e j w))`:
* unary and top collapses vanish by minimality;
* collapses of non-binary blocks of length at most `m + 2` vanish by the lower-arity hypothesis,
  because one of the two copies of `e` either lies inside the block or survives outside it;
* binary collapses strictly before `j - 1` leave `e` at slot `j - 1 < j` and vanish by the slot
  induction hypothesis, while the binary collapses at `j - 1` and `j` cancel in pairs (leaving
  `m(w)` when `j = 0`, which cancels the tail `(m + 3)`-collapse `m₂(e, m(w))`).

Only the initial `(m + 3)`-collapse and the binary collapses from `j + 1` onward remain
(`IsMinimal.taylor_barDifferential_duplicateAt`).  At `j = m + 2` there are no binary collapses
after `j`, so this forces `𝒜.taylor` to vanish automatically when `e` sits in the final slot of
arity `m + 3` (`IsMinimal.taylor_of_tprod_last_eq_zero`), and for `j < m + 2` it matches the
Hochschild coboundary of the unit-killing cochain in
`TauCeti.Algebra.Homology.AInfinity.Algebra.Strictification.UnitKilling`.

## Main definitions

* `TauCeti.AInfinityAlgebra.duplicateAt`: replaces `z j` by two adjacent copies of `e` at positions
  `j` and `j + 1`.

## Main results

* `TauCeti.AInfinityAlgebra.IsMinimal.taylor_barDifferential_duplicateAt`: reduced Stasheff
  identity on `duplicateAt e j w`.
* `TauCeti.AInfinityAlgebra.IsMinimal.taylor_of_tprod_last_eq_zero`: automatic vanishing of `e` in
  the final slot of arity `m + 3` once the first `m + 2` slots vanish.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1, 3.3, and 3.6.
* K. Lefèvre-Hasegawa, *Sur les `A∞`-catégories*, Ph.D. thesis, Université Paris 7 (2003),
  Chapter 3, Section 3.2.
* P. Seidel, *Fukaya Categories and Picard--Lefschetz Theory*, Zurich Lectures in Advanced
  Mathematics (2008), Chapter I, Section 2.
-/

public section

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

universe uR uA

section DuplicateAt

variable {R : Type uR} {A : Type uA}

/-- Replace `z j` in an `L`-tuple `z` by two adjacent copies of `e` at positions `j` and `j + 1`. -/
def duplicateAt (e : A) {L : ℕ} (j : Fin L) (z : Fin L → A) : Fin (L + 1) → A :=
  j.succ.insertNth e (Function.update z j e)

/-- Explicit definition of `duplicateAt` via `Fin.insertNth` and `Function.update`. -/
theorem duplicateAt_def (e : A) {L : ℕ} (j : Fin L) (z : Fin L → A) :
    duplicateAt e j z = j.succ.insertNth e (Function.update z j e) := by
  rfl

/-- Coordinate formula for `duplicateAt`: indices `< j` are unchanged, indices `j` and `j + 1` equal
`e`, and indices `> j + 1` shift down by `1`. -/
theorem duplicateAt_apply (e : A) {L : ℕ} (j : Fin L) (z : Fin L → A) (k : Fin (L + 1)) :
    duplicateAt e j z k =
      if hk : k.1 < j.1 then z ⟨k.1, by omega⟩
      else if k.1 = j.1 ∨ k.1 = j.1 + 1 then e
      else z ⟨k.1 - 1, by omega⟩ := by
  rw [duplicateAt]
  cases k using Fin.succAboveCases j.succ with
  | x => simp
  | p r =>
    rw [Fin.insertNth_apply_succAbove]
    rcases lt_trichotomy r.1 j.1 with hlt | heq | hgt
    · have hne : r ≠ j := fun h ↦ Nat.ne_of_lt hlt (congrArg Fin.val h)
      have hsa : j.succ.succAbove r = r.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 (by simp; omega))
      rw [Function.update_of_ne hne, hsa]
      simp [hlt]
    · have hrj : r = j := Fin.ext heq
      subst hrj
      have hsa : r.succ.succAbove r = r.castSucc :=
        Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.2 (by simp))
      rw [Function.update_self, hsa]
      simp
    · have hne : r ≠ j := fun h ↦ Nat.ne_of_gt hgt (congrArg Fin.val h)
      have hsa : j.succ.succAbove r = r.succ :=
        Fin.succAbove_of_le_castSucc _ _ (Fin.le_def.2 (by simp; omega))
      rw [Function.update_of_ne hne, hsa, dite_eq_right (by rw [Fin.val_succ]; omega),
        ite_eq_right (by rw [Fin.val_succ]; omega)]
      exact congrArg z (Fin.ext (by simp))

/-- Sum of `duplicateAt (-1) j 𝒟` when `𝒟 j = -1`: replacing one `-1` by two `-1`s decreases the
total degree by `1`. -/
theorem sum_duplicateAt_neg_one {L : ℕ} (j : Fin L) {𝒟 : Fin L → ℤ} (h𝒟j : 𝒟 j = -1) :
    ∑ k : Fin (L + 1), duplicateAt (-1 : ℤ) j 𝒟 k = (∑ r : Fin L, 𝒟 r) - 1 := by
  rw [duplicateAt, Fin.sum_univ_succAbove _ j.succ, Fin.insertNth_apply_same]
  simp only [Fin.insertNth_apply_succAbove]
  rw [Finset.sum_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.add_sum_erase Finset.univ 𝒟 (Finset.mem_univ j)
  omega

variable [CommRing R] [AddCommGroup A] [Module R A]

/-- If `z` has degrees `𝒟` and `e ∈ G.piece (-1)`, then `duplicateAt e j z` has degrees
`duplicateAt (-1) j 𝒟`. -/
theorem duplicateAt_mem_piece {G : InternalGrading R A ℤ} {e : A} (he : e ∈ G.piece (-1))
    {L : ℕ} (j : Fin L) {z : Fin L → A} {𝒟 : Fin L → ℤ} (hz : ∀ r, z r ∈ G.piece (𝒟 r))
    (k : Fin (L + 1)) : duplicateAt e j z k ∈ G.piece (duplicateAt (-1 : ℤ) j 𝒟 k) := by
  rw [duplicateAt_apply, duplicateAt_apply]
  split_ifs
  · exact hz _
  · exact he
  · exact hz _

private theorem sum_duplicateAt_range_le {m : ℕ} (j : Fin (m + 3)) (𝒟 : Fin (m + 3) → ℤ) {p : ℕ}
    (hp : p ≤ j.1) :
    (∑ r ∈ Finset.range p, if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) =
      ∑ r ∈ Finset.range p, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0 :=
  Finset.sum_congr rfl fun r hr ↦ by
    rw [Finset.mem_range] at hr
    rw [dite_eq_left (by omega), dite_eq_left (by omega), duplicateAt_apply,
      dite_eq_left (by rw [Fin.val_mk]; omega)]

private theorem sum_duplicateAt_range_succ_ge {m : ℕ} (j : Fin (m + 3)) {𝒟 : Fin (m + 3) → ℤ}
    (h𝒟j : 𝒟 j = -1) :
    ∀ {q : ℕ}, j.1 ≤ q → q ≤ m + 2 →
      (∑ r ∈ Finset.range (q + 1), if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) =
        (∑ r ∈ Finset.range q, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) - 1 := by
  intro q hq₁
  induction q, hq₁ using Nat.le_induction with
  | base =>
    intro _
    rw [Finset.sum_range_succ, sum_duplicateAt_range_le j 𝒟 le_rfl, dite_eq_left (by omega),
      duplicateAt_apply]
    simp [sub_eq_add_neg]
  | succ q hjq ih =>
    intro hq₂
    rw [Finset.sum_range_succ _ (q + 1), ih (by omega), Finset.sum_range_succ _ q,
      dite_eq_left (by omega), dite_eq_left (by omega), duplicateAt_apply]
    rcases eq_or_lt_of_le hjq with heq | hlt
    · have hqj : (⟨q, by omega⟩ : Fin (m + 3)) = j := Fin.ext heq.symm
      rw [hqj, h𝒟j]
      simp [heq]
      omega
    · rw [dite_eq_right (by rw [Fin.val_mk]; omega), ite_eq_right (by rw [Fin.val_mk]; omega)]
      have hfin : (⟨(⟨q + 1, by omega⟩ : Fin (m + 4)).1 - 1, by omega⟩ : Fin (m + 3)) =
          ⟨q, by omega⟩ := Fin.ext (by simp)
      rw [hfin]
      omega

/-! ### Subword and splice identities -/

/-- The initial `(m + 3)`-letter subword of `duplicateAt e j.castSucc w` duplicates `e` at slot `j`
of the initial `(m + 2)`-letter prefix of `w`. -/
theorem subword_init_duplicateAt_castSucc (e : A) {m : ℕ} (j : Fin (m + 2)) (w : Fin (m + 3) → A) :
    subword R (duplicateAt e j.castSucc w) 0 (m + 3) =
      of R A ⟨m + 3, by omega⟩
        (PiTensorProduct.tprod R (duplicateAt e j fun r ↦ w r.castSucc)) := by
  rw [subword_eq_of_tprod R _ (by omega) (by omega)]
  refine of_tprod_congr R A _ rfl fun k ↦ ?_
  simp only [Fin.val_cast, zero_add, duplicateAt_apply, Fin.val_castSucc]
  split_ifs <;> rfl

private theorem subword_init_duplicateAt_last {e : A} {m : ℕ} {w : Fin (m + 3) → A}
    (hw : w (Fin.last (m + 2)) = e) :
    subword R (duplicateAt e (Fin.last (m + 2)) w) 0 (m + 3) =
      of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w) := by
  rw [subword_eq_of_tprod R _ (by omega) (by omega)]
  refine of_tprod_congr R A _ rfl fun k ↦ ?_
  have hk := k.isLt
  simp only [Fin.cast_eq_self, zero_add]
  rw [duplicateAt_apply]
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | heq
  · rw [dite_eq_left (by rw [Fin.val_mk, Fin.val_last]; exact hlt)]
  · rw [dite_eq_right (by rw [Fin.val_mk, Fin.val_last]; omega),
      ite_eq_left (by rw [Fin.val_mk, Fin.val_last]; omega)]
    exact hw.symm.trans (congrArg w (Fin.ext (by rw [Fin.val_last]; omega)))

private theorem subword_tail_duplicateAt_zero {e : A} {m : ℕ} {j : Fin (m + 3)} (hj : j.1 = 0)
    {w : Fin (m + 3) → A} (hw : w 0 = e) :
    subword R (duplicateAt e j w) 1 (m + 3) =
      of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w) := by
  rw [subword_eq_of_tprod R _ (by omega) (by omega)]
  refine of_tprod_congr R A _ rfl fun k ↦ ?_
  rw [Fin.cast_eq_self, duplicateAt_apply, dite_eq_right (by rw [Fin.val_mk]; omega)]
  rcases Nat.eq_zero_or_pos k.1 with hk0 | hkpos
  · rw [ite_eq_left (by rw [Fin.val_mk]; omega)]
    exact hw.symm.trans (congrArg w (Fin.ext (by rw [Fin.val_zero]; omega)))
  · rw [ite_eq_right (by rw [Fin.val_mk]; omega)]
    exact congrArg w (Fin.ext (by rw [Fin.val_mk, Fin.val_mk]; omega))

private theorem subword_tail_duplicateAt_of_pos (R : Type uR) [CommRing R] [Module R A] (e : A)
    {m : ℕ} {j : Fin (m + 3)} (hj : 1 ≤ j.1) (w : Fin (m + 3) → A) :
    ∃ u : Fin (m + 3) → A, u ⟨j.1 - 1, by omega⟩ = e ∧
      subword R (duplicateAt e j w) 1 (m + 3) =
        of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R u) := by
  refine ⟨fun k ↦ duplicateAt e j w ⟨1 + k.1, by omega⟩, ?_,
    subword_eq_of_tprod R _ (by omega) (by omega)⟩
  dsimp only
  rw [duplicateAt_apply, dite_eq_right (by rw [Fin.val_mk]; omega),
    ite_eq_left (by rw [Fin.val_mk]; omega)]

private theorem splice_two_duplicateAt_of_lt (R : Type uR) [CommRing R] [Module R A] (e : A)
    {m : ℕ} {j : Fin (m + 3)} {p : ℕ} (hp : p + 2 ≤ j.1) (w : Fin (m + 3) → A) (v : A) :
    ∃ u : Fin (m + 3) → A, u ⟨j.1 - 1, by omega⟩ = e ∧
      splice R (duplicateAt e j w) 0 (m + 4) p 2 v =
        of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R u) := by
  refine ⟨_, ?_, splice_eq_of_tprod R (duplicateAt e j w) v two_pos (by omega) (by omega)⟩
  dsimp only
  rw [dite_eq_right (by rw [Fin.val_mk]; omega), dite_eq_right (by rw [Fin.val_mk]; omega),
    duplicateAt_apply, dite_eq_right (by rw [Fin.val_mk, Fin.val_mk]; omega),
    ite_eq_left (by rw [Fin.val_mk, Fin.val_mk]; omega)]

private theorem splice_two_duplicateAt_pred {e : A} {m : ℕ} {j : Fin (m + 3)} (hj : 1 ≤ j.1)
    {w : Fin (m + 3) → A} (hw : w j = e) :
    splice R (duplicateAt e j w) 0 (m + 4) (j.1 - 1) 2 (w ⟨j.1 - 1, by omega⟩) =
      of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w) := by
  rw [splice_eq_of_tprod R _ _ two_pos (by omega) (by omega)]
  refine of_tprod_congr R A _ rfl fun k ↦ ?_
  simp only [Fin.cast_eq_self, zero_add]
  rcases lt_trichotomy k.1 (j.1 - 1) with hlt | heq | hgt
  · rw [dite_eq_left hlt, duplicateAt_apply, dite_eq_left (by rw [Fin.val_mk]; omega)]
    exact congrArg w (Fin.ext rfl)
  · rw [dite_eq_right (by omega), dite_eq_left heq]
    exact congrArg w (Fin.ext (by rw [Fin.val_mk]; omega))
  · rw [dite_eq_right (by omega), dite_eq_right (by omega), duplicateAt_apply,
      dite_eq_right (by rw [Fin.val_mk]; omega)]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with hkj | hgt'
    · rw [ite_eq_left (by rw [Fin.val_mk]; omega)]
      exact hw.symm.trans (congrArg w (Fin.ext (by omega)))
    · rw [ite_eq_right (by rw [Fin.val_mk]; omega)]
      exact congrArg w (Fin.ext (by rw [Fin.val_mk, Fin.val_mk]; omega))

private theorem splice_two_duplicateAt_self (R : Type uR) [CommRing R] [Module R A]
    {e : A} {m : ℕ} {j : Fin (m + 3)} {w : Fin (m + 3) → A} (hw : w j = e) :
    splice R (duplicateAt e j w) 0 (m + 4) j.1 2 e =
      of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w) := by
  rw [splice_eq_of_tprod R _ _ two_pos (by omega) (by omega)]
  refine of_tprod_congr R A _ rfl fun k ↦ ?_
  simp only [Fin.cast_eq_self, zero_add]
  rcases lt_trichotomy k.1 j.1 with hlt | heq | hgt
  · rw [dite_eq_left hlt, duplicateAt_apply, dite_eq_left (by rw [Fin.val_mk]; exact hlt)]
    exact congrArg w (Fin.ext rfl)
  · rw [dite_eq_right (by omega), dite_eq_left heq]
    exact hw.symm.trans (congrArg w (Fin.ext heq.symm))
  · rw [dite_eq_right (by omega), dite_eq_right (by omega), duplicateAt_apply,
      dite_eq_right (by rw [Fin.val_mk]; omega), ite_eq_right (by rw [Fin.val_mk]; omega)]
    exact congrArg w (Fin.ext (by rw [Fin.val_mk, Fin.val_mk]; omega))

/-- Collapsing `[e, w (j + 1)]` to `w (j + 1)` in `duplicateAt e j w` recovers `w` when
`w j = e`. -/
theorem splice_two_duplicateAt_succ {e : A} {m : ℕ} {j : Fin (m + 3)} (hj : j.1 < m + 2)
    {w : Fin (m + 3) → A} (hw : w j = e) :
    splice R (duplicateAt e j w) 0 (m + 4) (j.1 + 1) 2 (w ⟨j.1 + 1, by omega⟩) =
      of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w) := by
  rw [splice_eq_of_tprod R _ _ two_pos (by omega) (by omega)]
  refine of_tprod_congr R A _ rfl fun k ↦ ?_
  simp only [Fin.cast_eq_self, zero_add]
  rcases lt_trichotomy k.1 (j.1 + 1) with hlt | heq | hgt
  · rw [dite_eq_left hlt, duplicateAt_apply]
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with hlt' | hkj
    · rw [dite_eq_left (by rw [Fin.val_mk]; exact hlt')]
      exact congrArg w (Fin.ext rfl)
    · rw [dite_eq_right (by rw [Fin.val_mk]; omega), ite_eq_left (by rw [Fin.val_mk]; omega)]
      exact hw.symm.trans (congrArg w (Fin.ext hkj.symm))
  · rw [dite_eq_right (by omega), dite_eq_left heq]
    exact congrArg w (Fin.ext (by rw [Fin.val_mk]; omega))
  · rw [dite_eq_right (by omega), dite_eq_right (by omega), duplicateAt_apply,
      dite_eq_right (by rw [Fin.val_mk]; omega), ite_eq_right (by rw [Fin.val_mk]; omega)]
    exact congrArg w (Fin.ext (by rw [Fin.val_mk, Fin.val_mk]; omega))

private theorem subword_two_duplicateAt_ge {e : A} {m : ℕ} {j : Fin (m + 3)} {q : ℕ}
    (hq₁ : j.1 ≤ q) (hq₂ : q + 2 ≤ m + 3) {w : Fin (m + 3) → A} (hw : w j = e) :
    subword R (duplicateAt e j w) (q + 1) 2 = subword R w q 2 := by
  rw [subword_eq_of_tprod R _ two_pos (by omega), subword_eq_of_tprod R _ two_pos hq₂]
  refine of_tprod_congr R A _ rfl fun k ↦ ?_
  rw [Fin.cast_eq_self, duplicateAt_apply, dite_eq_right (by rw [Fin.val_mk]; omega)]
  by_cases h : (⟨q + 1 + k.1, by omega⟩ : Fin (m + 4)).1 = j.1 ∨
      (⟨q + 1 + k.1, by omega⟩ : Fin (m + 4)).1 = j.1 + 1
  · rw [ite_eq_left h]
    dsimp only at h
    exact hw.symm.trans (congrArg w (Fin.ext (by dsimp only; omega)))
  · rw [ite_eq_right h]
    dsimp only at h
    exact congrArg w (Fin.ext (by dsimp only; omega))

/-- Splicing a two-letter block strictly after `j` commutes with duplicating `e` at slot `j`. -/
theorem splice_two_duplicateAt_after (e : A) {m : ℕ} (j : Fin (m + 2)) {q : ℕ}
    (hq₁ : j.1 + 1 ≤ q) (hq₂ : q + 2 ≤ m + 3) (w : Fin (m + 3) → A) (v : A) :
    splice R (duplicateAt e j.castSucc w) 0 (m + 4) (q + 1) 2 v =
      of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R (duplicateAt e j fun r : Fin (m + 2) ↦
        if _ : r.1 < q then w ⟨r.1, by omega⟩
        else if _ : r.1 = q then v
        else w ⟨r.1 + 1, by omega⟩)) := by
  rw [splice_eq_of_tprod R _ v two_pos (by omega) (by omega)]
  refine of_tprod_congr R A _ rfl fun k ↦ ?_
  have _hk := k.isLt
  simp only [Fin.val_cast, zero_add, duplicateAt_apply, Fin.val_castSucc]
  split_ifs <;> first
    | omega
    | rfl
    | exact congrArg w (Fin.ext (by simp; omega))

/-! ### Stasheff identity on duplicated-unit words -/

private theorem taylor_barDifferential_duplicateAt_ne_two {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {m : ℕ}
    (hlow : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
      (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0)
    (j : Fin (m + 3))
    (hIH : ∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < j.1 → x k = e →
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0)
    {w : Fin (m + 3) → A} (𝒟 : Fin (m + 3) → ℤ) (hwj : w j = e) {p d : ℕ} (hp : p < m + 4)
    (hd : d < m + 5) (hd2 : d ≠ 2) :
    negOnePowCast R (∑ r ∈ Finset.range p,
        if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
      𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p d
        (𝒜.taylor (subword R (duplicateAt e j w) p d))) =
      (if p = 0 ∧ d = m + 3 then
        𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
          ![𝒜.taylor (subword R (duplicateAt e j w) 0 (m + 3)),
            duplicateAt e j w (Fin.last (m + 3))]))
       else 0) +
      (if p = 1 ∧ d = m + 3 ∧ j.1 = 0 then
        -𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w))
       else 0) := by
  by_cases hfit : 0 < d ∧ p + d ≤ m + 4
  swap
  · simp (disch := omega) only [splice_eq_zero_of_not_fits R _ _ hfit, map_zero, smul_zero,
      ite_eq_right, add_zero]
  by_cases hd1 : d = 1
  · subst hd1
    have hz : 𝒜.taylor (subword R (duplicateAt e j w) p 1) = 0 := by
      rw [subword_eq_of_tprod R _ one_pos hfit.2]
      exact h𝒜.taylor_apply_eq_zero_of_mem_filtration_one _
        (of_mem_filtration R A (k := ⟨1, one_pos⟩) le_rfl _)
    simp (disch := omega) only [hz, splice_zero, map_zero, smul_zero, ite_eq_right, add_zero]
  by_cases hdm4 : d = m + 4
  · subst hdm4
    have hz : 𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p (m + 4)
        (𝒜.taylor (subword R (duplicateAt e j w) p (m + 4)))) = 0 := by
      rw [splice_eq_of_tprod R _ _ hfit.1 hfit.2 (by omega)]
      exact h𝒜.taylor_apply_eq_zero_of_mem_filtration_one _
        (of_mem_filtration R A (by dsimp only; omega) _)
    simp (disch := omega) only [hz, smul_zero, ite_eq_right, add_zero]
  by_cases hdle : d ≤ m + 2
  · have heY : duplicateAt e j w j.castSucc = e := by rw [duplicateAt_apply]; simp
    by_cases hblock : p ≤ j.1 ∧ j.1 < p + d
    · have hz : 𝒜.taylor (subword R (duplicateAt e j w) p d) = 0 := by
        rw [subword_eq_of_tprod R _ hfit.1 hfit.2]
        exact hlow ⟨d, hfit.1⟩ hd2 hdle _ ⟨⟨j.1 - p, by dsimp only; omega⟩, (congrArg _
          (Fin.ext (by rw [Fin.val_mk, Fin.val_mk, Fin.val_castSucc]; omega))).trans heY⟩
      simp (disch := omega) only [hz, splice_zero, map_zero, smul_zero, ite_eq_right, add_zero]
    · obtain ⟨u, ⟨r, hr⟩, hsp⟩ := exists_splice_eq_of_tprod R (duplicateAt e j w) hfit.2
        (𝒜.taylor (subword R (duplicateAt e j w) p d)) (i := j.castSucc) (by simpa using hblock)
      have hz := hlow ⟨m + 5 - d, by omega⟩ (by dsimp only; omega) (by dsimp only; omega) u
        ⟨r, hr.trans heY⟩
      simp (disch := omega) only [hsp, hz, smul_zero, ite_eq_right, add_zero]
  obtain rfl : d = m + 3 := by omega
  rcases Nat.eq_zero_or_pos p with rfl | hppos
  · rw [ite_eq_left ⟨rfl, rfl⟩, ite_eq_right (by omega), add_zero, Finset.sum_range_zero,
      negOnePowCast_zero, one_smul, splice_collapse_init_eq R (by omega : 0 < m + 3)]
  · obtain rfl : p = 1 := by omega
    rcases Nat.eq_zero_or_pos j.1 with hj0 | hjpos
    · have hw0 : w 0 = e := (congrArg w (Fin.ext hj0.symm)).trans hwj
      have hY0 : duplicateAt e j w 0 = e := by rw [duplicateAt_apply]; simp [hj0]
      rw [ite_eq_right (by omega), ite_eq_left ⟨rfl, rfl, hj0⟩, zero_add, Finset.sum_range_one,
        dite_eq_left (by omega : 0 < m + 4), duplicateAt_apply]
      simp only [hj0, lt_irrefl, dite_false, true_or, ite_true, negOnePowCast_neg,
        negOnePowCast_one, neg_one_smul]
      rw [splice_collapse_tail_eq R (by omega : 0 < m + 3), hY0,
        subword_tail_duplicateAt_zero hj0 hw0, h𝒜.taylor_of_two_cohomologicalUnit_left he]
    · obtain ⟨u, hu, hsub⟩ := subword_tail_duplicateAt_of_pos R e hjpos w
      rw [hsub, hIH u ⟨j.1 - 1, by omega⟩ (by dsimp only; omega) hu, splice_zero, map_zero,
        smul_zero, ite_eq_right (by omega), ite_eq_right (by omega), add_zero]

private theorem taylor_barDifferential_duplicateAt_binary_prefix {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {m : ℕ} (j : Fin (m + 3))
    (hIH : ∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < j.1 → x k = e →
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0)
    {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ}
    (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) (hwj : w j = e) :
    (∑ p ∈ Finset.range (j.1 + 1),
      negOnePowCast R (∑ r ∈ Finset.range p,
          if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
        𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p 2
          (𝒜.taylor (subword R (duplicateAt e j w) p 2)))) =
      if j.1 = 0 then 𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w)) else 0 := by
  have hjlt := j.isLt
  rcases Nat.eq_zero_or_pos j.1 with hj0 | hjpos
  · have hr0 : Finset.range (j.1 + 1) = Finset.range 1 := congrArg Finset.range (by omega)
    have hsp := splice_two_duplicateAt_self R hwj
    rw [hj0] at hsp
    rw [ite_eq_left hj0, hr0, Finset.sum_range_one, Finset.sum_range_zero, negOnePowCast_zero,
      one_smul, subword_two_eq R _ (by omega)]
    have h0 : duplicateAt e j w ⟨0, by omega⟩ = e := by rw [duplicateAt_apply]; simp [hj0]
    have h1 : duplicateAt e j w ⟨1, by omega⟩ = e := by rw [duplicateAt_apply]; simp [hj0]
    rw [h0, h1, h𝒜.taylor_of_two_cohomologicalUnit_left he, hsp]
  · have hlen : Finset.range (j.1 + 1) = Finset.range ((j.1 - 1) + 1 + 1) :=
      congrArg Finset.range (by omega)
    rw [ite_eq_right (Nat.ne_of_gt hjpos), hlen, Finset.sum_range_succ, Finset.sum_range_succ]
    have hpre : (∑ p ∈ Finset.range (j.1 - 1),
        negOnePowCast R (∑ r ∈ Finset.range p,
            if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
          𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p 2
            (𝒜.taylor (subword R (duplicateAt e j w) p 2)))) = 0 :=
      Finset.sum_eq_zero fun p hp ↦ by
        rw [Finset.mem_range] at hp
        obtain ⟨u, hu, hsp⟩ := splice_two_duplicateAt_of_lt R e (by omega : p + 2 ≤ j.1) w
          (𝒜.taylor (subword R (duplicateAt e j w) p 2))
        rw [hsp, hIH u ⟨j.1 - 1, by omega⟩ (by dsimp only; omega) hu, smul_zero]
    have hj_pred : (j.1 - 1) + 1 = j.1 := by omega
    rw [hpre, zero_add, hj_pred, sum_duplicateAt_range_le j 𝒟 (by omega),
      sum_duplicateAt_range_le j 𝒟 le_rfl]
    have hYpred : duplicateAt e j w ⟨j.1 - 1, by omega⟩ = w ⟨j.1 - 1, by omega⟩ := by
      rw [duplicateAt_apply, dite_eq_left (by rw [Fin.val_mk]; omega)]
    have hY0 : duplicateAt e j w ⟨j.1 - 1 + 1, by omega⟩ = e := by
      rw [duplicateAt_apply]; simp [hj_pred]
    have hY1 : duplicateAt e j w ⟨j.1, by omega⟩ = e := by rw [duplicateAt_apply]; simp
    have hY2 : duplicateAt e j w ⟨j.1 + 1, by omega⟩ = e := by rw [duplicateAt_apply]; simp
    rw [subword_two_eq R _ (by omega), hYpred, hY0, h𝒜.taylor_of_two_cohomologicalUnit_right he,
      𝒜.grading.koszulTwist_one_apply_of_mem
        (by simpa [InternalGrading.shift_piece] using hw ⟨j.1 - 1, by omega⟩),
      ← negOnePowCast_eq_intCast, splice_smul, map_smul, splice_two_duplicateAt_pred hjpos hwj,
      subword_two_eq R _ (by omega), hY1, hY2, h𝒜.taylor_of_two_cohomologicalUnit_left he,
      splice_two_duplicateAt_self R hwj, smul_smul, ← negOnePowCast_add, ← add_smul]
    have hrj : Finset.range j.1 = Finset.range ((j.1 - 1) + 1) :=
      congrArg Finset.range (by omega)
    have hS : (∑ r ∈ Finset.range j.1, if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) =
        (∑ r ∈ Finset.range (j.1 - 1), if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) +
          𝒟 ⟨j.1 - 1, by omega⟩ := by
      rw [hrj, Finset.sum_range_succ, dite_eq_left (by omega)]
    rw [hS, ← add_assoc, negOnePowCast_add _ 1, negOnePowCast_one, mul_neg_one, neg_add_cancel,
      zero_smul]

private theorem taylor_barDifferential_duplicateAt_row {𝒜 : AInfinityAlgebra R A}
    (h𝒜 : 𝒜.IsMinimal) {e : A} (he : 𝒜.CohomologicalUnit e) {m : ℕ}
    (hlow : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
      (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0)
    (j : Fin (m + 3))
    (hIH : ∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < j.1 → x k = e →
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0)
    {w : Fin (m + 3) → A} (𝒟 : Fin (m + 3) → ℤ) (hwj : w j = e) {p : ℕ}
    (hp : p ∈ Finset.range (m + 4)) :
    (∑ d ∈ Finset.range (m + 5),
      negOnePowCast R (∑ r ∈ Finset.range p,
          if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
        𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p d
          (𝒜.taylor (subword R (duplicateAt e j w) p d)))) =
      negOnePowCast R (∑ r ∈ Finset.range p,
          if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
        𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) p 2
          (𝒜.taylor (subword R (duplicateAt e j w) p 2))) +
      ((if p = 0 then
          𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
            ![𝒜.taylor (subword R (duplicateAt e j w) 0 (m + 3)),
              duplicateAt e j w (Fin.last (m + 3))]))
        else 0) +
       (if p = 1 ∧ j.1 = 0 then
          -𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R w))
        else 0)) := by
  rw [Finset.mem_range] at hp
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 (by omega : 2 < m + 5))]
  congr 1
  rw [Finset.sum_congr rfl fun d hd ↦
    taylor_barDifferential_duplicateAt_ne_two h𝒜 he hlow j hIH 𝒟 hwj hp
      (Finset.mem_range.1 (Finset.mem_erase.1 hd).2) (Finset.mem_erase.1 hd).1]
  simp only [Finset.sum_add_distrib, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_erase, Finset.mem_range]
  congr 1 <;> split_ifs <;> first | rfl | omega

/-- **Reduced Stasheff identity on `duplicateAt e j w`**: on a minimal `A∞` algebra with
cohomological unit `e` whose Taylor map vanishes on words of length `k ≠ 2` (`k ≤ m + 2`) containing
`e` and on `(m + 3)`-letter words carrying `e` in slots `< j`, the Stasheff identity on
`duplicateAt e j w` reduces to the initial `(m + 3)`-collapse plus the binary collapses from
position `j + 1` onward. -/
theorem IsMinimal.taylor_barDifferential_duplicateAt {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal)
    {e : A} (he : 𝒜.CohomologicalUnit e) {m : ℕ}
    (hlow : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
      (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0)
    (j : Fin (m + 3))
    (hIH : ∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < j.1 → x k = e →
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0)
    {w : Fin (m + 3) → A} {𝒟 : Fin (m + 3) → ℤ}
    (hw : ∀ r, w r ∈ (𝒜.grading.shift 1).piece (𝒟 r)) (hwj : w j = e) (h𝒟j : 𝒟 j = -1) :
    𝒜.taylor (of R A (2 : ℕ+) (PiTensorProduct.tprod R
        ![𝒜.taylor (subword R (duplicateAt e j w) 0 (m + 3)),
          duplicateAt e j w (Fin.last (m + 3))])) +
      ∑ t ∈ Finset.range (m + 2 - j.1),
        -(negOnePowCast R
            (∑ r ∈ Finset.range (j.1 + t), if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) (j.1 + 1 + t) 2
            (𝒜.taylor (subword R w (j.1 + t) 2)))) = 0 := by
  have hjlt := j.isLt
  have hzero : 𝒜.taylor (𝒜.barDifferential
      (of R A ⟨m + 4, by omega⟩ (PiTensorProduct.tprod R (duplicateAt e j w)))) = 0 := by
    rw [← 𝒜.letter_comp_barDifferential, LinearMap.comp_apply,
      ← LinearMap.comp_apply 𝒜.barDifferential, 𝒜.barDifferential_sq, LinearMap.zero_apply,
      map_zero]
  rw [barDifferential_def,
    gradedCoderiv_of_tprod_of_homogeneous _ _ 1 _ _ (duplicateAt (-1 : ℤ) j 𝒟)
      (duplicateAt_mem_piece he.mem_shift_one_piece j hw)] at hzero
  simp only [one_mul, map_sum, map_smul, ← negOnePowCast_eq_intCast] at hzero
  rw [Finset.sum_congr rfl fun p hp ↦
      taylor_barDifferential_duplicateAt_row h𝒜 he hlow j hIH 𝒟 hwj hp,
    Finset.sum_add_distrib, Finset.sum_add_distrib] at hzero
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_range,
    ite_eq_left (by omega : 0 < m + 4), ite_eq_left (by omega : 1 < m + 4)] at hzero
  have hsplit_range : Finset.range (m + 3) = Finset.range ((j.1 + 1) + (m + 2 - j.1)) :=
    congrArg Finset.range (by omega)
  rw [Finset.sum_range_succ _ (m + 3),
    splice_eq_zero_of_not_fits R _ _ (by omega : ¬ (0 < 2 ∧ (m + 3) + 2 ≤ m + 4)), map_zero,
    smul_zero, add_zero, hsplit_range, Finset.sum_range_add,
    taylor_barDifferential_duplicateAt_binary_prefix h𝒜 he j hIH hw hwj] at hzero
  have htail : (∑ t ∈ Finset.range (m + 2 - j.1),
      negOnePowCast R (∑ r ∈ Finset.range (j.1 + 1 + t),
          if h : r < m + 4 then duplicateAt (-1 : ℤ) j 𝒟 ⟨r, h⟩ else 0) •
        𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) (j.1 + 1 + t) 2
          (𝒜.taylor (subword R (duplicateAt e j w) (j.1 + 1 + t) 2)))) =
      ∑ t ∈ Finset.range (m + 2 - j.1),
        -(negOnePowCast R
            (∑ r ∈ Finset.range (j.1 + t), if h : r < m + 3 then 𝒟 ⟨r, h⟩ else 0) •
          𝒜.taylor (splice R (duplicateAt e j w) 0 (m + 4) (j.1 + 1 + t) 2
            (𝒜.taylor (subword R w (j.1 + t) 2)))) :=
    Finset.sum_congr rfl fun t ht ↦ by
      rw [Finset.mem_range] at ht
      have hidx : j.1 + 1 + t = (j.1 + t) + 1 := by omega
      rw [hidx, sum_duplicateAt_range_succ_ge j h𝒟j (by omega) (by omega),
        subword_two_duplicateAt_ge (by omega) (by omega) hwj, sub_eq_add_neg, negOnePowCast_add,
        negOnePowCast_neg, negOnePowCast_one, mul_neg_one, neg_smul]
  rw [htail] at hzero
  by_cases hj0 : j.1 = 0
  · rw [ite_eq_left hj0, ite_eq_left hj0] at hzero
    refine Eq.trans ?_ hzero
    abel
  · rw [ite_eq_right hj0, ite_eq_right hj0] at hzero
    refine Eq.trans ?_ hzero
    abel

/-- On a minimal `A∞` algebra with cohomological unit `e`, once `𝒜.taylor` vanishes on pure tensor
words of length `k ≠ 2` (`k ≤ m + 2`) containing `e` and on `(m + 3)`-letter words carrying `e` in
any of the first `m + 2` slots, the Stasheff identity forces vanishing when `e` sits in the final
slot `Fin.last (m + 2)`. -/
theorem IsMinimal.taylor_of_tprod_last_eq_zero {𝒜 : AInfinityAlgebra R A} (h𝒜 : 𝒜.IsMinimal)
    {e : A} (he : 𝒜.CohomologicalUnit e) {m : ℕ}
    (hlow : ∀ (k : {k : ℕ // 0 < k}), k.1 ≠ 2 → k.1 ≤ m + 2 → ∀ x : Fin k.1 → A,
      (∃ r, x r = e) → 𝒜.taylor (of R A k (PiTensorProduct.tprod R x)) = 0)
    (hIH : ∀ (x : Fin (m + 3) → A) (k : Fin (m + 3)), k.1 < m + 2 → x k = e →
      𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0)
    (x : Fin (m + 3) → A) (hx : x (Fin.last (m + 2)) = e) :
    𝒜.taylor (of R A ⟨m + 3, by omega⟩ (PiTensorProduct.tprod R x)) = 0 := by
  refine of_tprod_mem_of_mem_piece (𝒜.grading.shift 1) he.mem_shift_one_piece
    (S := LinearMap.ker 𝒜.taylor) ⟨m + 3, by omega⟩ (Fin.last (m + 2))
    (fun w 𝒟 hw hwlast h𝒟last ↦ ?_) x hx
  rw [LinearMap.mem_ker]
  have hst := h𝒜.taylor_barDifferential_duplicateAt he hlow (Fin.last (m + 2))
    (by simpa only [Fin.val_last] using hIH) hw hwlast h𝒟last
  have hYlast : duplicateAt e (Fin.last (m + 2)) w (Fin.last (m + 3)) = e := by
    rw [duplicateAt_apply]; simp
  rw [Fin.val_last, Nat.sub_self, Finset.sum_range_zero, add_zero,
    subword_init_duplicateAt_last hwlast, hYlast,
    h𝒜.taylor_of_two_cohomologicalUnit_right he] at hst
  simpa only [InternalGrading.koszulTwist_koszulTwist, map_zero] using
    congrArg (𝒜.grading.koszulTwist 1) hst

end DuplicateAt

end TauCeti.AInfinityAlgebra
