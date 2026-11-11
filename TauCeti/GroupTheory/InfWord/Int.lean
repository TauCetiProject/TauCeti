/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Order.SuccPred.Int
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import TauCeti.GroupTheory.InfWord.Basic

/-!
# `ℤ`-words are finite words

For `Λ = ℤ` an infinite word `w : [1, n] → X^{±1}` is a finite word in the letters `X^{±1}`. This
file identifies `TauCeti.InfWord ℤ X` with `List (X × Bool)`, the type of words used by Mathlib's
`FreeGroup X`, and shows that the identification matches concatenation with `++`, inversion with
`FreeGroup.invRev`, and reducedness with `FreeGroup.IsReduced`. Hence the reduced `ℤ`-words are
exactly the normal forms `FreeGroup.toWord g` of the elements `g` of the free group on `X`.

## Main definitions

* `TauCeti.InfWord.ofList`, `TauCeti.InfWord.toList`: the `ℤ`-word spelled by a list, and the list
  of letters of a `ℤ`-word.
* `TauCeti.InfWord.equivList`: the bijection `InfWord ℤ X ≃ List (X × Bool)`.

## Main results

* `TauCeti.InfWord.ofList_append`, `TauCeti.InfWord.ofList_invRev`: the bijection is compatible
  with concatenation and inversion.
* `TauCeti.InfWord.isReduced_ofList`: a list is a reduced `ℤ`-word iff it is reduced in the sense
  of `FreeGroup.IsReduced`.
* `TauCeti.InfWord.isReduced_iff_mem_range_toWord`: the reduced `ℤ`-words are the words
  `FreeGroup.toWord g`.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §3.1.
-/

public section

namespace TauCeti

namespace InfWord

variable {X : Type*}

/-- The `ℤ`-word spelled by a list of letters: its letter at the position `i + 1` is the `i`-th
entry of the list. -/
def ofList (L : List (X × Bool)) : InfWord ℤ X where
  length := L.length
  letter n := if 0 < n then L[n.toNat - 1]? else none
  length_nonneg := by simp
  isSome_letter n := by
    split_ifs with h
    · rw [Option.isSome_iff_ne_none, ne_eq, List.getElem?_eq_none_iff]; omega
    · simp [h]

@[simp] theorem length_ofList (L : List (X × Bool)) : (ofList L).length = L.length := (rfl)

theorem letter_ofList (L : List (X × Bool)) (n : ℤ) :
    (ofList L).letter n = if 0 < n then L[n.toNat - 1]? else none := (rfl)

@[simp]
theorem letter_ofList_natCast_add_one (L : List (X × Bool)) (i : ℕ) :
    (ofList L).letter (i + 1) = L[i]? := by
  simp [letter_ofList, show (0 : ℤ) < i + 1 by omega]

/-- The list of letters of a `ℤ`-word. -/
def toList (w : InfWord ℤ X) : List (X × Bool) :=
  List.ofFn fun i : Fin w.length.toNat =>
    (w.letter (i + 1)).get ((w.isSome_letter _).2 (by omega))

@[simp]
theorem length_toList (w : InfWord ℤ X) : w.toList.length = w.length.toNat := by
  simp [toList]

theorem natCast_length_toList (w : InfWord ℤ X) : (w.toList.length : ℤ) = w.length := by
  simp [w.length_nonneg]

theorem getElem?_toList (w : InfWord ℤ X) (i : ℕ) : w.toList[i]? = w.letter (i + 1) := by
  rw [toList, List.getElem?_ofFn]
  split_ifs with h
  · simp
  · exact (letter_eq_none_of_not_le (by omega)).symm

@[simp]
theorem ofList_toList (w : InfWord ℤ X) : ofList w.toList = w := by
  refine ext (natCast_length_toList w) fun n h0 hn => ?_
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = i + 1 := ⟨(n - 1).toNat, by omega⟩
  rw [letter_ofList_natCast_add_one, getElem?_toList]

@[simp]
theorem toList_ofList (L : List (X × Bool)) : (ofList L).toList = L :=
  List.ext_getElem? fun i => by rw [getElem?_toList, letter_ofList_natCast_add_one]

/-- Words over `ℤ` are finite words: a `ℤ`-word is the same thing as the list of its letters. -/
def equivList : InfWord ℤ X ≃ List (X × Bool) where
  toFun := toList
  invFun := ofList
  left_inv := ofList_toList
  right_inv := toList_ofList

@[simp] theorem equivList_apply (w : InfWord ℤ X) : equivList w = w.toList := (rfl)

@[simp]
theorem equivList_symm_apply (L : List (X × Bool)) : equivList.symm L = ofList L := (rfl)

@[simp]
theorem ofList_nil : ofList ([] : List (X × Bool)) = empty ℤ X := by
  simp [← length_eq_zero_iff]

theorem ofList_append (L₁ L₂ : List (X × Bool)) :
    ofList (L₁ ++ L₂) = ofList L₁ ++ ofList L₂ := by
  refine ext (by simp) fun n h0 hn => ?_
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = i + 1 := ⟨(n - 1).toNat, by omega⟩
  rw [letter_ofList_natCast_add_one, List.getElem?_append, letter_append, length_ofList]
  by_cases h : i < L₁.length
  · simp [h, show (i : ℤ) + 1 ≤ L₁.length by omega]
  · obtain ⟨j, rfl⟩ : ∃ j, i = L₁.length + j := ⟨i - L₁.length, by omega⟩
    have h' : ¬((L₁.length + j : ℕ) : ℤ) + 1 ≤ L₁.length := by omega
    have e : ((L₁.length + j : ℕ) : ℤ) + 1 - L₁.length = j + 1 := by omega
    simp only [h, h', ↓reduceIte, e, letter_ofList_natCast_add_one, Nat.add_sub_cancel_left]

theorem ofList_invRev (L : List (X × Bool)) : ofList (FreeGroup.invRev L) = (ofList L)⁻¹ := by
  refine ext (by simp) fun n h0 hn => ?_
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = i + 1 := ⟨(n - 1).toNat, by omega⟩
  have hi : i < L.length := by simp at hn; omega
  rw [letter_ofList_natCast_add_one, letter_inv, length_ofList,
    show (L.length : ℤ) + 1 - (i + 1) = (L.length - 1 - i : ℕ) + 1 by omega,
    letter_ofList_natCast_add_one, FreeGroup.invRev, List.getElem?_reverse (by simpa using hi)]
  simp [Prod.map_def]

theorem toList_empty : (empty ℤ X).toList = [] := by
  rw [← ofList_nil, toList_ofList]

theorem toList_append (u v : InfWord ℤ X) : (u ++ v).toList = u.toList ++ v.toList := by
  rw [← toList_ofList (u.toList ++ v.toList), ofList_append, ofList_toList, ofList_toList]

theorem toList_inv (w : InfWord ℤ X) : w⁻¹.toList = FreeGroup.invRev w.toList := by
  rw [← toList_ofList (FreeGroup.invRev w.toList), ofList_invRev, ofList_toList]

/-- A list of letters is reduced as a `ℤ`-word exactly when it is a reduced word of the free
group. -/
@[simp]
theorem isReduced_ofList {L : List (X × Bool)} : (ofList L).IsReduced ↔ FreeGroup.IsReduced L := by
  rw [FreeGroup.IsReduced, List.isChain_iff_getElem, isReduced_iff]
  have key (i : ℕ) (hi : i + 1 < L.length) :
      (ofList L).letter ((i : ℤ) + 1 + 1) ≠ ((ofList L).letter (i + 1)).map (Prod.map id not) ↔
        (L[i].1 = L[i + 1].1 → L[i].2 = L[i + 1].2) := by
    rw [show (i : ℤ) + 1 + 1 = ((i + 1 : ℕ) : ℤ) + 1 by omega, letter_ofList_natCast_add_one,
      letter_ofList_natCast_add_one, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (by omega), Option.map_some, Ne, Option.some.injEq]
    generalize L[i] = a
    generalize L[i + 1] = b
    obtain ⟨x, s⟩ := a
    obtain ⟨y, t⟩ := b
    cases s <;> cases t <;> simp [eq_comm]
  refine ⟨fun h i hi => (key i hi).1 (h (i + 1) (by omega) (by simp; omega)), fun h n h0 hn => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = i + 1 := ⟨(n - 1).toNat, by omega⟩
  exact (key i (by simp at hn; omega)).2 (h i (by simp at hn; omega))

theorem isReduced_iff_isReduced_toList {w : InfWord ℤ X} :
    w.IsReduced ↔ FreeGroup.IsReduced w.toList := by
  rw [← isReduced_ofList, ofList_toList]

/-- For `Λ = ℤ` the reduced words are exactly the normal forms `FreeGroup.toWord` of the elements
of the free group. -/
theorem isReduced_iff_mem_range_toWord [DecidableEq X] {w : InfWord ℤ X} :
    w.IsReduced ↔ w.toList ∈ Set.range (FreeGroup.toWord (α := X)) := by
  rw [isReduced_iff_isReduced_toList]
  refine ⟨fun h => ⟨FreeGroup.mk w.toList, ?_⟩, ?_⟩
  · exact FreeGroup.toWord_mk.trans h.reduce_eq
  · rintro ⟨g, hg⟩
    rw [← hg]
    exact FreeGroup.isReduced_toWord

end InfWord

end TauCeti
