/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.RootSubgroup
import Mathlib.GroupTheory.Commutator.Basic

/-!
# The negative double-bond Chevalley relation in the short-root F₄ carrier

At Bourbaki nodes one and two (zero based), the first root is long and the second short.
The commutator of their negative root subgroups has factors at the roots -α₂ - α₃ and
-α₂ - 2α₃. These factors use the existing Weyl presentations `[1, 2], 2` and `[2, 1], 1`.
Their parameters are `ab` and `ab²`, with signs fixed by those particular presentations.
The identity holds over every commutative ring, with the short-root divided square retained.

These equations concern the explicit twenty-six-dimensional carrier, not an identification
with an independently pinned simply connected group scheme.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.

The calculation uses the integral generator tables in
`TauCeti.Algebra.Lie.F4.ShortRoot.Basic` and the Weyl transports in
`TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.RootSubgroup`.
-/

public section

namespace TauCeti.F4ShortRoot

open scoped commutatorElement

universe v

private abbrev Node := Fin 4 ⊕ Fin 4

-- A reversed list of root factors permits column selection rather than full matrix sums.
private def wordEntry {A : Type*} [CommRing A] : List (Node × A) → Fin 26 → Fin 26 → A
  | [], a, b => if a = b then 1 else 0
  | (Sum.inl i, u) :: l, a, b =>
      wordEntry l a b +
        (if raisingCoeff i b = 0 then 0
        else u * (raisingCoeff i b : A) * wordEntry l a (raisingTarget i b)) +
        (if raisingDividedSquareCoeff i b = 0 then 0
        else u ^ 2 * (raisingDividedSquareCoeff i b : A) *
          wordEntry l a (raisingDividedSquareTarget i b))
  | (Sum.inr i, u) :: l, a, b =>
      wordEntry l a b +
        (if loweringCoeff i b = 0 then 0
        else u * (loweringCoeff i b : A) * wordEntry l a (loweringTarget i b)) +
        (if loweringDividedSquareCoeff i b = 0 then 0
        else u ^ 2 * (loweringDividedSquareCoeff i b : A) *
          wordEntry l a (loweringDividedSquareTarget i b))

private theorem wordEntry_eq {A : Type*} [CommRing A] (l : List (Node × A)) (a b : Fin 26) :
    wordEntry l a b =
      (((l.reverse.map fun p => rootSubgroupPoints p.1 A (Multiplicative.ofAdd p.2)).prod :
        points A) : Matrix.GeneralLinearGroup (Fin 26) A).val a b := by
  induction l generalizing b with
  | nil => simp [wordEntry, Matrix.one_apply]
  | cons p l ih =>
    obtain ⟨k, u⟩ := p
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one, Subgroup.coe_mul, Units.val_mul]
    rw [coe_rootSubgroupPoints_eq]
    cases k with
    | inl i =>
      simp only [rootMatrix_inl, rootDividedSquareMatrix_inl, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, raisingMatrix_apply,
        raisingDividedSquareMatrix_apply, apply_ite Int.cast, Int.cast_zero,
        mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Matrix.one_apply,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, toAdd_ofAdd]
      simp only [wordEntry, ih]
      split_ifs <;> simp_all <;> ring
    | inr i =>
      simp only [rootMatrix_inr, rootDividedSquareMatrix_inr, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, loweringMatrix_apply,
        loweringDividedSquareMatrix_apply, apply_ite Int.cast, Int.cast_zero,
        mul_add, mul_ite, mul_zero, Finset.sum_add_distrib, Matrix.one_apply,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, toAdd_ofAdd]
      simp only [wordEntry, ih]
      split_ifs <;> simp_all <;> ring

-- The conjugated negative short root has a divided square at entry (16, 9).
private def sumTarget : Fin 26 → Fin 26 :=
  ![0, 3, 5, 3, 8, 5, 10, 7, 8, 12, 10, 11, 16, 16, 14, 19, 16, 21, 18, 19, 23, 21, 24, 23, 24, 25]
private def sumCoeff : Fin 26 → ℤ :=
  ![0, 1, -1, 0, 1, 0, -1, 0, 0, -1, 0, 0, 2, 1, 0, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0]
private def highestTarget : Fin 26 → Fin 26 :=
  ![0, 5, 2, 3, 10, 5, 6, 7, 8, 14, 10, 16, 12, 13, 14, 21, 16, 17, 18, 19, 24, 21, 22, 23, 24, 25]
private def highestCoeff : Fin 26 → ℤ :=
  ![0, 1, 0, 0, 1, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]

private def sumEntry {A : Type*} [CommRing A] (u : A) (i j : Fin 26) : A :=
  (if i = j then 1 else 0) + (if i = sumTarget j then u * (sumCoeff j : A) else 0) -
    (if i = 16 ∧ j = 9 then u ^ 2 else 0)

private def highestEntry {A : Type*} [CommRing A] (u : A) (i j : Fin 26) : A :=
  (if i = j then 1 else 0) + (if i = highestTarget j then u * (highestCoeff j : A) else 0)

-- The lists below are in reverse multiplication order.
private def conjugateWord {A : Type*} [CommRing A] (i j : Fin 4) (u : A) : List (Node × A) :=
  [(.inl i, -1), (.inr i, 1), (.inl i, -1), (.inr j, -u),
    (.inl i, 1), (.inr i, -1), (.inl i, 1)]

-- These finite coefficient certificates compute the two Weyl conjugates before multiplying them.
-- Keeping each row separate bounds elaboration without changing the heartbeat limit.
local macro "double_bond_entry" : tactic => `(tactic|
  (dsimp [conjugateWord, wordEntry, sumEntry, highestEntry, sumTarget, sumCoeff,
      highestTarget, highestCoeff, raisingCoeff, raisingTarget, loweringCoeff, loweringTarget,
      raisingDividedSquareCoeff, raisingDividedSquareTarget,
      loweringDividedSquareCoeff, loweringDividedSquareTarget] <;> norm_num <;> ring))

private theorem conjugate_row0 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 0 j = sumEntry u 0 j ∧
      wordEntry (conjugateWord 2 1 u) 0 j = highestEntry u 0 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row9 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 9 j = sumEntry u 9 j ∧
      wordEntry (conjugateWord 2 1 u) 9 j = highestEntry u 9 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row1 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 1 j = sumEntry u 1 j ∧
      wordEntry (conjugateWord 2 1 u) 1 j = highestEntry u 1 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row2 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 2 j = sumEntry u 2 j ∧
      wordEntry (conjugateWord 2 1 u) 2 j = highestEntry u 2 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row3 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 3 j = sumEntry u 3 j ∧
      wordEntry (conjugateWord 2 1 u) 3 j = highestEntry u 3 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row4 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 4 j = sumEntry u 4 j ∧
      wordEntry (conjugateWord 2 1 u) 4 j = highestEntry u 4 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row5 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 5 j = sumEntry u 5 j ∧
      wordEntry (conjugateWord 2 1 u) 5 j = highestEntry u 5 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row6 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 6 j = sumEntry u 6 j ∧
      wordEntry (conjugateWord 2 1 u) 6 j = highestEntry u 6 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row7 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 7 j = sumEntry u 7 j ∧
      wordEntry (conjugateWord 2 1 u) 7 j = highestEntry u 7 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row8 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 8 j = sumEntry u 8 j ∧
      wordEntry (conjugateWord 2 1 u) 8 j = highestEntry u 8 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row10 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 10 j = sumEntry u 10 j ∧
      wordEntry (conjugateWord 2 1 u) 10 j = highestEntry u 10 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row11 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 11 j = sumEntry u 11 j ∧
      wordEntry (conjugateWord 2 1 u) 11 j = highestEntry u 11 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row12 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 12 j = sumEntry u 12 j ∧
      wordEntry (conjugateWord 2 1 u) 12 j = highestEntry u 12 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row13 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 13 j = sumEntry u 13 j ∧
      wordEntry (conjugateWord 2 1 u) 13 j = highestEntry u 13 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row14 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 14 j = sumEntry u 14 j ∧
      wordEntry (conjugateWord 2 1 u) 14 j = highestEntry u 14 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row15 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 15 j = sumEntry u 15 j ∧
      wordEntry (conjugateWord 2 1 u) 15 j = highestEntry u 15 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row16 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 16 j = sumEntry u 16 j ∧
      wordEntry (conjugateWord 2 1 u) 16 j = highestEntry u 16 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row17 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 17 j = sumEntry u 17 j ∧
      wordEntry (conjugateWord 2 1 u) 17 j = highestEntry u 17 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row18 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 18 j = sumEntry u 18 j ∧
      wordEntry (conjugateWord 2 1 u) 18 j = highestEntry u 18 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row19 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 19 j = sumEntry u 19 j ∧
      wordEntry (conjugateWord 2 1 u) 19 j = highestEntry u 19 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row20 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 20 j = sumEntry u 20 j ∧
      wordEntry (conjugateWord 2 1 u) 20 j = highestEntry u 20 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row21 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 21 j = sumEntry u 21 j ∧
      wordEntry (conjugateWord 2 1 u) 21 j = highestEntry u 21 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row22 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 22 j = sumEntry u 22 j ∧
      wordEntry (conjugateWord 2 1 u) 22 j = highestEntry u 22 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row23 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 23 j = sumEntry u 23 j ∧
      wordEntry (conjugateWord 2 1 u) 23 j = highestEntry u 23 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row24 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 24 j = sumEntry u 24 j ∧
      wordEntry (conjugateWord 2 1 u) 24 j = highestEntry u 24 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_row25 {A : Type*} [CommRing A] (u : A) (j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) 25 j = sumEntry u 25 j ∧
      wordEntry (conjugateWord 2 1 u) 25 j = highestEntry u 25 j := by
  constructor <;> fin_cases j <;> double_bond_entry

private theorem conjugate_entries {A : Type*} [CommRing A] (u : A) (i j : Fin 26) :
    wordEntry (conjugateWord 1 2 u) i j = sumEntry u i j ∧
      wordEntry (conjugateWord 2 1 u) i j = highestEntry u i j := by
  fin_cases i
  · exact conjugate_row0 u j
  · exact conjugate_row1 u j
  · exact conjugate_row2 u j
  · exact conjugate_row3 u j
  · exact conjugate_row4 u j
  · exact conjugate_row5 u j
  · exact conjugate_row6 u j
  · exact conjugate_row7 u j
  · exact conjugate_row8 u j
  · exact conjugate_row9 u j
  · exact conjugate_row10 u j
  · exact conjugate_row11 u j
  · exact conjugate_row12 u j
  · exact conjugate_row13 u j
  · exact conjugate_row14 u j
  · exact conjugate_row15 u j
  · exact conjugate_row16 u j
  · exact conjugate_row17 u j
  · exact conjugate_row18 u j
  · exact conjugate_row19 u j
  · exact conjugate_row20 u j
  · exact conjugate_row21 u j
  · exact conjugate_row22 u j
  · exact conjugate_row23 u j
  · exact conjugate_row24 u j
  · exact conjugate_row25 u j

private def commutatorWord {A : Type*} [CommRing A] (a b : A) : List (Node × A) :=
  [(.inr 2, -b), (.inr 1, -a), (.inr 2, b), (.inr 1, a)]

private def productEntry {A : Type*} [CommRing A] (a b : A) (i j : Fin 26) : A :=
  sumEntry (a * b) i j +
    (a * b ^ 2) * (highestCoeff j : A) * sumEntry (a * b) i (highestTarget j)

local macro "double_bond_product_entry" : tactic => `(tactic|
  (dsimp [commutatorWord, wordEntry, productEntry, sumEntry, sumTarget, sumCoeff,
      highestTarget, highestCoeff, loweringCoeff, loweringTarget,
      loweringDividedSquareCoeff, loweringDividedSquareTarget] <;> norm_num <;> ring))

private theorem product_row0 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 0 j = productEntry a b 0 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row1 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 1 j = productEntry a b 1 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row2 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 2 j = productEntry a b 2 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row3 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 3 j = productEntry a b 3 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row4 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 4 j = productEntry a b 4 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row5 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 5 j = productEntry a b 5 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row6 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 6 j = productEntry a b 6 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row7 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 7 j = productEntry a b 7 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row8 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 8 j = productEntry a b 8 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row9 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 9 j = productEntry a b 9 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row10 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 10 j = productEntry a b 10 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row11 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 11 j = productEntry a b 11 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row12 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 12 j = productEntry a b 12 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row13 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 13 j = productEntry a b 13 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row14 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 14 j = productEntry a b 14 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row15 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 15 j = productEntry a b 15 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row16 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 16 j = productEntry a b 16 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row17 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 17 j = productEntry a b 17 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row18 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 18 j = productEntry a b 18 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row19 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 19 j = productEntry a b 19 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row20 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 20 j = productEntry a b 20 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row21 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 21 j = productEntry a b 21 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row22 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 22 j = productEntry a b 22 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row23 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 23 j = productEntry a b 23 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row24 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 24 j = productEntry a b 24 j := by
  fin_cases j <;> double_bond_product_entry
private theorem product_row25 {A : Type*} [CommRing A] (a b : A) (j : Fin 26) :
    wordEntry (commutatorWord a b) 25 j = productEntry a b 25 j := by
  fin_cases j <;> double_bond_product_entry

private theorem commutator_entries {A : Type*} [CommRing A] (a b : A) (i j : Fin 26) :
    wordEntry (commutatorWord a b) i j = productEntry a b i j := by
  fin_cases i
  · exact product_row0 a b j
  · exact product_row1 a b j
  · exact product_row2 a b j
  · exact product_row3 a b j
  · exact product_row4 a b j
  · exact product_row5 a b j
  · exact product_row6 a b j
  · exact product_row7 a b j
  · exact product_row8 a b j
  · exact product_row9 a b j
  · exact product_row10 a b j
  · exact product_row11 a b j
  · exact product_row12 a b j
  · exact product_row13 a b j
  · exact product_row14 a b j
  · exact product_row15 a b j
  · exact product_row16 a b j
  · exact product_row17 a b j
  · exact product_row18 a b j
  · exact product_row19 a b j
  · exact product_row20 a b j
  · exact product_row21 a b j
  · exact product_row22 a b j
  · exact product_row23 a b j
  · exact product_row24 a b j
  · exact product_row25 a b j

private theorem conjugateWord_prod {A : Type*} [CommRing A] (i j : Fin 4) (u : A) :
    ((conjugateWord i j u).reverse.map fun p =>
      rootSubgroupPoints p.1 A (Multiplicative.ofAdd p.2)).prod =
      weylRootSubgroupPoints [i, j] j A (Multiplicative.ofAdd u) := by
  rw [weylRootSubgroupPoints_cons, weylRootSubgroupPoints_singleton_self]
  simp [conjugateWord, simpleWeylPoint_def,
    mul_inv_rev, ← map_inv, ← ofAdd_neg, mul_assoc]

private theorem commutatorWord_prod {A : Type*} [CommRing A] (a b : A) :
    ((commutatorWord a b).reverse.map fun p =>
      rootSubgroupPoints p.1 A (Multiplicative.ofAdd p.2)).prod =
      ⁅rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd a),
        rootSubgroupPoints (.inr 2) A (Multiplicative.ofAdd b)⁆ := by
  simp [commutatorWord, commutatorElement_def, ← map_inv, ← ofAdd_neg, mul_assoc]

private theorem sum_entry {A : Type*} [CommRing A] (u : A) (i j : Fin 26) :
    ((weylRootSubgroupPoints [1, 2] 2 A (Multiplicative.ofAdd u) :
      Matrix.GeneralLinearGroup (Fin 26) A).val i j) = sumEntry u i j := by
  rw [← conjugateWord_prod, ← wordEntry_eq]
  exact (conjugate_entries u i j).1

private theorem highest_entry {A : Type*} [CommRing A] (u : A) (i j : Fin 26) :
    ((weylRootSubgroupPoints [2, 1] 1 A (Multiplicative.ofAdd u) :
      Matrix.GeneralLinearGroup (Fin 26) A).val i j) = highestEntry u i j := by
  rw [← conjugateWord_prod, ← wordEntry_eq]
  exact (conjugate_entries u i j).2

/-- The negative long-short double-bond commutator, normalized by the specified pinned Weyl
words. The short negative sum-root factor comes first. -/
theorem commutatorElement_rootSubgroupPoints_negative_doubleBond (A : Type v) [CommRing A]
    (a b : A) :
    ⁅rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd a),
      rootSubgroupPoints (.inr 2) A (Multiplicative.ofAdd b)⁆ =
      weylRootSubgroupPoints [1, 2] 2 A (Multiplicative.ofAdd (a * b)) *
        weylRootSubgroupPoints [2, 1] 1 A (Multiplicative.ofAdd (a * b ^ 2)) := by
  rw [← commutatorWord_prod]
  apply Subtype.ext
  apply Units.ext
  funext i j
  rw [← wordEntry_eq, commutator_entries, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  simp only [sum_entry, highest_entry, highestEntry, mul_add, mul_ite, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, mul_one]
  have hcollect (x y c : A) :
      x + (a * b ^ 2) * c * y = x + y * ((a * b ^ 2) * c) := by ring
  exact hcollect (sumEntry (a * b) i j)
    (sumEntry (a * b) i (highestTarget j)) (highestCoeff j : A)

/-- Reversing the negative simple-root commutator reverses the factors and negates both
parameters. -/
theorem commutatorElement_rootSubgroupPoints_negative_doubleBond_reverse (A : Type v)
    [CommRing A] (a b : A) :
    ⁅rootSubgroupPoints (.inr 2) A (Multiplicative.ofAdd b),
      rootSubgroupPoints (.inr 1) A (Multiplicative.ofAdd a)⁆ =
      weylRootSubgroupPoints [2, 1] 1 A (Multiplicative.ofAdd (-(a * b ^ 2))) *
        weylRootSubgroupPoints [1, 2] 2 A (Multiplicative.ofAdd (-(a * b))) := by
  rw [← commutatorElement_inv, commutatorElement_rootSubgroupPoints_negative_doubleBond]
  simp only [mul_inv_rev, ← map_inv, ← ofAdd_neg]

end TauCeti.F4ShortRoot
