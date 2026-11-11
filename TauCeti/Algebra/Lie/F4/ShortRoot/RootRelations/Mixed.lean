/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.RootSubgroup
public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The long–short simple-root commutator in the F₄ short-root carrier

At Bourbaki nodes 2 and 3 (indices 1 and 2), the commutator has two root factors.
We use the existing parametrizations obtained by conjugating the short root by the
long-root Weyl representative, and the long root by the short-root representative.
With these parametrizations their parameters are respectively `a * b` and `-(a * b²)`.
The signs refer to the actual integral pinning, not just the two abstract root lines.

The identities hold over every commutative ring, including rings with nilpotents.
The calculation retains the quadratic divided-square term of the short-root subgroup.
A sparse column recurrence computes entries of the actual root words, and finite
integral table calculations followed by polynomial identities verify the relation.

The carrier is not identified with the pinned simply connected group scheme of type F₄;
transfer to that group requires such an identification.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.

The formal inputs are the integral root and divided-square tables of
`TauCeti.F4ShortRoot.Basic` and the Weyl-transported root parametrizations of
`TauCeti.F4ShortRoot.Weyl.RootSubgroup`.
-/

public section

namespace TauCeti.F4ShortRoot

open scoped commutatorElement

universe v

noncomputable section

-- A letter is a signed simple node and an additive parameter. The recurrence reads
-- the list right-to-left, so adjoining a letter means multiplying on the right.
private def wordEntry {A : Type v} [CommRing A] :
    List ((Fin 4 ⊕ Fin 4) × A) → Fin 26 → Fin 26 → A
  | [], r, s => if r = s then 1 else 0
  | (k, t) :: l, r, s => wordEntry l r s +
      (if Sum.elim raisingCoeff loweringCoeff k s = 0 then 0 else
        t * (Sum.elim raisingCoeff loweringCoeff k s : A) *
          wordEntry l r (Sum.elim raisingTarget loweringTarget k s)) +
      (if Sum.elim raisingDividedSquareCoeff loweringDividedSquareCoeff k s = 0 then 0 else
        t ^ 2 * (Sum.elim raisingDividedSquareCoeff loweringDividedSquareCoeff k s : A) *
          wordEntry l r (Sum.elim raisingDividedSquareTarget loweringDividedSquareTarget k s))

private theorem wordEntry_eq {A : Type v} [CommRing A]
    (l : List ((Fin 4 ⊕ Fin 4) × A)) (r s : Fin 26) :
    wordEntry l r s =
      (((l.map fun kt => rootSubgroupPoints kt.1 A (Multiplicative.ofAdd kt.2)).reverse.prod :
          Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) r s := by
  induction l generalizing r s with
  | nil => simp [wordEntry, Matrix.one_apply]
  | cons kt l ih =>
    obtain ⟨k, t⟩ := kt
    simp only [wordEntry, List.map_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      coe_rootSubgroupPoints_eq, Matrix.mul_add,
      Matrix.mul_one, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simp only [ih]
    cases k with
    | inl i =>
      simp [Matrix.mul_apply, rootMatrix_inl, rootDividedSquareMatrix_inl,
        raisingMatrix_apply, raisingDividedSquareMatrix_apply, Matrix.map_apply,
        Finset.sum_ite_eq', mul_comm, mul_assoc]
      split_ifs <;> simp_all
    | inr i =>
      simp [Matrix.mul_apply, rootMatrix_inr, rootDividedSquareMatrix_inr,
        loweringMatrix_apply, loweringDividedSquareMatrix_apply, Matrix.map_apply,
        Finset.sum_ite_eq', mul_comm, mul_assoc]
      split_ifs <;> simp_all

-- Both sides are kept as words in the original numbered root subgroups.
private def commutatorWord {A : Type v} [CommRing A] (a b : A) :
    List ((Fin 4 ⊕ Fin 4) × A) :=
  [(.inl 2, -b), (.inl 1, -a), (.inl 2, b), (.inl 1, a)]

private def collectedWord {A : Type v} [CommRing A] (a b : A) :
    List ((Fin 4 ⊕ Fin 4) × A) :=
  [(.inl 2, -1), (.inr 2, 1), (.inl 2, -1),
    (.inl 1, -(a * b ^ 2)), (.inl 2, 1), (.inr 2, -1), (.inl 2, 1),
    (.inl 1, -1), (.inr 1, 1), (.inl 1, -1),
    (.inl 2, a * b), (.inl 1, 1), (.inr 1, -1), (.inl 1, 1)]

-- Columns are checked separately. Keeping the row symbolic lets polynomial
-- normalization collect coordinate-vector coefficients without twenty-six case splits.
local macro "check_mixed_column" : tactic =>
  `(tactic| (intro r <;>
    simp [commutatorWord, collectedWord, wordEntry, raisingTarget, raisingCoeff,
      loweringTarget, loweringCoeff, raisingDividedSquareTarget, raisingDividedSquareCoeff,
      loweringDividedSquareTarget, loweringDividedSquareCoeff, -mul_ite, -ite_mul] <;>
    ring))

private theorem wordEntry_column_0 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 0 = wordEntry (collectedWord a b) r 0 := by
  check_mixed_column

private theorem wordEntry_column_1 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 1 = wordEntry (collectedWord a b) r 1 := by
  check_mixed_column

private theorem wordEntry_column_2 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 2 = wordEntry (collectedWord a b) r 2 := by
  check_mixed_column

private theorem wordEntry_column_3 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 3 = wordEntry (collectedWord a b) r 3 := by
  check_mixed_column

private theorem wordEntry_column_4 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 4 = wordEntry (collectedWord a b) r 4 := by
  check_mixed_column

private theorem wordEntry_column_5 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 5 = wordEntry (collectedWord a b) r 5 := by
  check_mixed_column

private theorem wordEntry_column_6 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 6 = wordEntry (collectedWord a b) r 6 := by
  check_mixed_column

private theorem wordEntry_column_7 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 7 = wordEntry (collectedWord a b) r 7 := by
  check_mixed_column

private theorem wordEntry_column_8 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 8 = wordEntry (collectedWord a b) r 8 := by
  check_mixed_column

private theorem wordEntry_column_9 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 9 = wordEntry (collectedWord a b) r 9 := by
  check_mixed_column

private theorem wordEntry_column_10 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 10 = wordEntry (collectedWord a b) r 10 := by
  check_mixed_column

private theorem wordEntry_column_11 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 11 = wordEntry (collectedWord a b) r 11 := by
  check_mixed_column

private theorem wordEntry_column_12 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 12 = wordEntry (collectedWord a b) r 12 := by
  check_mixed_column

private theorem wordEntry_column_13 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 13 = wordEntry (collectedWord a b) r 13 := by
  check_mixed_column

private theorem wordEntry_column_14 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 14 = wordEntry (collectedWord a b) r 14 := by
  check_mixed_column

private theorem wordEntry_column_15 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 15 = wordEntry (collectedWord a b) r 15 := by
  check_mixed_column

private theorem wordEntry_column_16 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 16 = wordEntry (collectedWord a b) r 16 := by
  check_mixed_column

private theorem wordEntry_column_17 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 17 = wordEntry (collectedWord a b) r 17 := by
  check_mixed_column

private theorem wordEntry_column_18 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 18 = wordEntry (collectedWord a b) r 18 := by
  check_mixed_column

private theorem wordEntry_column_19 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 19 = wordEntry (collectedWord a b) r 19 := by
  check_mixed_column

private theorem wordEntry_column_20 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 20 = wordEntry (collectedWord a b) r 20 := by
  check_mixed_column

private theorem wordEntry_column_21 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 21 = wordEntry (collectedWord a b) r 21 := by
  check_mixed_column

private theorem wordEntry_column_22 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 22 = wordEntry (collectedWord a b) r 22 := by
  check_mixed_column

private theorem wordEntry_column_23 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 23 = wordEntry (collectedWord a b) r 23 := by
  check_mixed_column

private theorem wordEntry_column_24 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 24 = wordEntry (collectedWord a b) r 24 := by
  check_mixed_column

private theorem wordEntry_column_25 {A : Type v} [CommRing A] (a b : A) :
    ∀ r, wordEntry (commutatorWord a b) r 25 = wordEntry (collectedWord a b) r 25 := by
  check_mixed_column

private theorem wordEntry_commutator_eq_collected {A : Type v} [CommRing A]
    (a b : A) (r s : Fin 26) :
    wordEntry (commutatorWord a b) r s = wordEntry (collectedWord a b) r s := by
  fin_cases s
  · exact wordEntry_column_0 a b r
  · exact wordEntry_column_1 a b r
  · exact wordEntry_column_2 a b r
  · exact wordEntry_column_3 a b r
  · exact wordEntry_column_4 a b r
  · exact wordEntry_column_5 a b r
  · exact wordEntry_column_6 a b r
  · exact wordEntry_column_7 a b r
  · exact wordEntry_column_8 a b r
  · exact wordEntry_column_9 a b r
  · exact wordEntry_column_10 a b r
  · exact wordEntry_column_11 a b r
  · exact wordEntry_column_12 a b r
  · exact wordEntry_column_13 a b r
  · exact wordEntry_column_14 a b r
  · exact wordEntry_column_15 a b r
  · exact wordEntry_column_16 a b r
  · exact wordEntry_column_17 a b r
  · exact wordEntry_column_18 a b r
  · exact wordEntry_column_19 a b r
  · exact wordEntry_column_20 a b r
  · exact wordEntry_column_21 a b r
  · exact wordEntry_column_22 a b r
  · exact wordEntry_column_23 a b r
  · exact wordEntry_column_24 a b r
  · exact wordEntry_column_25 a b r

/-- The commutator at the long–short bond is the product of the transported
`α₂ + α₃` and `α₂ + 2α₃` root points, with their integral pinned signs. -/
theorem commutatorElement_rootSubgroupPoints_long_short (A : Type v) [CommRing A]
    (a b : A) :
    ⁅rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a),
        rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd b)⁆ =
      weylRootSubgroupPoints [1] 2 A (Multiplicative.ofAdd (a * b)) *
        weylRootSubgroupPoints [2] 1 A (Multiplicative.ofAdd (-(a * b ^ 2))) := by
  apply Subtype.ext
  apply Units.ext
  ext r s
  have h := wordEntry_commutator_eq_collected a b r s
  rw [wordEntry_eq, wordEntry_eq] at h
  simpa only [commutatorWord, collectedWord, List.map_cons, List.map_nil,
    List.reverse_cons, List.reverse_nil, List.prod_append, List.prod_cons,
    List.prod_nil, List.prod_singleton, mul_one, one_mul, commutatorElement_def,
    weylRootSubgroupPoints_apply, weylWordPoint_cons, weylWordPoint_nil,
    simpleWeylPoint_def, mul_inv_rev, inv_inv, ← map_inv,
    ← ofAdd_neg, neg_neg, mul_assoc, Subgroup.coe_mul,
    Subgroup.coe_inv, Subgroup.coe_one, Matrix.GeneralLinearGroup.coe_one,
    Matrix.GeneralLinearGroup.coe_mul] using h

/-- Reversing the simple-root commutator reverses its two root factors and negates
both parameters. -/
theorem commutatorElement_rootSubgroupPoints_short_long (A : Type v) [CommRing A]
    (a b : A) :
    ⁅rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd b),
        rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a)⁆ =
      weylRootSubgroupPoints [2] 1 A (Multiplicative.ofAdd (a * b ^ 2)) *
        weylRootSubgroupPoints [1] 2 A (Multiplicative.ofAdd (-(a * b))) := by
  simpa only [commutatorElement_inv, mul_inv_rev, ← map_inv, ← ofAdd_neg, neg_neg] using
    congrArg Inv.inv (commutatorElement_rootSubgroupPoints_long_short A a b)

end

end TauCeti.F4ShortRoot
