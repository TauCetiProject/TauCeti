/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.RootSubgroup
import Mathlib.Tactic.Module

/-!
# The double-bond Chevalley relation in the short-root F₄ carrier

At Bourbaki nodes `1` (long) and `2` (short), the commutator has two root factors,
with roots `α₁ + α₂` and `α₁ + 2α₂` in zero-based numbering. We normalize these
factors by the existing Weyl presentations `[1], 2` and `[2], 1`. With these
presentations their parameters are `a * b` and `-(a * b²)`, respectively.

The relations hold over every commutative ring, without inverting two. The integral
coefficient certificates below retain the divided square of the short-root generator,
so they also apply to nonreduced rings in characteristic two. They concern the explicit
toral-closure carrier, not an identification with an independently pinned group scheme.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.

The matrices and Weyl normalization are those of
`TauCeti.Algebra.Lie.F4.ShortRoot.Basic` and
`TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.RootSubgroup`.
-/

public section

open scoped Matrix commutatorElement

namespace TauCeti.F4ShortRoot

universe v

-- The three coefficient matrices of the two nonsimple root factors. They are
-- recorded separately to keep each integral certificate at default resource limits.
private def sumRootMatrix : Matrix (Fin 26) (Fin 26) ℤ :=
  Matrix.of fun a b =>
    if a = (![0, 1, 2, 1, 4, 2, 6, 7, 4, 9, 6, 11, 9, 9, 14, 15, 12, 17, 18, 15, 20,
      17, 22, 20, 22, 25] : Fin 26 → Fin 26) b then
      (![0, 0, 0, -1, 0, 1, 0, 0, -1, 0, 1, 0, 2, 1, 0, 0, -1, 0, 0, -1, 0,
        1, 0, -1, 1, 0] : Fin 26 → ℤ) b
    else 0

private def sumRootDividedSquare : Matrix (Fin 26) (Fin 26) ℤ :=
  Matrix.single 9 16 (-1)

private def highestRootMatrix : Matrix (Fin 26) (Fin 26) ℤ :=
  Matrix.of fun a b =>
    if a = (![0, 1, 2, 3, 4, 1, 6, 7, 8, 9, 4, 11, 12, 13, 9, 15, 11, 17, 18, 19, 20,
      15, 22, 23, 20, 25] : Fin 26 → Fin 26) b then
      (![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0,
        -1, 0, 0, -1, 0] : Fin 26 → ℤ) b
    else 0

private def weylMatrix (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℤ :=
  (1 + raisingMatrix i + raisingDividedSquareMatrix i) *
    (1 - loweringMatrix i + loweringDividedSquareMatrix i) *
    (1 + raisingMatrix i + raisingDividedSquareMatrix i)

private theorem weylMatrix_intertwining (j : Fin 2) :
    weylMatrix (![1, 2] j) * raisingMatrix (![2, 1] j) =
      (![sumRootMatrix, highestRootMatrix] j) * weylMatrix (![1, 2] j) ∧
    weylMatrix (![1, 2] j) * raisingDividedSquareMatrix (![2, 1] j) =
      (![sumRootDividedSquare, 0] j) * weylMatrix (![1, 2] j) := by
  fin_cases j <;>
    simp only [weylMatrix, ← Matrix.ext_iff, Matrix.mul_apply, Matrix.add_apply,
      Matrix.sub_apply, Matrix.one_apply, raisingMatrix_apply,
      loweringMatrix_apply, raisingDividedSquareMatrix_apply,
      loweringDividedSquareMatrix_apply] <;> decide +kernel

private theorem doubleBond_coefficients :
    raisingMatrix 1 * raisingMatrix 2 - raisingMatrix 2 * raisingMatrix 1 = sumRootMatrix ∧
    raisingMatrix 1 * raisingDividedSquareMatrix 2 -
        raisingDividedSquareMatrix 2 * raisingMatrix 1 =
      sumRootMatrix * raisingMatrix 2 - highestRootMatrix ∧
    raisingMatrix 1 * raisingMatrix 2 * raisingMatrix 1 = 0 ∧
    raisingMatrix 1 * raisingDividedSquareMatrix 2 * raisingMatrix 1 =
      -sumRootDividedSquare := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [← Matrix.ext_iff, Matrix.mul_apply, Matrix.sub_apply, Matrix.neg_apply,
      Matrix.zero_apply, raisingMatrix_apply, raisingDividedSquareMatrix_apply,
      sumRootMatrix, highestRootMatrix, sumRootDividedSquare, Matrix.of_apply] <;>
    decide +kernel

private theorem doubleBond_zero_products :
    sumRootMatrix * highestRootMatrix = 0 ∧
    sumRootDividedSquare * highestRootMatrix = 0 ∧
    sumRootMatrix * raisingDividedSquareMatrix 2 = 0 ∧
    highestRootMatrix * raisingMatrix 2 = 0 ∧
    highestRootMatrix * raisingDividedSquareMatrix 2 = 0 ∧
    sumRootDividedSquare * raisingMatrix 2 = 0 ∧
    sumRootDividedSquare * raisingDividedSquareMatrix 2 = 0 := by
  simp only [← Matrix.ext_iff, Matrix.mul_apply, Matrix.zero_apply, raisingMatrix_apply,
    raisingDividedSquareMatrix_apply]
  decide +kernel

private theorem coe_simpleWeylPoint_eq_weylMatrix (i : Fin 4)
    (A : Type v) [CommRing A] :
    ((simpleWeylPoint i A : Matrix.GeneralLinearGroup (Fin 26) A) :
      Matrix (Fin 26) (Fin 26) A) = (Int.castRingHom A).mapMatrix (weylMatrix i) := by
  rw [simpleWeylPoint_def]
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_inl,
    coe_rootSubgroupPoints_inr, toAdd_ofAdd, one_smul, one_pow, neg_one_sq, neg_one_smul]
  simp only [weylMatrix, map_mul, map_add, map_sub, map_one]
  simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom, sub_eq_add_neg]

private theorem coe_weylRootSubgroupPoints_doubleBond (j : Fin 2)
    (A : Type v) [CommRing A] (t : A) :
    ((weylRootSubgroupPoints [![1, 2] j] (![2, 1] j) A (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 26) A) : Matrix (Fin 26) (Fin 26) A) =
      1 + t • (Int.castRingHom A).mapMatrix (![sumRootMatrix, highestRootMatrix] j) +
        t ^ 2 • (Int.castRingHom A).mapMatrix (![sumRootDividedSquare, 0] j) := by
  let f : Matrix (Fin 26) (Fin 26) ℤ →+* Matrix (Fin 26) (Fin 26) A :=
    (Int.castRingHom A).mapMatrix
  obtain ⟨hE, hD⟩ := weylMatrix_intertwining j
  have hE' := congrArg f hE
  have hD' := congrArg f hD
  simp only [map_mul] at hE' hD'
  have hint :
      f (weylMatrix (![1, 2] j)) *
          (1 + t • f (raisingMatrix (![2, 1] j)) +
            t ^ 2 • f (raisingDividedSquareMatrix (![2, 1] j))) =
        (1 + t • f (![sumRootMatrix, highestRootMatrix] j) +
            t ^ 2 • f (![sumRootDividedSquare, 0] j)) *
          f (weylMatrix (![1, 2] j)) := by
    simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
      hE', hD']
  rw [weylRootSubgroupPoints_cons, weylRootSubgroupPoints_nil]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  rw [coe_rootSubgroupPoints_inl, coe_simpleWeylPoint_eq_weylMatrix]
  have hN := coe_simpleWeylPoint_eq_weylMatrix (![1, 2] j) A
  simp only [f, RingHom.mapMatrix_apply, Int.coe_castRingHom] at hint
  simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at hN ⊢
  simp only [toAdd_ofAdd]
  rw [hint, mul_assoc, ← hN, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

private theorem doubleBond_conjugation_matrix (A : Type v) [CommRing A] (a b : A) :
    (1 + a • (raisingMatrix 1).map (Int.cast : ℤ → A)) *
        (1 + b • (raisingMatrix 2).map (Int.cast : ℤ → A) +
          b ^ 2 • (raisingDividedSquareMatrix 2).map (Int.cast : ℤ → A)) *
        (1 - a • (raisingMatrix 1).map (Int.cast : ℤ → A)) =
      (1 + (a * b) • sumRootMatrix.map (Int.cast : ℤ → A) +
          (a * b) ^ 2 • sumRootDividedSquare.map (Int.cast : ℤ → A)) *
        (1 - (a * b ^ 2) • highestRootMatrix.map (Int.cast : ℤ → A)) *
        (1 + b • (raisingMatrix 2).map (Int.cast : ℤ → A) +
          b ^ 2 • (raisingDividedSquareMatrix 2).map (Int.cast : ℤ → A)) := by
  let f : Matrix (Fin 26) (Fin 26) ℤ →+* Matrix (Fin 26) (Fin 26) A :=
    (Int.castRingHom A).mapMatrix
  obtain ⟨hC, hL, hEFE, hEDE⟩ := doubleBond_coefficients
  obtain ⟨hCL, hSL, hCD, hLF, hLD, hSF, hSD⟩ := doubleBond_zero_products
  have hC' := congrArg f hC
  have hL' := congrArg f hL
  have hEFE' := congrArg f hEFE
  have hEDE' := congrArg f hEDE
  have hCL' := congrArg f hCL
  have hSL' := congrArg f hSL
  have hCD' := congrArg f hCD
  have hLF' := congrArg f hLF
  have hLD' := congrArg f hLD
  have hSF' := congrArg f hSF
  have hSD' := congrArg f hSD
  have hEE' := congrArg f (raisingMatrix_mul_self_of_lt_two 1 (by decide))
  simp only [map_mul, map_sub, map_neg, map_zero] at *
  have hconj :
      (1 + a • f (raisingMatrix 1)) *
          (1 + b • f (raisingMatrix 2) + b ^ 2 • f (raisingDividedSquareMatrix 2)) *
          (1 - a • f (raisingMatrix 1)) =
        (1 + (a * b) • f sumRootMatrix + (a * b) ^ 2 • f sumRootDividedSquare) *
          (1 - (a * b ^ 2) • f highestRootMatrix) *
          (1 + b • f (raisingMatrix 2) + b ^ 2 • f (raisingDividedSquareMatrix 2)) := by
    simp only [mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, smul_mul_assoc,
      mul_smul_comm, hEE', hEFE', hEDE', hCL', hSL', hCD', hLF',
      hLD', hSF', hSD', smul_zero, add_zero, sub_zero]
    rw [eq_add_of_sub_eq hC', eq_add_of_sub_eq hL']
    module
  simpa only [f, RingHom.mapMatrix_apply, Int.coe_castRingHom] using hconj

/-- The double-bond Chevalley relation, with the sum-root and highest-root
parameters normalized by the Weyl words `[1]` and `[2]`. -/
theorem commutatorElement_rootSubgroupPoints_one_two
    (A : Type v) [CommRing A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a),
      rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd b)⁆ =
      weylRootSubgroupPoints [1] 2 A (Multiplicative.ofAdd (a * b)) *
        weylRootSubgroupPoints [2] 1 A (Multiplicative.ofAdd (-(a * b ^ 2))) := by
  have hconj := doubleBond_conjugation_matrix A a b
  rw [commutatorElement_def, mul_inv_eq_iff_eq_mul, ← map_inv, ← ofAdd_neg]
  apply Subtype.ext
  apply Units.ext
  have hsum := coe_weylRootSubgroupPoints_doubleBond 0 A (a * b)
  have hhigh := coe_weylRootSubgroupPoints_doubleBond 1 A (-(a * b ^ 2))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hsum hhigh
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_rootSubgroupPoints_inl_of_lt_two 1 (by decide),
    coe_rootSubgroupPoints_inl, coe_rootSubgroupPoints_inl_of_lt_two 1 (by decide),
    hsum, hhigh]
  simpa only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, map_zero, smul_zero, add_zero, toAdd_ofAdd, neg_smul,
    sub_eq_add_neg, RingHom.mapMatrix_apply, Int.coe_castRingHom] using hconj

/-- Reversing the two simple-root inputs reverses the factor order and negates
both parameters in the double-bond relation. -/
theorem commutatorElement_rootSubgroupPoints_two_one
    (A : Type v) [CommRing A] (a b : A) :
    ⁅rootSubgroupPoints (.inl 2) A (Multiplicative.ofAdd b),
      rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd a)⁆ =
      weylRootSubgroupPoints [2] 1 A (Multiplicative.ofAdd (a * b ^ 2)) *
        weylRootSubgroupPoints [1] 2 A (Multiplicative.ofAdd (-(a * b))) := by
  rw [← commutatorElement_inv, commutatorElement_rootSubgroupPoints_one_two, mul_inv_rev]
  simp only [← map_inv, ← ofAdd_neg, neg_neg]

end TauCeti.F4ShortRoot
