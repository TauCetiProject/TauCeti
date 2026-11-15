/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic
import Mathlib.Tactic.Ring

/-!
# Positive-root collection in the seven-dimensional G₂ carrier

`commutatorElement_positive_simple_eq_root_product` collects the commutator of the two
positive simple-root points into four root-subgroup factors, ordered by increasing height.
The nonsimple root parameters are normalized by actual opposite-root words, not by an
independent choice of root vectors. With `nᵢ = xᵢ(1)x₋ᵢ(-1)xᵢ(1)`, the conjugating words are
`n₂`, `n₁n₂`, `n₁`, and `n₂n₁`; the corresponding roots are α₁+α₂, 2α₁+α₂,
3α₁+α₂, and 3α₁+2α₂. Their parameters are respectively `-ab`, `a²b`, `a³b`, and `2a³b²`.

The formula holds over arbitrary commutative rings, with the divided-square terms retained.
It supplies the triple-bond collection relation for the explicit carrier. It does not identify
that carrier with an independently constructed pinned simply connected group scheme.

The calculation uses the integral root matrices of `G2ShortRoot.AdmissibleLattice` and their
faithful point realization in `IntegralToralClosure.Basic`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6.
-/

public section

namespace TauCeti.G2ShortRoot.IntegralToralClosure

open _root_.Matrix
open scoped commutatorElement

universe v

private def rootPolynomial {A : Type*} [CommRing A] (k : Fin 2 ⊕ Fin 2) (t : A) :
    Matrix (Fin 7) (Fin 7) A :=
  1 + t • (rootMatrix k).map (Int.cast : ℤ → A) +
    t ^ 2 • (rootDividedSquareMatrix k).map (Int.cast : ℤ → A)

private def weylMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  rootPolynomial (.inl i) 1 * rootPolynomial (.inr i) (-1) * rootPolynomial (.inl i) 1

private def inverseWeylMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  rootPolynomial (.inl i) (-1) * rootPolynomial (.inr i) 1 * rootPolynomial (.inl i) (-1)

private def conjugator : Fin 4 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![weylMatrix 1, weylMatrix 0 * weylMatrix 1, weylMatrix 0, weylMatrix 1 * weylMatrix 0]

private def inverseConjugator : Fin 4 → Matrix (Fin 7) (Fin 7) ℤ :=
  ![inverseWeylMatrix 1, inverseWeylMatrix 1 * inverseWeylMatrix 0,
    inverseWeylMatrix 0, inverseWeylMatrix 0 * inverseWeylMatrix 1]

private def rootNode : Fin 4 → Fin 2 ⊕ Fin 2 := ![.inl 0, .inl 0, .inl 1, .inl 1]

private def collectedGenerator (j : Fin 4) : Matrix (Fin 7) (Fin 7) ℤ :=
  conjugator j * rootMatrix (rootNode j) * inverseConjugator j

private def collectedDividedSquare (j : Fin 4) : Matrix (Fin 7) (Fin 7) ℤ :=
  conjugator j * rootDividedSquareMatrix (rootNode j) * inverseConjugator j

private def collectedPolynomial {A : Type*} [CommRing A] (j : Fin 4) (t : A) :
    Matrix (Fin 7) (Fin 7) A :=
  1 + t • (collectedGenerator j).map (Int.cast : ℤ → A) +
    t ^ 2 • (collectedDividedSquare j).map (Int.cast : ℤ → A)

private theorem collectedGenerator_table : collectedGenerator = ![
    -single 0 2 1 + 2 • single 1 3 1 - single 3 5 1 + single 4 6 1,
    -(2 • single 0 3 1) + single 1 4 1 + single 2 5 1 - single 3 6 1,
    single 0 4 1 - single 2 6 1,
    -single 0 5 1 - single 1 6 1] := by
  funext j
  fin_cases j <;>
    simp only [collectedGenerator, conjugator, inverseConjugator, weylMatrix,
      inverseWeylMatrix, rootPolynomial, rootNode, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      rootMatrix_inl, rootMatrix_inr, rootDividedSquareMatrix_inl,
      rootDividedSquareMatrix_inr] <;> decide +kernel

private theorem collectedDividedSquare_table :
    collectedDividedSquare = ![-single 1 5 1, single 0 6 1, 0, 0] := by
  funext j
  fin_cases j <;>
    simp only [collectedDividedSquare, conjugator, inverseConjugator, weylMatrix,
      inverseWeylMatrix, rootPolynomial, rootNode, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      rootMatrix_inl, rootMatrix_inr, rootDividedSquareMatrix_inl,
      rootDividedSquareMatrix_inr] <;> decide +kernel

private theorem conjugator_mul_inverse (j : Fin 4) :
    conjugator j * inverseConjugator j = 1 := by
  fin_cases j <;>
    simp only [conjugator, inverseConjugator, weylMatrix, inverseWeylMatrix, rootPolynomial,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, rootMatrix_inl, rootMatrix_inr, rootDividedSquareMatrix_inl,
      rootDividedSquareMatrix_inr] <;> decide +kernel

private theorem conjugate_rootPolynomial {A : Type*} [CommRing A] (j : Fin 4) (t : A) :
    (conjugator j).map (Int.castRingHom A) * rootPolynomial (rootNode j) t *
      (inverseConjugator j).map (Int.castRingHom A) = collectedPolynomial j t := by
  simp only [rootPolynomial, collectedPolynomial, ← Int.coe_castRingHom, mul_add, add_mul,
    mul_one, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, conjugator_mul_inverse,
    collectedGenerator, collectedDividedSquare]
  simp

-- Each scalar identity is stated before the finite entry calculation uses it.
private theorem collection_scalar_certificate {A : Type*} [CommRing A] (a b : A) :
    a * b * (a * 2) = a ^ 2 * b * 2 ∧
    a * b * a ^ 2 = a ^ 3 * b ∧
    -(a * b * a ^ 2 * b) = -(2 * a ^ 3 * b ^ 2) + a * b * (a ^ 2 * b) ∧
    0 = -(a * b * (a ^ 3 * b)) + (a ^ 2 * b) ^ 2 ∧
    b * (a * 2) = a * b * 2 ∧
    b * a ^ 2 = a ^ 2 * b ∧
    b * a ^ 2 * b = (a * b) ^ 2 ∧
    0 = -(2 * a ^ 3 * b ^ 2) + a * b * 2 * (a ^ 2 * b) ∧
    a ^ 2 + (-(a * 2 * a) + a ^ 2) = 0 ∧
    a ^ 2 * b * a = a ^ 3 * b ∧
    a * b * a = a ^ 2 * b :=
  ⟨by ring, by ring, by ring, by ring, by ring, by ring,
    by ring, by ring, by ring, by ring, by ring⟩

private def collectionLeft {A : Type*} [CommRing A] (a b : A) : Matrix (Fin 7) (Fin 7) A :=
  rootPolynomial (.inl 0) a * rootPolynomial (.inl 1) b *
    rootPolynomial (.inl 0) (-a) * rootPolynomial (.inl 1) (-b)

private def collectionRight {A : Type*} [CommRing A] (a b : A) : Matrix (Fin 7) (Fin 7) A :=
  collectedPolynomial 0 (-a * b) * collectedPolynomial 1 (a ^ 2 * b) *
    collectedPolynomial 2 (a ^ 3 * b) * collectedPolynomial 3 (2 * a ^ 3 * b ^ 2)

-- Splitting the seven rows keeps the finite matrix certificate within the default elaboration
-- budget. This local tactic shares only the entry expansion and the explicitly stated scalars.
local macro "check_collection_row" a:ident b:ident j:ident : tactic => `(tactic| (
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    collection_scalar_certificate $a $b
  fin_cases $j:term <;>
    norm_num [collectionLeft, collectionRight, rootPolynomial, collectedPolynomial,
      collectedGenerator_table, collectedDividedSquare_table, rootMatrix_inl, rootMatrix_inr,
      rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr, raisingMatrix_apply,
      loweringMatrix_apply, raisingCoefficient_apply, loweringCoefficient_apply,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.single, Matrix.one_apply]
  all_goals first | assumption | exact mul_comm _ _ | exact mul_eq_zero_of_left h9 $b))

private theorem collection_row_zero {A : Type*} [CommRing A] (a b : A) (j : Fin 7) :
    collectionLeft a b 0 j = collectionRight a b 0 j := by check_collection_row a b j

private theorem collection_row_one {A : Type*} [CommRing A] (a b : A) (j : Fin 7) :
    collectionLeft a b 1 j = collectionRight a b 1 j := by check_collection_row a b j

private theorem collection_row_two {A : Type*} [CommRing A] (a b : A) (j : Fin 7) :
    collectionLeft a b 2 j = collectionRight a b 2 j := by check_collection_row a b j

private theorem collection_row_three {A : Type*} [CommRing A] (a b : A) (j : Fin 7) :
    collectionLeft a b 3 j = collectionRight a b 3 j := by check_collection_row a b j

private theorem collection_row_four {A : Type*} [CommRing A] (a b : A) (j : Fin 7) :
    collectionLeft a b 4 j = collectionRight a b 4 j := by check_collection_row a b j

private theorem collection_row_five {A : Type*} [CommRing A] (a b : A) (j : Fin 7) :
    collectionLeft a b 5 j = collectionRight a b 5 j := by check_collection_row a b j

private theorem collection_row_six {A : Type*} [CommRing A] (a b : A) (j : Fin 7) :
    collectionLeft a b 6 j = collectionRight a b 6 j := by check_collection_row a b j

private theorem collection_matrix {A : Type*} [CommRing A] (a b : A) :
    collectionLeft a b = collectionRight a b := by
  ext i j
  fin_cases i
  · exact collection_row_zero a b j
  · exact collection_row_one a b j
  · exact collection_row_two a b j
  · exact collection_row_three a b j
  · exact collection_row_four a b j
  · exact collection_row_five a b j
  · exact collection_row_six a b j

private theorem map_rootPolynomial (k : Fin 2 ⊕ Fin 2) (t : ℤ)
    (A : Type v) [CommRing A] :
    (rootPolynomial k t).map (Int.castRingHom A) = rootPolynomial k (t : A) := by
  ext i j
  simp only [rootPolynomial, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Int.cast_id]
  simp [Matrix.one_apply]

private noncomputable def weylPoint (i : Fin 2) (A : Type v) [CommRing A] : points A :=
  rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1) *
    rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) *
    rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd 1)

private noncomputable def conjugatingPoint (j : Fin 4) (A : Type v) [CommRing A] : points A :=
  ![weylPoint 1 A, weylPoint 0 A * weylPoint 1 A,
    weylPoint 0 A, weylPoint 1 A * weylPoint 0 A] j

private noncomputable def conjugatedPoint (j : Fin 4) (A : Type v) [CommRing A]
    (t : A) : points A :=
  conjugatingPoint j A * rootSubgroupPoints (rootNode j) A (Multiplicative.ofAdd t) *
    (conjugatingPoint j A)⁻¹

private theorem coe_weylPoint (i : Fin 2) (A : Type v) [CommRing A] :
    ((weylPoint i A : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      (weylMatrix i).map (Int.castRingHom A) := by
  simp only [weylPoint, Subgroup.coe_mul, Units.val_mul, weylMatrix, Matrix.map_mul,
    map_rootPolynomial]
  simp only [Int.cast_one, Int.cast_neg, coe_rootSubgroupPoints, toAdd_ofAdd, rootPolynomial]

private theorem coe_conjugatingPoint (j : Fin 4) (A : Type v) [CommRing A] :
    ((conjugatingPoint j A : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = (conjugator j).map (Int.castRingHom A) := by
  fin_cases j <;>
    simp [conjugatingPoint, conjugator, Subgroup.coe_mul, Units.val_mul, coe_weylPoint] <;>
    simp only [← Int.coe_castRingHom, Matrix.map_mul]

private theorem coe_conjugatedPoint (j : Fin 4) (A : Type v) [CommRing A] (t : A) :
    ((conjugatedPoint j A t : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = collectedPolynomial j t := by
  have hinv : (((conjugatingPoint j A)⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = (inverseConjugator j).map (Int.castRingHom A) := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [coe_conjugatingPoint, ← Matrix.map_mul, conjugator_mul_inverse]
    simp
  -- `rootPolynomial` is precisely the divided-power matrix in `coe_rootSubgroupPoints`.
  have hroot := coe_rootSubgroupPoints (rootNode j) A (Multiplicative.ofAdd t)
  simp only [toAdd_ofAdd] at hroot
  simp only [conjugatedPoint, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
  rw [coe_conjugatingPoint, hinv, hroot]
  exact conjugate_rootPolynomial j t

/-- **The positive-simple-root Chevalley collection formula in type G₂.** The four factors
are normalized by the displayed Weyl words and ordered as α₁+α₂, 2α₁+α₂, 3α₁+α₂,
3α₁+2α₂. No invertibility, characteristic or reducedness condition on the coefficients is needed. -/
theorem commutatorElement_positive_simple_eq_root_product
    (A : Type v) [CommRing A] (a b : A) :
    let x := fun (i : Fin 2) (t : A) ↦ rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd t)
    let n := fun i ↦ x i 1 * rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (-1)) * x i 1
    ⁅x 0 a, x 1 b⁆ =
      (n 1 * x 0 (-a * b) * (n 1)⁻¹) *
      ((n 0 * n 1) * x 0 (a ^ 2 * b) * (n 0 * n 1)⁻¹) *
      (n 0 * x 1 (a ^ 3 * b) * (n 0)⁻¹) *
      ((n 1 * n 0) * x 1 (2 * a ^ 3 * b ^ 2) * (n 1 * n 0)⁻¹) := by
  -- The four explicit conjugating words are exactly the four entries of `conjugatingPoint`.
  have h : ⁅rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd a),
      rootSubgroupPoints (.inl 1) A (Multiplicative.ofAdd b)⁆ =
      conjugatedPoint 0 A (-a * b) * conjugatedPoint 1 A (a ^ 2 * b) *
        conjugatedPoint 2 A (a ^ 3 * b) * conjugatedPoint 3 A (2 * a ^ 3 * b ^ 2) := by
    apply Subtype.ext
    apply Units.ext
    simp only [commutatorElement_def, ← map_inv, ← ofAdd_neg, Subgroup.coe_mul, Units.val_mul,
      coe_rootSubgroupPoints, toAdd_ofAdd, coe_conjugatedPoint]
    exact collection_matrix a b
  simpa [conjugatedPoint, conjugatingPoint, rootNode, weylPoint] using h

end TauCeti.G2ShortRoot.IntegralToralClosure
