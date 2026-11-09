/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic

/-!
# Negative-root Chevalley collection in the seven-dimensional G₂ carrier

The commutator of the two negative simple-root points is the ordered product of four
Weyl-conjugated root points. The conjugating words fix the signs of the nonsimple-root
parameters: in order of increasing height the parameters are `ab`, `a²b`, `-a³b`, and
`2a³b²`. The coefficient two is retained over arbitrary commutative rings.

`commutatorElement_rootSubgroupPoints_inr_zero_inr_one` states this group identity, not just an
identity of tangent vectors or selected matrix entries. The roots of the four factors
are `-(α₁+α₂)`, `-(2α₁+α₂)`, `-(3α₁+α₂)`, and `-(3α₁+2α₂)`.

The carrier and divided-power matrices are those of
`TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Basic`. No identification with an
independently pinned simply connected group is asserted here.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2 (Chevalley commutators).
* R. Steinberg, *Lectures on Chevalley Groups*, §§3 and 6 (root words and their signs).
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IX (numbering).
-/

public section

open scoped Matrix commutatorElement

namespace TauCeti.G2ShortRoot.IntegralToralClosure

universe v w

variable {A : Type v} [CommRing A]

private noncomputable def x (k : Fin 2 ⊕ Fin 2) (t : A) : points A :=
  rootSubgroupPoints k A (Multiplicative.ofAdd t)

private noncomputable def n (i : Fin 2) : points A :=
  x (.inl i) 1 * x (.inr i) (-1) * x (.inl i) 1

private theorem x_inv (k : Fin 2 ⊕ Fin 2) (t : A) : (x k t)⁻¹ = x k (-t) := by
  simp [x, ← map_inv]

private def simpleMatrix (k : Fin 2 ⊕ Fin 2) (t : A) : Matrix (Fin 7) (Fin 7) A :=
  1 + t • (Int.castRingHom A).mapMatrix (rootMatrix k) +
    t ^ 2 • (Int.castRingHom A).mapMatrix (rootDividedSquareMatrix k)

private theorem simpleMatrix_map {B : Type w} [CommRing B] (f : A →+* B)
    (k : Fin 2 ⊕ Fin 2) (t : A) :
    (simpleMatrix k t).map f = simpleMatrix k (f t) := by
  ext r s
  simp [simpleMatrix, Matrix.one_apply]

private theorem coe_x (k : Fin 2 ⊕ Fin 2) (t : A) :
    ((x k t : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      simpleMatrix k t := by
  simp only [x, coe_rootSubgroupPoints, toAdd_ofAdd, simpleMatrix,
    RingHom.mapMatrix_apply, Int.coe_castRingHom]

private def weylMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 1, 0, 0, 0, 0, 0;
       -1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, -1, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 0, -1, 0],
    !![1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, -1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, -1, 0, 0;
       0, 0, 0, 0, 0, 0, 1]] i

private theorem weylMatrix_eq (i : Fin 2) :
    simpleMatrix (.inl i) (1 : ℤ) * simpleMatrix (.inr i) (-1) *
      simpleMatrix (.inl i) 1 = weylMatrix i := by
  simp only [simpleMatrix, rootMatrix_inl, rootMatrix_inr,
    rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr]
  revert i
  decide +kernel

private theorem weylMatrix_transpose_eq (i : Fin 2) :
    simpleMatrix (.inl i) (-1 : ℤ) * simpleMatrix (.inr i) 1 *
      simpleMatrix (.inl i) (-1) = (weylMatrix i).transpose := by
  simp only [simpleMatrix, rootMatrix_inl, rootMatrix_inr,
    rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr]
  revert i
  decide +kernel

private theorem coe_n (i : Fin 2) :
    ((n (A := A) i : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) =
      (Int.castRingHom A).mapMatrix (weylMatrix i) := by
  have h := congrArg (fun M => M.map (Int.castRingHom A)) (weylMatrix_eq i)
  simpa only [n, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_x,
    Matrix.map_mul, simpleMatrix_map, map_one, map_neg, RingHom.mapMatrix_apply] using h

private theorem coe_n_inv (i : Fin 2) :
    ((((n (A := A) i)⁻¹ : points A) : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) =
      (Int.castRingHom A).mapMatrix (weylMatrix i).transpose := by
  have h := congrArg (fun M => M.map (Int.castRingHom A)) (weylMatrix_transpose_eq i)
  simpa only [n, mul_inv_rev, x_inv, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    coe_x, Matrix.map_mul, simpleMatrix_map, map_one, map_neg, neg_neg,
    RingHom.mapMatrix_apply, mul_assoc] using h

private def conjugator (i : Fin 4) : Matrix (Fin 7) (Fin 7) ℤ :=
  ![weylMatrix 1, weylMatrix 0 * weylMatrix 1,
    weylMatrix 0, weylMatrix 1 * weylMatrix 0] i

private def negativeRoot (i : Fin 4) : Fin 2 ⊕ Fin 2 :=
  .inr (if i < 2 then 0 else 1)

private def collectedLinear (i : Fin 4) : Matrix (Fin 7) (Fin 7) ℤ :=
  ![!![0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       -1, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, -2, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       -1, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, -2, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, -1, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 0;
       -1, 0, 0, 0, 0, 0, 0;
       0, -1, 0, 0, 0, 0, 0]] i

private def collectedSquare (i : Fin 4) : Matrix (Fin 7) (Fin 7) ℤ :=
  ![-Matrix.single 5 1 1, Matrix.single 6 0 1, 0, 0] i

private theorem conjugator_mul_transpose (i : Fin 4) :
    conjugator i * (conjugator i).transpose = 1 := by
  revert i
  decide +kernel

private theorem conjugator_rootMatrix (i : Fin 4) :
    conjugator i * rootMatrix (negativeRoot i) * (conjugator i).transpose =
      collectedLinear i := by
  simp only [negativeRoot, rootMatrix_inr]
  revert i
  decide +kernel

private theorem conjugator_rootDividedSquareMatrix (i : Fin 4) :
    conjugator i * rootDividedSquareMatrix (negativeRoot i) * (conjugator i).transpose =
      collectedSquare i := by
  simp only [negativeRoot, rootDividedSquareMatrix_inr]
  revert i
  decide +kernel

private def collectedMatrix (i : Fin 4) (t : A) : Matrix (Fin 7) (Fin 7) A :=
  1 + t • (Int.castRingHom A).mapMatrix (collectedLinear i) +
    t ^ 2 • (Int.castRingHom A).mapMatrix (collectedSquare i)

private theorem conjugate_matrix (i : Fin 4) (t : A) :
    (Int.castRingHom A).mapMatrix (conjugator i) * simpleMatrix (negativeRoot i) t *
        (Int.castRingHom A).mapMatrix (conjugator i).transpose = collectedMatrix i t := by
  simp only [simpleMatrix, collectedMatrix, mul_add, add_mul, mul_one,
    Matrix.mul_smul, Matrix.smul_mul, ← map_mul,
    conjugator_mul_transpose, conjugator_rootMatrix, conjugator_rootDividedSquareMatrix,
    map_one]

private noncomputable def conjugatorPoint (i : Fin 4) : points A :=
  ![n 1, n 0 * n 1, n 0, n 1 * n 0] i

private theorem coe_conjugatorPoint (i : Fin 4) :
    ((conjugatorPoint (A := A) i : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = (Int.castRingHom A).mapMatrix (conjugator i) := by
  fin_cases i <;>
    simp only [conjugatorPoint, conjugator, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_n, map_mul]

private theorem coe_conjugatorPoint_inv (i : Fin 4) :
    (((conjugatorPoint (A := A) i)⁻¹ : points A) :
      Matrix.GeneralLinearGroup (Fin 7) A).val =
        (Int.castRingHom A).mapMatrix (conjugator i).transpose := by
  fin_cases i <;>
    simp only [conjugatorPoint, conjugator, Matrix.cons_val_zero', Matrix.cons_val_succ',
      mul_inv_rev, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      coe_n_inv, Matrix.transpose_mul, map_mul]

private noncomputable def collectedPoint (i : Fin 4) (t : A) : points A :=
  conjugatorPoint i * x (negativeRoot i) t * (conjugatorPoint i)⁻¹

private theorem coe_collectedPoint (i : Fin 4) (t : A) :
    ((collectedPoint i t : Matrix.GeneralLinearGroup (Fin 7) A) :
      Matrix (Fin 7) (Fin 7) A) = collectedMatrix i t := by
  simp only [collectedPoint, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    coe_conjugatorPoint, coe_conjugatorPoint_inv, coe_x]
  exact conjugate_matrix i t

-- Keep the four-factor polynomial calculation separate from the constant conjugation
-- certificates. Row-sized proofs avoid re-elaborating all 49 entries in one declaration.
private def collectionEntry (a b : A) (r s : Fin 7) : Prop :=
  (simpleMatrix (.inr 0) a * simpleMatrix (.inr 1) b *
      simpleMatrix (.inr 0) (-a) * simpleMatrix (.inr 1) (-b)) r s =
    (collectedMatrix 0 (a * b) * collectedMatrix 1 (a ^ 2 * b) *
      collectedMatrix 2 (-(a ^ 3 * b)) * collectedMatrix 3 (2 * a ^ 3 * b ^ 2) :
        Matrix (Fin 7) (Fin 7) A) r s

local macro "collect_row " s:ident : tactic =>
  `(tactic| (unfold collectionEntry; fin_cases $(s):ident <;>
    norm_num [simpleMatrix, collectedMatrix, collectedLinear, collectedSquare,
      rootMatrix_inr, rootDividedSquareMatrix_inr, loweringMatrix_apply, Matrix.single_apply,
      Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.one_apply] <;> ring))

private theorem collection_row_zero (a b : A) (s : Fin 7) : collectionEntry a b 0 s := by
  collect_row s

private theorem collection_row_one (a b : A) (s : Fin 7) : collectionEntry a b 1 s := by
  collect_row s

private theorem collection_row_two (a b : A) (s : Fin 7) : collectionEntry a b 2 s := by
  collect_row s

private theorem collection_row_three (a b : A) (s : Fin 7) : collectionEntry a b 3 s := by
  collect_row s

private theorem collection_row_four (a b : A) (s : Fin 7) : collectionEntry a b 4 s := by
  collect_row s

private theorem collection_row_five (a b : A) (s : Fin 7) : collectionEntry a b 5 s := by
  collect_row s

private theorem collection_row_six (a b : A) (s : Fin 7) : collectionEntry a b 6 s := by
  collect_row s

/-- The negative-simple-root Chevalley commutator is the four root factors in increasing
height order. The actual pinned Weyl words specify the normalization of every factor. -/
theorem commutatorElement_rootSubgroupPoints_inr_zero_inr_one (A : Type v) [CommRing A] (a b : A) :
    let x := fun k t => rootSubgroupPoints k A (Multiplicative.ofAdd t)
    let n := fun i => x (.inl i) 1 * x (.inr i) (-1) * x (.inl i) 1
    ⁅x (.inr 0) a, x (.inr 1) b⁆ =
      (n 1 * x (.inr 0) (a * b) * (n 1)⁻¹) *
      ((n 0 * n 1) * x (.inr 0) (a ^ 2 * b) * (n 0 * n 1)⁻¹) *
      (n 0 * x (.inr 1) (-(a ^ 3 * b)) * (n 0)⁻¹) *
      ((n 1 * n 0) * x (.inr 1) (2 * a ^ 3 * b ^ 2) * (n 1 * n 0)⁻¹) := by
  suffices ⁅x (.inr 0) a, x (.inr 1) b⁆ =
      collectedPoint 0 (a * b) * collectedPoint 1 (a ^ 2 * b) *
      collectedPoint 2 (-(a ^ 3 * b)) * collectedPoint 3 (2 * a ^ 3 * b ^ 2) by
    -- Expand only the four indexed Weyl words, without using group simplification.
    simpa only [x, n, collectedPoint, conjugatorPoint, negativeRoot,
      Matrix.cons_val, Fin.reduceLT, ↓reduceIte] using this
  apply Subtype.ext
  apply Units.ext
  simp only [commutatorElement_def, x_inv, Subgroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul, coe_x, coe_collectedPoint]
  ext r s
  fin_cases r
  · exact collection_row_zero a b s
  · exact collection_row_one a b s
  · exact collection_row_two a b s
  · exact collection_row_three a b s
  · exact collection_row_four a b s
  · exact collection_row_five a b s
  · exact collection_row_six a b s

end TauCeti.G2ShortRoot.IntegralToralClosure
