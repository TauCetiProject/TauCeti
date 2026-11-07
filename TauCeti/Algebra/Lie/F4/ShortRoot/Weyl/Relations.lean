/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Weyl.Basic
public import Mathlib.GroupTheory.Coxeter.Basic

/-!
# Braid relations for the short-root F₄ Weyl representatives

The pinned Weyl representatives in the twenty-six-dimensional short-root carrier satisfy
all the braid relations of the Bourbaki F₄ diagram, over every commutative ring. These
relations justify changing Weyl words by braid moves when transporting root subgroups.
They do not identify the carrier with the pinned simply connected group scheme.

The proof uses the root matrices and divided squares of
`TauCeti.Algebra.Lie.F4.ShortRoot.Basic`, followed by change of coefficients.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

open scoped Matrix

namespace TauCeti.F4ShortRoot

private def weylTarget : Fin 4 → Fin 26 → Fin 26 := ![
  ![0, 1, 2, 4, 3, 6, 5, 9, 8, 7, 10, 11, 12, 13, 14, 15, 18, 17, 16, 20, 19, 22, 21, 23, 24, 25],
  ![0, 1, 3, 2, 4, 5, 8, 7, 6, 11, 10, 9, 12, 13, 16, 15, 14, 19, 18, 17, 20, 21, 23, 22, 24, 25],
  ![0, 2, 1, 5, 6, 3, 4, 7, 10, 9, 8, 14, 12, 12, 11, 17, 16, 15, 18, 21, 22, 19, 20, 24, 23, 25],
  ![1, 0, 2, 3, 4, 7, 9, 5, 11, 6, 15, 8, 12, 13, 17, 10, 19, 14, 20, 16, 18, 21, 22, 23, 25, 24]]

private def weylCoeff : Fin 4 → Fin 26 → ℤ := ![
  ![1, 1, 1, -1, 1, -1, 1, -1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, 1, -1, 1, -1, 1, 1, 1, 1],
  ![1, 1, -1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, -1, 1, 1, -1, 1, 1, 1, 1, -1, 1, 1, 1],
  ![1, -1, 1, -1, -1, 1, 1, 1, -1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, -1, -1, 1, 1, -1, 1, 1],
  ![-1, 1, 1, 1, 1, -1, -1, 1, -1, 1, 1, 1, 1, -1, -1, 1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1]]

-- The extra entries record the two-dimensional zero-weight block, which is not monomial.
private def weylMatrix (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℤ :=
  Matrix.of fun a b ↦ (if a = weylTarget i b then weylCoeff i b else 0) +
    if i = 2 ∧ a = 13 ∧ b = 13 then 1 else
      if i = 3 ∧ a = 13 ∧ b = 12 then -1 else 0

private def positiveMatrix (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℤ :=
  Matrix.of fun a b ↦ (if a = b then 1 else 0) +
    (if a = raisingTarget i b then raisingCoeff i b else 0) +
    (if a = raisingDividedSquareTarget i b then raisingDividedSquareCoeff i b else 0)

private def negativeMatrix (i : Fin 4) : Matrix (Fin 26) (Fin 26) ℤ :=
  Matrix.of fun a b ↦ (if a = b then 1 else 0) -
    (if a = loweringTarget i b then loweringCoeff i b else 0) +
    (if a = loweringDividedSquareTarget i b then loweringDividedSquareCoeff i b else 0)

private theorem weylMatrix_certificate : ∀ i : Fin 4,
    positiveMatrix i * negativeMatrix i * positiveMatrix i = weylMatrix i := by
  decide +kernel

private theorem braid_certificate : ∀ i j : Fin 4,
    ((CoxeterSystem.braidWord CoxeterMatrix.F₄ i j).map weylMatrix).prod =
      ((CoxeterSystem.braidWord CoxeterMatrix.F₄ j i).map weylMatrix).prod := by
  decide +kernel

private theorem coe_simpleWeylPoint_int (i : Fin 4) :
    ((simpleWeylPoint i ℤ : Matrix.GeneralLinearGroup (Fin 26) ℤ) :
      Matrix (Fin 26) (Fin 26) ℤ) = weylMatrix i := by
  have hp : ((rootSubgroupPoints (.inl i) ℤ (Multiplicative.ofAdd 1) :
      Matrix.GeneralLinearGroup (Fin 26) ℤ) : Matrix (Fin 26) (Fin 26) ℤ) =
        positiveMatrix i := by
    rw [coe_rootSubgroupPoints_inl]
    ext a b
    simp [positiveMatrix, Matrix.one_apply]
  have hn : ((rootSubgroupPoints (.inr i) ℤ (Multiplicative.ofAdd (-1)) :
      Matrix.GeneralLinearGroup (Fin 26) ℤ) : Matrix (Fin 26) (Fin 26) ℤ) =
        negativeMatrix i := by
    rw [coe_rootSubgroupPoints_inr]
    ext a b
    simp [negativeMatrix, Matrix.one_apply, sub_eq_add_neg]
  simpa only [simpleWeylPoint_def, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    hp, hn] using weylMatrix_certificate i

private theorem coe_weylWordPoint_int (l : List (Fin 4)) :
    ((weylWordPoint l ℤ : Matrix.GeneralLinearGroup (Fin 26) ℤ) :
      Matrix (Fin 26) (Fin 26) ℤ) = (l.map weylMatrix).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [weylWordPoint_cons, Subgroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      coe_simpleWeylPoint_int, ih, List.map_cons, List.prod_cons]

/-- The pinned Weyl representatives satisfy every F₄ braid relation, including the
four-letter relation across the double bond. This holds over arbitrary commutative rings. -/
theorem weylWordPoint_braid (i j : Fin 4) (A : Type*) [CommRing A] :
    weylWordPoint (CoxeterSystem.braidWord CoxeterMatrix.F₄ i j) A =
      weylWordPoint (CoxeterSystem.braidWord CoxeterMatrix.F₄ j i) A := by
  have h : weylWordPoint (CoxeterSystem.braidWord CoxeterMatrix.F₄ i j) ℤ =
      weylWordPoint (CoxeterSystem.braidWord CoxeterMatrix.F₄ j i) ℤ := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_weylWordPoint_int, coe_weylWordPoint_int]
    exact braid_certificate i j
  have hmap := congrArg ((pointsPresentation ℤ).map (pointsPresentation A) (Int.castRingHom A)) h
  rw [map_weylWordPoint, map_weylWordPoint] at hmap
  exact hmap

end TauCeti.F4ShortRoot
