/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuaternionBasis
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Quaternion symbols with a square second parameter

This file constructs the explicit splitting of a quaternion symbol whose second parameter is a
square. For units `a` and `b` over a commutative ring in which two is invertible, the equivalence

```text
QuaternionAlgebra R a 0 b² ≃ₐ[R] Matrix (Fin 2) (Fin 2) R
```

sends its standard generators to

```text
i ↦ !![0, a; 1, 0],   j ↦ !![b, 0; 0, -b].
```

The formulas for the equivalence and its inverse are recorded entrywise, so later symbol
relations can use the splitting without unfolding the quaternion-basis implementation.

## Main definition

* `TauCeti.QuaternionAlgebra.secondSquareEquivMatrix`: the equivalence from the quaternion symbol
  `(a,b²)` to `Matrix (Fin 2) (Fin 2) R` for units `a` and `b`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter III, Section 2.11.
-/

public section

open scoped Matrix Quaternion

namespace TauCeti

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

private def secondSquareMatrixBasis (a b : R) :
    _root_.QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) R) a 0 (b ^ 2) where
  i := !![0, a; 1, 0]
  j := !![b, 0; 0, -b]
  k := !![0, -(a * b); b, 0]
  i_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  i_mul_j := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  j_mul_i := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    all_goals ring

omit [Invertible (2 : R)] in
private theorem secondSquareMatrixBasis_liftHom_apply (a b : Rˣ)
    (q : _root_.QuaternionAlgebra R (a : R) 0 ((b : R) ^ 2)) :
    (secondSquareMatrixBasis (a : R) (b : R)).liftHom q =
      !![q.re + (b : R) * q.imJ, (a : R) * q.imI - (a : R) * (b : R) * q.imK;
        q.imI + (b : R) * q.imK, q.re - (b : R) * q.imJ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [secondSquareMatrixBasis, _root_.QuaternionAlgebra.Basis.liftHom,
      _root_.QuaternionAlgebra.Basis.lift, Algebra.algebraMap_eq_smul_one] <;> ring

private def secondSquareMatrixInverse (a b : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    _root_.QuaternionAlgebra R (a : R) 0 ((b : R) ^ 2) :=
  ⟨⅟(2 : R) * (M 0 0 + M 1 1),
    ⅟(2 : R) * (((a⁻¹ : Rˣ) : R) * M 0 1 + M 1 0),
    ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * (M 0 0 - M 1 1)),
    ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) *
      (M 1 0 - ((a⁻¹ : Rˣ) : R) * M 0 1))⟩

private theorem invOf_two_mul_mul_two (x : R) : ⅟(2 : R) * (x * 2) = x := by
  calc
    ⅟(2 : R) * (x * 2) = (⅟(2 : R) * 2) * x := by ring
    _ = x := by rw [invOf_mul_self, one_mul]

private theorem secondSquareMatrixInverse_leftInverse (a b : Rˣ) :
    Function.LeftInverse (secondSquareMatrixInverse a b)
      (secondSquareMatrixBasis (a : R) (b : R)).liftHom := by
  intro q
  have hai : ((a⁻¹ : Rˣ) : R) * (a : R) = 1 := a.inv_val
  have hbi : ((b⁻¹ : Rˣ) : R) * (b : R) = 1 := b.inv_val
  rw [secondSquareMatrixBasis_liftHom_apply]
  ext
  · calc
      ⅟(2 : R) * ((q.re + (b : R) * q.imJ) + (q.re - (b : R) * q.imJ)) =
          ⅟(2 : R) * (q.re * 2) := by ring
      _ = q.re := invOf_two_mul_mul_two q.re
  · calc
      ⅟(2 : R) * (((a⁻¹ : Rˣ) : R) *
          ((a : R) * q.imI - (a : R) * (b : R) * q.imK) +
            (q.imI + (b : R) * q.imK)) = ⅟(2 : R) *
          (((a⁻¹ : Rˣ) : R) * (a : R) * q.imI -
            ((a⁻¹ : Rˣ) : R) * (a : R) * (b : R) * q.imK +
              q.imI + (b : R) * q.imK) := by ring
      _ = ⅟(2 : R) * (q.imI * 2) := by rw [hai]; ring
      _ = q.imI := invOf_two_mul_mul_two q.imI
  · calc
      ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) *
          ((q.re + (b : R) * q.imJ) - (q.re - (b : R) * q.imJ))) = ⅟(2 : R) *
          (((b⁻¹ : Rˣ) : R) * (b : R) * q.imJ * 2) := by ring
      _ = ⅟(2 : R) * (q.imJ * 2) := by rw [hbi, one_mul]
      _ = q.imJ := invOf_two_mul_mul_two q.imJ
  · calc
      ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) *
          ((q.imI + (b : R) * q.imK) - ((a⁻¹ : Rˣ) : R) *
            ((a : R) * q.imI - (a : R) * (b : R) * q.imK))) =
          ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) *
          (q.imI + (b : R) * q.imK -
            (((a⁻¹ : Rˣ) : R) * (a : R) * q.imI -
              ((a⁻¹ : Rˣ) : R) * (a : R) * (b : R) * q.imK))) := by ring
      _ = ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * ((b : R) * q.imK * 2)) := by
        rw [hai]
        ring
      _ = ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * (b : R) * q.imK * 2) := by ring
      _ = ⅟(2 : R) * (q.imK * 2) := by rw [hbi, one_mul]
      _ = q.imK := invOf_two_mul_mul_two q.imK

private theorem secondSquareMatrixInverse_rightInverse (a b : Rˣ) :
    Function.RightInverse (secondSquareMatrixInverse a b)
      (secondSquareMatrixBasis (a : R) (b : R)).liftHom := by
  intro M
  have ha : (a : R) * ((a⁻¹ : Rˣ) : R) = 1 := a.val_inv
  have hb : (b : R) * ((b⁻¹ : Rˣ) : R) = 1 := b.val_inv
  rw [secondSquareMatrixBasis_liftHom_apply]
  ext i j
  fin_cases i <;> fin_cases j
  · calc
      ⅟(2 : R) * (M 0 0 + M 1 1) +
          (b : R) * (⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * (M 0 0 - M 1 1))) =
          ⅟(2 : R) * (M 0 0 + M 1 1) +
          ((b : R) * ((b⁻¹ : Rˣ) : R)) * ⅟(2 : R) * (M 0 0 - M 1 1) := by ring
      _ = ⅟(2 : R) * (M 0 0 * 2) := by rw [hb, one_mul]; ring
      _ = M 0 0 := invOf_two_mul_mul_two (M 0 0)
  · calc
      (a : R) * (⅟(2 : R) * (((a⁻¹ : Rˣ) : R) * M 0 1 + M 1 0)) -
          (a : R) * (b : R) * (⅟(2 : R) * (((b⁻¹ : Rˣ) : R) *
            (M 1 0 - ((a⁻¹ : Rˣ) : R) * M 0 1))) =
          ((a : R) * ((a⁻¹ : Rˣ) : R)) * ⅟(2 : R) * M 0 1 +
          (a : R) * ⅟(2 : R) * M 1 0 -
          (a : R) * ((b : R) * ((b⁻¹ : Rˣ) : R)) * ⅟(2 : R) * M 1 0 +
          ((a : R) * ((a⁻¹ : Rˣ) : R)) *
            ((b : R) * ((b⁻¹ : Rˣ) : R)) * ⅟(2 : R) * M 0 1 := by ring
      _ = ⅟(2 : R) * (M 0 1 * 2) := by rw [ha, hb]; ring
      _ = M 0 1 := invOf_two_mul_mul_two (M 0 1)
  · calc
      ⅟(2 : R) * (((a⁻¹ : Rˣ) : R) * M 0 1 + M 1 0) +
          (b : R) * (⅟(2 : R) * (((b⁻¹ : Rˣ) : R) *
            (M 1 0 - ((a⁻¹ : Rˣ) : R) * M 0 1))) =
          ⅟(2 : R) * (((a⁻¹ : Rˣ) : R) * M 0 1 + M 1 0) +
          ((b : R) * ((b⁻¹ : Rˣ) : R)) * ⅟(2 : R) *
            (M 1 0 - ((a⁻¹ : Rˣ) : R) * M 0 1) := by ring
      _ = ⅟(2 : R) * (M 1 0 * 2) := by rw [hb, one_mul]; ring
      _ = M 1 0 := invOf_two_mul_mul_two (M 1 0)
  · calc
      ⅟(2 : R) * (M 0 0 + M 1 1) -
          (b : R) * (⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * (M 0 0 - M 1 1))) =
          ⅟(2 : R) * (M 0 0 + M 1 1) -
          ((b : R) * ((b⁻¹ : Rˣ) : R)) * ⅟(2 : R) * (M 0 0 - M 1 1) := by ring
      _ = ⅟(2 : R) * (M 1 1 * 2) := by rw [hb, one_mul]; ring
      _ = M 1 1 := invOf_two_mul_mul_two (M 1 1)

private theorem secondSquareMatrixBasis_liftHom_bijective (a b : Rˣ) :
    Function.Bijective (secondSquareMatrixBasis (a : R) (b : R)).liftHom := by
  exact ⟨(secondSquareMatrixInverse_leftInverse a b).injective,
    (secondSquareMatrixInverse_rightInverse a b).surjective⟩

/-- The explicit splitting of the symbol `(a,b²)` as `M₂(R)` for units `a` and `b` over a
commutative ring in which two is invertible. It sends the quaternion generators `i` and `j`
to `!![0, a; 1, 0]` and `!![b, 0; 0, -b]`, respectively. -/
noncomputable def secondSquareEquivMatrix (a b : Rˣ) :
    _root_.QuaternionAlgebra R (a : R) 0 ((b : R) ^ 2) ≃ₐ[R]
      Matrix (Fin 2) (Fin 2) R :=
  AlgEquiv.ofBijective (secondSquareMatrixBasis (a : R) (b : R)).liftHom
    (secondSquareMatrixBasis_liftHom_bijective a b)

/-- The splitting equivalence on an arbitrary quaternion. -/
@[simp]
theorem secondSquareEquivMatrix_apply (a b : Rˣ)
    (q : _root_.QuaternionAlgebra R (a : R) 0 ((b : R) ^ 2)) :
    secondSquareEquivMatrix a b q =
      !![q.re + (b : R) * q.imJ, (a : R) * q.imI - (a : R) * (b : R) * q.imK;
        q.imI + (b : R) * q.imK, q.re - (b : R) * q.imJ] := by
  rw [secondSquareEquivMatrix, AlgEquiv.ofBijective_apply,
    secondSquareMatrixBasis_liftHom_apply]

/-- The inverse splitting equivalence recovers the four quaternion coordinates from the four
matrix entries. -/
@[simp]
theorem secondSquareEquivMatrix_symm_apply (a b : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    (secondSquareEquivMatrix a b).symm M =
      ⟨⅟(2 : R) * (M 0 0 + M 1 1),
        ⅟(2 : R) * (((a⁻¹ : Rˣ) : R) * M 0 1 + M 1 0),
        ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) * (M 0 0 - M 1 1)),
        ⅟(2 : R) * (((b⁻¹ : Rˣ) : R) *
          (M 1 0 - ((a⁻¹ : Rˣ) : R) * M 0 1))⟩ := by
  change (secondSquareEquivMatrix a b).symm M = secondSquareMatrixInverse a b M
  apply (secondSquareEquivMatrix a b).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (secondSquareMatrixInverse_rightInverse a b M).symm

end QuaternionAlgebra

end TauCeti
