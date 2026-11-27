/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdjoinRoot.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Weighted forward shifts

The forward shift with wrap entry `v` has `s`-th power equal to the scalar matrix of `v`,
including over a noncommutative ring. In a commutative ring, this matrix represents
multiplication by the root of `X ^ s - C v` in its power basis.
-/

public section

open Polynomial

namespace Matrix

/-- The forward shift with ones below the diagonal and wrap entry `v` at the top right. -/
def weightedShift {A : Type*} [Zero A] [One A] (s : ℕ) (v : A) :
    Matrix (Fin s) (Fin s) A :=
  Matrix.of fun i j => if (i : ℕ) = j + 1 then 1 else
    if (i : ℕ) = 0 ∧ (j : ℕ) + 1 = s then v else 0

/-- The entries of the weighted forward shift. -/
@[simp]
theorem weightedShift_apply {A : Type*} [Zero A] [One A] (s : ℕ) (v : A)
    (i j : Fin s) :
    weightedShift s v i j = if (i : ℕ) = j + 1 then 1 else
      if (i : ℕ) = 0 ∧ (j : ℕ) + 1 = s then v else 0 := by rfl

/-- The weighted shift represents multiplication by the root in the power basis. -/
theorem weightedShift_eq_toMatrix {R : Type*} [CommRing R] [Nontrivial R]
    (s : ℕ) [NeZero s] (v : R) :
    weightedShift s v = LinearMap.toMatrixAlgEquiv (AdjoinRoot.basisXPowSubC s v)
      (LinearMap.mulLeft R (AdjoinRoot.root (X ^ s - C v : R[X]))) := by
  symm
  ext i j
  rw [LinearMap.toMatrixAlgEquiv_apply,
    AdjoinRoot.basisXPowSubC_apply, LinearMap.mulLeft_apply, ← pow_succ']
  have hj : (j : ℕ) + 1 ≤ s := j.isLt
  rcases hj.lt_or_eq with h | h
  · rw [AdjoinRoot.basisXPowSubC_repr_root_pow _ _ ⟨j + 1, h⟩, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = j + 1
    · have h1 : (⟨j + 1, h⟩ : Fin s) = i := Fin.ext hi.symm
      simp only [weightedShift, Matrix.of_apply, ite_eq_left hi, ite_eq_left h1]
    · have h1 : (⟨j + 1, h⟩ : Fin s) ≠ i := fun h' => hi (congrArg Fin.val h').symm
      simp [weightedShift, h1, hi, h.ne]
  · rw [h, AdjoinRoot.basisXPowSubC_repr_root_pow_self, Finsupp.single_apply]
    rcases eq_or_ne i 0 with rfl | hi
    · simp [weightedShift, h, (NeZero.ne s).symm]
    · simp [weightedShift, h, hi, hi.symm, i.isLt.ne]

private theorem weightedShift_pow_comm {R : Type*} [CommRing R] [Nontrivial R]
    (s : ℕ) [NeZero s] (v : R) :
    weightedShift s v ^ s = Matrix.scalar (Fin s) v := by
  rw [weightedShift_eq_toMatrix, ← map_pow]
  have hp : LinearMap.mulLeft R (AdjoinRoot.root (X ^ s - C v : R[X])) ^ s =
      algebraMap R (Module.End R (AdjoinRoot (X ^ s - C v : R[X]))) v := by
    ext q
    simp [LinearMap.pow_mulLeft, ← AdjoinRoot.algebraMap_eq, ← Algebra.smul_def]
  rw [hp, AlgEquiv.commutes]
  rfl

/-- After one full turn, the forward shift is the scalar matrix of its wrap entry.
The entry ring need not be commutative. -/
theorem weightedShift_pow_card {A : Type*} [Ring A] (s : ℕ) (v : A) :
    weightedShift s v ^ s = Matrix.scalar (Fin s) v := by
  by_cases hs : s = 0
  · subst s
    ext i j
    exact Fin.elim0 i
  have : NeZero s := ⟨hs⟩
  let f : ℤ[X] →+* A := Polynomial.eval₂RingHom' (Int.castRingHom A) v
    (fun z => Int.cast_commute z v)
  have h := congrArg (fun M : Matrix (Fin s) (Fin s) ℤ[X] => M.map f)
    (weightedShift_pow_comm s (X : ℤ[X]))
  rw [Matrix.map_pow] at h
  have hm : (weightedShift s (X : ℤ[X])).map f = weightedShift s v := by
    ext i j
    simp only [weightedShift, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp [f]
  rw [hm] at h
  convert h using 1
  ext i j
  by_cases hij : i = j <;> simp [Matrix.scalar, Matrix.diagonal, Matrix.map_apply, f, hij]

/-- The weighted shift advances a supported column before wrapping. -/
theorem weightedShift_mul_single {A : Type*} [Semiring A] (s : ℕ)
    (v : A) (i j : Fin s) (h : (i : ℕ) + 1 < s) :
    weightedShift s v * Matrix.single i j 1 = Matrix.single ⟨i + 1, h⟩ j 1 := by
  ext k l
  by_cases hl : l = j
  · subst l
    simp only [Matrix.mul_single_apply_same, mul_one, weightedShift, Matrix.of_apply]
    by_cases hk : (k : ℕ) = i + 1
    · have hk' : k = ⟨i + 1, h⟩ := Fin.ext hk
      simp [hk']
    · have hk' : k ≠ ⟨i + 1, h⟩ := fun hh => hk (congrArg Fin.val hh)
      simp [Matrix.single, hk, h.ne, Ne.symm hk']
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl]
    simp [Matrix.single, Ne.symm hl]

/-- Right multiplication by the weighted shift moves support from column `j + 1` to column `j`. -/
theorem single_mul_weightedShift {A : Type*} [Semiring A] (s : ℕ)
    (v : A) (i j : Fin s) (h : (j : ℕ) + 1 < s) :
    Matrix.single i ⟨j + 1, h⟩ 1 * weightedShift s v = Matrix.single i j 1 := by
  ext k l
  by_cases hk : k = i
  · subst k
    simp only [Matrix.single_mul_apply_same, one_mul, weightedShift, Matrix.of_apply]
    by_cases hl : (l : ℕ) = j
    · have hl' : l = j := Fin.ext hl
      simp [hl']
    · have hl' : l ≠ j := fun hh => hl (congrArg Fin.val hh)
      simp [Matrix.single, Ne.symm hl, Ne.symm hl']
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hk]
    simp [Matrix.single, Ne.symm hk]

/-- Powers before the wrap send the zeroth diagonal unit to the corresponding column unit. -/
theorem weightedShift_pow_mul_single_zero {A : Type*} [Semiring A] (s : ℕ) [NeZero s]
    (v : A) (i : ℕ) (hi : i < s) :
    weightedShift s v ^ i * Matrix.single 0 0 1 = Matrix.single ⟨i, hi⟩ 0 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', mul_assoc, ih (by omega)]
    exact weightedShift_mul_single s v ⟨i, by omega⟩ 0 hi

/-- A supported row multiplied by its index power of the shift returns to column zero. -/
theorem single_mul_weightedShift_pow {A : Type*} [Semiring A] (s : ℕ) [NeZero s]
    (v : A) (k : Fin s) (i : ℕ) (hi : i < s) :
    Matrix.single k ⟨i, hi⟩ 1 * weightedShift s v ^ i = Matrix.single k 0 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', ← mul_assoc, single_mul_weightedShift s v k ⟨i, by omega⟩ hi]
    exact ih (by omega)

/-- Powers of an invertible weighted shift give the matrix units from the zeroth diagonal unit. -/
theorem weightedShift_pow_single_zero_mul_inv_pow {A : Type*} [Semiring A] (s : ℕ) [NeZero s]
    (v : A) (u : (Matrix (Fin s) (Fin s) A)ˣ) (hu : (u : _) = weightedShift s v)
    (i j : Fin s) :
    weightedShift s v ^ (i : ℕ) * Matrix.single 0 0 1 *
      (↑(u⁻¹ ^ (j : ℕ)) : Matrix (Fin s) (Fin s) A) = Matrix.single i j 1 := by
  apply (u ^ (j : ℕ)).isUnit.mul_right_cancel
  rw [mul_assoc, ← Units.val_mul, inv_pow, inv_mul_cancel,
    Units.val_one, mul_one]
  rw [Units.val_pow_eq_pow_val, hu, single_mul_weightedShift_pow s v i j j.isLt,
    weightedShift_pow_mul_single_zero s v i i.isLt]

end Matrix
