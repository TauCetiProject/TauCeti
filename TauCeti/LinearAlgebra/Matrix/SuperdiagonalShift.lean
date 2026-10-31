/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# The superdiagonal shift matrix

`TauCeti.superdiagonalShift n` is the nilpotent `n × n` matrix with ones on the superdiagonal and
zeros elsewhere. Subtracting a multiple of it from the identity gives an upper unitriangular
matrix, hence a unit, over any ring, and multiplying a row vector by `s • superdiagonalShift n`
moves each entry one place to the right, multiplied by `s` on the right.

## Main results

* `TauCeti.isUnit_one_sub_smul_superdiagonalShift`: `1 - s • superdiagonalShift n` is a unit.
* `TauCeti.vecMul_smul_superdiagonalShift_succ`: row multiplication by `s • superdiagonalShift`
  shifts entries to the right.
-/

public section

open Matrix

namespace TauCeti

variable {A : Type*}

section Shift

variable [Zero A] [One A]

/-- The nilpotent shift matrix of size `n`, with ones on the superdiagonal and zeros elsewhere. -/
def superdiagonalShift (n : ℕ) : Matrix (Fin n) (Fin n) A :=
  of fun i j => if (j : ℕ) = i + 1 then 1 else 0

/-- The entries of the superdiagonal shift. -/
theorem superdiagonalShift_apply (n : ℕ) (i j : Fin n) :
    superdiagonalShift n i j = if (j : ℕ) = i + 1 then (1 : A) else 0 :=
  (rfl)

/-- The last row of the superdiagonal shift vanishes. -/
@[simp]
theorem superdiagonalShift_last_apply (d : ℕ) (j : Fin (d + 1)) :
    superdiagonalShift (d + 1) (Fin.last d) j = (0 : A) := by
  rw [superdiagonalShift_apply, ite_eq_right_iff]
  intro h
  have := j.isLt
  simp only [Fin.val_last] at h
  omega

end Shift

section Semiring

variable [Semiring A] {d : ℕ}

/-- Row multiplication by a multiple of the superdiagonal shift: the first entry vanishes. -/
theorem vecMul_smul_superdiagonalShift_zero (v : Fin (d + 1) → A) (s : A) :
    (v ᵥ* (s • superdiagonalShift (d + 1))) 0 = 0 := by
  simp [vecMul, dotProduct, superdiagonalShift_apply]

/-- Row multiplication by a multiple of the superdiagonal shift moves each entry one place to
the right. -/
theorem vecMul_smul_superdiagonalShift_succ (v : Fin (d + 1) → A) (s : A) (j : Fin d) :
    (v ᵥ* (s • superdiagonalShift (d + 1))) j.succ = v j.castSucc * s := by
  simp only [vecMul, dotProduct, Matrix.smul_apply, superdiagonalShift_apply, Fin.val_succ,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_eq_single j.castSucc fun k hk ↦ ite_eq_right_iff.2 fun h ↦ absurd ?_ hk]
  · simp
  · rw [Fin.ext_iff, Fin.val_castSucc]
    omega

end Semiring

section Ring

variable [Ring A]

/-- Subtracting a multiple of the superdiagonal shift from the identity gives an upper
unitriangular matrix. -/
theorem isUpperUnitriangular_one_sub_smul_superdiagonalShift (n : ℕ) (s : A) :
    Matrix.IsUpperUnitriangular (1 - s • superdiagonalShift n : Matrix (Fin n) (Fin n) A) := by
  refine (isUpperUnitriangular_def _).2 ⟨fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · have hne : i ≠ j := fun h ↦ (lt_irrefl _ (h ▸ hij))
    have hij' : (j : ℕ) < i := hij
    simp [superdiagonalShift_apply, one_apply, hne, show (j : ℕ) ≠ i + 1 by omega]
  · simp [superdiagonalShift_apply]

/-- Subtracting a multiple of the superdiagonal shift from the identity gives a unit. -/
theorem isUnit_one_sub_smul_superdiagonalShift (n : ℕ) (s : A) :
    IsUnit (1 - s • superdiagonalShift n : Matrix (Fin n) (Fin n) A) := by
  have h := (isUpperUnitriangular_one_sub_smul_superdiagonalShift n s).isNilpotent_sub_one
  rw [← sub_add_cancel (1 - s • superdiagonalShift n) 1]
  exact h.isUnit_add_one

end Ring

end TauCeti
