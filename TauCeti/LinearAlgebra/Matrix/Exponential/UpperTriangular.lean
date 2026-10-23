/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.Triangular
public import TauCeti.RingTheory.Nilpotent.Log

/-!
# Finite exponential and logarithm of triangular matrices

The finite exponential carries strictly upper-triangular matrices to upper-unitriangular
matrices. The finite logarithm carries upper-unitriangular matrices to strictly
upper-triangular matrices. These results let the finite exponential/logarithm identities be
restricted to these matrix spaces over rational algebras, including nonreduced algebras.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), §17.
-/

public section

namespace Matrix

open Finset

variable {R m : Type*} [Ring R] [Module ℚ R] [Fintype m] [LinearOrder m]

/-- The finite exponential of a strictly upper-triangular matrix is upper unitriangular. -/
theorem IsUpperTriangular.isUpperUnitriangular_exp {M : Matrix m m R}
    (hM : M.IsUpperTriangular) (hdiag : ∀ i, M i i = 0) :
    (IsNilpotent.exp M).IsUpperUnitriangular := by
  classical
  have hpow := pow_card_eq_zero_of_isUpperTriangular_of_diag_eq_zero hM hdiag
  rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_succ _) hpow)]
  rw [isUpperUnitriangular_def]
  refine ⟨?_, ?_⟩
  · intro i j hji
    simp only [sum_apply, smul_apply]
    exact sum_eq_zero fun k _ ↦ by rw [(hM.pow k) hji, smul_zero]
  · intro i
    simp only [sum_apply, smul_apply, pow_apply_diag_of_isUpperTriangular hM, hdiag i]
    simp [zero_pow_eq]

/-- The finite exponential of an upper-unitriangular matrix minus one is upper unitriangular. -/
theorem IsUpperUnitriangular.isUpperUnitriangular_exp_sub_one {M : Matrix m m R}
    (hM : M.IsUpperUnitriangular) : (IsNilpotent.exp (M - 1)).IsUpperUnitriangular :=
  hM.isUpperTriangular_sub_one.isUpperUnitriangular_exp hM.sub_one_apply_diag

/-- The finite logarithm of an upper-unitriangular matrix is upper triangular. -/
theorem IsUpperUnitriangular.isUpperTriangular_log {M : Matrix m m R}
    (hM : M.IsUpperUnitriangular) : (IsNilpotent.log M).IsUpperTriangular := by
  classical
  rw [IsNilpotent.log_def]
  intro i j hji
  simp only [sum_apply, smul_apply]
  exact sum_eq_zero fun k _ ↦ by
    rw [(hM.isUpperTriangular_sub_one.pow k) hji, smul_zero]

/-- The diagonal of the finite logarithm of an upper-unitriangular matrix vanishes. -/
@[simp]
theorem IsUpperUnitriangular.log_apply_diag {M : Matrix m m R}
    (hM : M.IsUpperUnitriangular) (i : m) : IsNilpotent.log M i i = 0 := by
  classical
  rw [IsNilpotent.log_def]
  simp only [sum_apply, smul_apply,
    pow_apply_diag_of_isUpperTriangular hM.isUpperTriangular_sub_one,
    hM.sub_one_apply_diag]
  apply sum_eq_zero
  intro k _
  by_cases hk : k = 0 <;> simp [hk]

end Matrix
