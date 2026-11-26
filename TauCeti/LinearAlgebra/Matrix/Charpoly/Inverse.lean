/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Inverses of matrices lying in a subalgebra

By the Cayley–Hamilton theorem, an invertible square matrix `A` over a commutative ring satisfies
`A * q(A) = -χ_A(0) • 1`, where `χ_A = X * q + χ_A(0)` and `χ_A(0) = ± det A` is a unit. Hence
`A⁻¹` is a polynomial in `A`, and every subalgebra of `Matrix n n R` containing `A` contains `A⁻¹`
(`Matrix.nonsing_inv_mem`). This holds for a matrix with nonunit determinant too, whose
`Matrix.nonsing_inv` is `0`. So a subalgebra of `Matrix n n R` is closed under inversion, and its
invertible elements form a subgroup of `GL n R` described by membership of the matrix alone.
-/

public section

namespace Matrix

open Polynomial

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **Subalgebras of a matrix algebra are closed under inversion.** If `A` lies in a subalgebra
`S` of `Matrix n n R`, so does `A⁻¹`: by the Cayley–Hamilton theorem it is a polynomial in `A`
when `det A` is a unit, and it is `0` otherwise. -/
theorem nonsing_inv_mem {S : Subalgebra R (Matrix n n R)} {A : Matrix n n R} (hA : A ∈ S) :
    A⁻¹ ∈ S := by
  by_cases h : IsUnit A.det
  · -- Write `χ_A = X * q + C c` with `c = χ_A(0)`; Cayley–Hamilton gives `A * q(A) = -c • 1`.
    set c := A.charpoly.coeff 0
    set q := A.charpoly.divX
    have hq : A * aeval A q = (-c) • 1 := by
      have := congrArg (aeval A) (X_mul_divX_add A.charpoly)
      rw [aeval_self_charpoly, map_add, map_mul, aeval_X, aeval_C,
        Algebra.algebraMap_eq_smul_one] at this
      rw [neg_smul, eq_neg_iff_add_eq_zero, this]
    -- `c = ± det A` is a unit, and `q(A) = -c • A⁻¹`.
    have hc : IsUnit (-c) := by
      rw [det_eq_sign_charpoly_coeff] at h
      exact (isUnit_of_mul_isUnit_right h).neg
    have hQ : aeval A q = (-c) • A⁻¹ := by
      rw [← one_mul (aeval A q), ← nonsing_inv_mul A h, mul_assoc, hq, mul_smul_comm, mul_one]
    have hinv : A⁻¹ = (↑hc.unit⁻¹ : R) • aeval A q := by
      rw [hQ, smul_smul, hc.val_inv_mul, one_smul]
    rw [hinv]
    exact S.smul_mem (coe_aeval_mk_apply (p := q) (h := hA) ▸ (aeval (⟨A, hA⟩ : S) q).property) _
  · rw [nonsing_inv_apply_not_isUnit A h]
    exact zero_mem S

end Matrix
