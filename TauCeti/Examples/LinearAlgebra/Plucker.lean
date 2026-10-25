/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.LinearAlgebra.ExteriorPower.Plucker
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Cauchy–Binet normalization checks

These examples check conjugation conventions and the empty and overfull boundary cases for
the Plücker Cauchy–Binet identities. The complex row `(1,i)` distinguishes conjugate transpose
from transpose. Empty families have determinant and squared Plücker norm one; overfull families
have no maximal minors and product determinant zero.
-/

public section
namespace TauCeti.Examples.Plucker
open Matrix

/-- The row used to distinguish Hermitian from bilinear Gram matrices. -/
def oneIRow : Matrix (Fin 1) (Fin 2) ℂ := Matrix.of ![![1, Complex.I]]

/-- The complex row `(1,i)` has Hermitian Gram determinant two. -/
theorem one_I_hermitian_gram :
    Matrix.det (oneIRow * Matrix.conjTranspose oneIRow) = 2 := by
  rw [Matrix.det_unique, Matrix.mul_apply]
  norm_num [oneIRow, Fin.sum_univ_two]

/-- Without conjugation the same row has Gram determinant zero. -/
theorem one_I_bilinear_gram :
    Matrix.det (oneIRow * Matrix.transpose oneIRow) = 0 := by
  rw [Matrix.det_unique, Matrix.mul_apply]
  norm_num [oneIRow, Fin.sum_univ_two]

/-- The squared Plücker norm of the row `(1,i)` is two, using the native Hermitian formula. -/
theorem one_I_plucker_norm :
    ∑ s, plucker oneIRow.row s * star (plucker oneIRow.row s) = 2 := by
  rw [← det_mul_conjTranspose_eq_sum_plucker_mul_star]
  exact one_I_hermitian_gram

/-- For an empty family both sides of Cauchy–Binet are one. -/
theorem empty_plucker_product {n : ℕ} (x y : Fin 0 → Fin n → ℂ) :
    ∑ s, plucker x s * plucker y s = 1 := by
  rw [← det_mul_transpose_eq_sum_plucker_mul]
  exact Matrix.det_isEmpty

/-- The Hermitian formula has the same empty-family normalization. -/
theorem empty_plucker_norm {n : ℕ} (x : Fin 0 → Fin n → ℂ) :
    ∑ s, plucker x s * star (plucker x s) = 1 := by
  rw [← det_mul_conjTranspose_eq_sum_plucker_mul_star]
  exact Matrix.det_isEmpty

/-- With more rows than columns there are no maximal minors. -/
theorem plucker_product_eq_zero_of_columns_lt_rows {m n : ℕ} (h : n < m)
    (x y : Fin m → Fin n → ℂ) : ∑ s, plucker x s * plucker y s = 0 := by
  have : IsEmpty (Set.powersetCard (Fin n) m) :=
    Set.isEmpty_coe_sort.mpr (Set.powersetCard.eq_empty_iff.mpr (by simpa using h))
  exact Finset.sum_eq_zero fun s _ => isEmptyElim s

/-- The product determinant also vanishes with more rows than columns. -/
theorem gram_eq_zero_of_columns_lt_rows {m n : ℕ} (h : n < m)
    (x y : Fin m → Fin n → ℂ) :
    (Matrix.of x * (Matrix.of y).transpose).det = 0 := by
  rw [det_mul_transpose_eq_sum_plucker_mul]
  exact plucker_product_eq_zero_of_columns_lt_rows h x y

end TauCeti.Examples.Plucker
