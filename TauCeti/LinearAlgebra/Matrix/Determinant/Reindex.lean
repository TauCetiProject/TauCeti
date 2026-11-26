/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Squaring a matrix along a bijection of its index types

A matrix `A` with rows `m` and columns `n` has no determinant of its own, but a bijection
`e : n ≃ m` makes it square: `A.submatrix id e.symm` has rows and columns `m`. This is how the
determinant of a bipartite adjacency matrix, such as a Kasteleyn matrix with rows the white and
columns the black faces of a region, is taken. Changing the bijection permutes the columns, so the
determinant only changes sign, and the inverse, read back as a matrix with rows `n` and columns
`m`, does not change at all.

## Main statements

* `Matrix.det_submatrix_id_symm_eq_sign_mul_det`: the determinants for two bijections `e`, `e'`
  differ by the sign of the permutation `e ∘ e'⁻¹` of `m`.
* `Matrix.inv_submatrix_id_symm_submatrix`: the matrix `(A.submatrix id e.symm)⁻¹.submatrix e id`,
  with rows `n` and columns `m`, does not depend on `e`.
-/

public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [DecidableEq m] [CommRing R]

/-- The determinants of a matrix squared along two bijections `e`, `e'` of its column index onto
its row index differ by the sign of the permutation `e ∘ e'⁻¹` of the rows. -/
theorem det_submatrix_id_symm_eq_sign_mul_det (A : Matrix m n R) (e e' : n ≃ m) :
    (A.submatrix id e'.symm).det =
      Equiv.Perm.sign (e'.symm.trans e) * (A.submatrix id e.symm).det := by
  rw [← det_permute']
  congr 1
  ext i j
  simp

/-- The inverse of a matrix squared along a bijection `e` of its column index `n` onto its row
index `m`, read as a matrix with rows `n` and columns `m`, does not depend on `e`. -/
theorem inv_submatrix_id_symm_submatrix (A : Matrix m n R) (e e' : n ≃ m) :
    (A.submatrix id e'.symm)⁻¹.submatrix e' id = (A.submatrix id e.symm)⁻¹.submatrix e id := by
  have h : (A.submatrix id e'.symm)⁻¹ =
      (A.submatrix id e.symm)⁻¹.submatrix (e'.symm.trans e) id := by
    rw [← Equiv.coe_refl, ← inv_submatrix_equiv]
    congr 1
    ext i j
    simp
  rw [h]
  ext j i
  simp

end Matrix
