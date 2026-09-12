/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cholesky.Basic
import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# The Cholesky equivalence

This file proves uniqueness of positive-diagonal lower-triangular Gram factors. Together with the
Cholesky construction, this packages Cholesky factorization and reconstruction as an equivalence
between positive-definite symmetric matrices and positive-diagonal lower-triangular matrices.

## Main results

* `TauCeti.cholesky_unique` identifies any positive-diagonal lower-triangular Gram factor with the
  Cholesky factor.
* `TauCeti.cholesky_choleskyReconstruction` is the inverse identity from factors to matrices.
* `TauCeti.choleskyEquiv` is the resulting equivalence.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 7.2.
-/

public section

noncomputable section

open scoped Matrix

namespace TauCeti

/-- A positive-diagonal lower-triangular square root of a positive-definite matrix is its
Cholesky factor. -/
theorem cholesky_unique {p : ℕ} (A : PosDefMatrix p) (L : PosDiagLowerTriangular p)
    (hL : L.1 * L.1ᵀ = (A.1 : Matrix (Fin p) (Fin p) ℝ)) : L = cholesky A := by
  apply Subtype.ext
  exact L.2.1.eq_of_mul_transpose_self_eq (cholesky A).2.1 L.2.2 (cholesky A).2.2
    (hL.trans (cholesky_mul_transpose A).symm)

/-- Taking the Cholesky factor after reconstructing a matrix from a positive-diagonal
lower-triangular factor returns that factor. -/
@[simp]
theorem cholesky_choleskyReconstruction {p : ℕ} (L : PosDiagLowerTriangular p) :
    cholesky (choleskyReconstruction L) = L :=
  (cholesky_unique (choleskyReconstruction L) L (choleskyReconstruction_coe L).symm).symm

/-- Cholesky factorization is an equivalence between positive-definite symmetric matrices and
positive-diagonal lower-triangular matrices. -/
noncomputable def choleskyEquiv {p : ℕ} :
    PosDefMatrix p ≃ PosDiagLowerTriangular p where
  toFun := cholesky
  invFun := choleskyReconstruction
  left_inv := choleskyReconstruction_cholesky
  right_inv := cholesky_choleskyReconstruction

/-- The forward map of `choleskyEquiv` is `cholesky`. -/
@[simp]
theorem choleskyEquiv_apply {p : ℕ} (A : PosDefMatrix p) :
    choleskyEquiv A = cholesky A :=
  (rfl)

/-- The inverse map of `choleskyEquiv` is `choleskyReconstruction`. -/
@[simp]
theorem choleskyEquiv_symm_apply {p : ℕ} (L : PosDiagLowerTriangular p) :
    choleskyEquiv.symm L = choleskyReconstruction L :=
  (rfl)

end TauCeti
