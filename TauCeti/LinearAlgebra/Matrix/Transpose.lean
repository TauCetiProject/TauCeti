/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Data.Matrix.Basic

/-!
# Transpose identities for polynomials and scalar-matrix products

Evaluating a polynomial at the transpose of a square matrix gives the transpose of its value
(`Matrix.aeval_transpose`). This is the image of `Polynomial.aeval_algHom_apply` under Mathlib's
`Matrix.transposeAlgEquiv` to the opposite ring.

Over a noncommutative `R`-algebra `A`, scalar matrices in the image of `algebraMap R A` commute
entrywise with arbitrary `A`-valued matrices, so transposing a product of a scalar matrix and an
`A`-valued matrix reverses the order of multiplication (`Matrix.transpose_map_algebraMap_mul` and
`Matrix.transpose_mul_map_algebraMap`).
-/

public section

open Polynomial

namespace Matrix

section Polynomial

variable {n R α : Type*} [Fintype n] [DecidableEq n] [CommSemiring R] [CommSemiring α]
  [Algebra R α]

/-- Evaluating a polynomial at the transpose of a matrix gives the transpose of its value. -/
theorem aeval_transpose (M : Matrix n n α) (q : R[X]) : aeval Mᵀ q = (aeval M q)ᵀ :=
  MulOpposite.op_injective <| by
    rw [← aeval_op_apply]
    exact aeval_algHom_apply (transposeAlgEquiv n R α) M q

end Polynomial

section AlgebraMap

variable {m n o R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Fintype n]

/-- Transposing the product of a scalar matrix (mapped along `algebraMap R A`) with an `A`-valued
matrix reverses the order of multiplication, even when `A` is noncommutative. -/
theorem transpose_map_algebraMap_mul (P : Matrix m n R) (X : Matrix n o A) :
    (P.map (algebraMap R A) * X)ᵀ = Xᵀ * Pᵀ.map (algebraMap R A) := by
  ext i j
  simp only [transpose_apply, Matrix.mul_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun k _ ↦ Algebra.commutes (P j k) (X k i)

/-- Transposing the product of an `A`-valued matrix with a scalar matrix (mapped along
`algebraMap R A`) reverses the order of multiplication, even when `A` is noncommutative. -/
theorem transpose_mul_map_algebraMap (X : Matrix m n A) (P : Matrix n o R) :
    (X * P.map (algebraMap R A))ᵀ = Pᵀ.map (algebraMap R A) * Xᵀ := by
  ext i j
  simp only [transpose_apply, Matrix.mul_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun k _ ↦ (Algebra.commutes (P k i) (X j k)).symm

end AlgebraMap

end Matrix
