/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MatrixAlgebra
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# Tensor products of matrix algebras

This file records the finite-index form of the Kronecker equivalence for tensor products of
matrix algebras, and the unital ⋆-algebra homomorphisms that tensor a matrix by the identity on
either side.

## Main results

* `Matrix.finOneAlgEquiv`: the canonical equivalence `A ≃ₐ[R] M₁(A)` using `Fin 1` indices.
* `Matrix.kroneckerTMulFinAlgEquiv`: matrix absorption
  `M_m(A) ⊗[R] M_n(B) ≃ₐ[R] M_(mn)(A ⊗[R] B)`.
* `Matrix.kroneckerFinAlgEquiv`: its scalar case `M_m(R) ⊗[R] M_n(R) ≃ₐ[R] M_(mn)(R)`.
* `Matrix.kroneckerOneStarAlgHom`, `Matrix.oneKroneckerStarAlgHom`: the unital ⋆-algebra
  homomorphisms `A ↦ A ⊗ₖ 1` and `B ↦ 1 ⊗ₖ B`.
-/

public section

open scoped Kronecker TensorProduct

namespace Matrix

/-- The canonical one-by-one matrix equivalence with `Fin 1` indices.

Unlike `(Matrix.uniqueAlgEquiv (m := Fin 1)).symm`, whose matrix ring carries the `Fintype` and
`DecidableEq` structures manufactured from `Unique`, this targets the matrix ring with the
standard instances on `Fin 1`, so it composes with other `Fin`-indexed matrix equivalences. -/
def finOneAlgEquiv (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] :
    A ≃ₐ[R] Matrix (Fin 1) (Fin 1) A :=
  (uniqueAlgEquiv (m := Unit)).symm.trans (reindexAlgEquiv R A (Equiv.ofUnique Unit (Fin 1)))

/-- The one-by-one matrix equivalence sends a scalar to the constant one-by-one matrix. -/
@[simp]
theorem finOneAlgEquiv_apply (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (a : A) (i j : Fin 1) : finOneAlgEquiv R A a i j = a := by
  simp [finOneAlgEquiv]

/-- The inverse one-by-one matrix equivalence extracts the unique entry. -/
@[simp]
theorem finOneAlgEquiv_symm_apply (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
    (M : Matrix (Fin 1) (Fin 1) A) : (finOneAlgEquiv R A).symm M = M 0 0 := by
  simp [finOneAlgEquiv]

/-- **Matrix absorption**: `M_m(A) ⊗[R] M_n(B) ≃ₐ[R] M_(mn)(A ⊗[R] B)`, over any commutative
semiring `R` and any two `R`-algebras, in any two sizes. -/
def kroneckerTMulFinAlgEquiv (m n : ℕ) (R : Type*) [CommSemiring R] (A : Type*) [Semiring A]
    [Algebra R A] (B : Type*) [Semiring B] [Algebra R B] :
    Matrix (Fin m) (Fin m) A ⊗[R] Matrix (Fin n) (Fin n) B ≃ₐ[R]
      Matrix (Fin (m * n)) (Fin (m * n)) (A ⊗[R] B) :=
  (kroneckerTMulAlgEquiv (Fin m) (Fin n) R R A B).trans (reindexAlgEquiv R _ finProdFinEquiv)

/-- The finite-index matrix absorption equivalence sends a pure tensor to the reindexed
Kronecker tensor product. -/
@[simp]
theorem kroneckerTMulFinAlgEquiv_tmul (m n : ℕ) (R : Type*) [CommSemiring R]
    (A : Type*) [Semiring A] [Algebra R A] (B : Type*) [Semiring B] [Algebra R B]
    (a : Matrix (Fin m) (Fin m) A) (b : Matrix (Fin n) (Fin n) B) :
    kroneckerTMulFinAlgEquiv m n R A B (a ⊗ₜ[R] b) =
      reindex finProdFinEquiv finProdFinEquiv (a ⊗ₖₜ b) := by
  simp [kroneckerTMulFinAlgEquiv]

/-- The inverse finite-index matrix absorption equivalence sends a matrix unit at paired finite
indices with a pure-tensor coefficient to the tensor of the two corresponding matrix units. -/
@[simp]
theorem kroneckerTMulFinAlgEquiv_symm_single_tmul (m n : ℕ) (R : Type*)
    [CommSemiring R] (A : Type*) [Semiring A] [Algebra R A] (B : Type*) [Semiring B]
    [Algebra R B] (ia ja : Fin m) (ib jb : Fin n) (a : A) (b : B) :
    (kroneckerTMulFinAlgEquiv m n R A B).symm
        (single (finProdFinEquiv (ia, ib)) (finProdFinEquiv (ja, jb)) (a ⊗ₜ[R] b)) =
      single ia ja a ⊗ₜ[R] single ib jb b := by
  simp [AlgEquiv.symm_apply_eq, single_kroneckerTMul_single]

/-- The Kronecker product identifies `M_m(R) ⊗[R] M_n(R)` with `M_(mn)(R)`, with `Fin` indices. -/
def kroneckerFinAlgEquiv (m n : ℕ) (R : Type*) [CommSemiring R] :
    Matrix (Fin m) (Fin m) R ⊗[R] Matrix (Fin n) (Fin n) R ≃ₐ[R]
      Matrix (Fin (m * n)) (Fin (m * n)) R :=
  (kroneckerAlgEquiv (Fin m) (Fin n) R).trans (reindexAlgEquiv R R finProdFinEquiv)

/-- The finite-index Kronecker equivalence sends a pure tensor to the reindexed Kronecker
product. -/
@[simp]
theorem kroneckerFinAlgEquiv_tmul (m n : ℕ) (R : Type*) [CommSemiring R]
    (a : Matrix (Fin m) (Fin m) R) (b : Matrix (Fin n) (Fin n) R) :
    kroneckerFinAlgEquiv m n R (a ⊗ₜ[R] b) = reindex finProdFinEquiv finProdFinEquiv (a ⊗ₖ b) := by
  simp [kroneckerFinAlgEquiv]

section StarAlgHom

variable (R : Type*) {α m : Type*} (n : Type*) [CommSemiring R] [Semiring α] [StarRing α]
  [Algebra R α] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- Tensoring by the identity on the right, `A ↦ A ⊗ₖ 1`, as a unital ⋆-algebra homomorphism
over `R`, for entries in any ⋆-semiring `α` that is an `R`-algebra. -/
def kroneckerOneStarAlgHom : Matrix m m α →⋆ₐ[R] Matrix (m × n) (m × n) α where
  toFun X := X ⊗ₖ (1 : Matrix n n α)
  map_one' := one_kronecker_one
  map_mul' X Y := by simp only [kronecker_one, blockDiagonal_mul]
  map_zero' := zero_kronecker _
  map_add' X Y := add_kronecker X Y _
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one, smul_kronecker]
  map_star' X := by simp [star_eq_conjTranspose, kronecker_one, blockDiagonal_conjTranspose]

/-- Tensoring by the identity on the left, `B ↦ 1 ⊗ₖ B`, as a unital ⋆-algebra homomorphism
over `R`, for entries in any ⋆-semiring `α` that is an `R`-algebra. -/
def oneKroneckerStarAlgHom : Matrix n n α →⋆ₐ[R] Matrix (m × n) (m × n) α where
  toFun X := (1 : Matrix m m α) ⊗ₖ X
  map_one' := one_kronecker_one
  map_mul' X Y := by
    simp only [one_kronecker, blockDiagonal_mul, reindex_apply, submatrix_mul_equiv]
  map_zero' := kronecker_zero _
  map_add' X Y := kronecker_add _ X Y
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one, kronecker_smul]
  map_star' X := by
    simp [star_eq_conjTranspose, one_kronecker, blockDiagonal_conjTranspose,
      conjTranspose_submatrix]

variable {R n}

@[simp]
theorem kroneckerOneStarAlgHom_apply (A : Matrix m m α) :
    kroneckerOneStarAlgHom R n A = A ⊗ₖ (1 : Matrix n n α) :=
  (rfl)

@[simp]
theorem oneKroneckerStarAlgHom_apply (B : Matrix n n α) :
    oneKroneckerStarAlgHom R (m := m) n B = (1 : Matrix m m α) ⊗ₖ B :=
  (rfl)

end StarAlgHom

end Matrix
