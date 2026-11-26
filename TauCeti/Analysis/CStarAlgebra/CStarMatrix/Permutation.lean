/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic

/-!
# Reindexing matrices and permutation unitaries on `CStarMatrix`

For an equivalence `e : m ≃ n`, `CStarMatrix.reindexMatrix A e` wraps `e.toPEquiv.toMatrix` in
`CStarMatrix m n A`; when `σ : Equiv.Perm n`, its underlying `Matrix` is `σ.permMatrix A`.
Accordingly, `CStarMatrix.permutationUnitary A` bundles `σ ↦ reindexMatrix A σ⁻¹` as a group
homomorphism `Equiv.Perm n →* unitary (CStarMatrix n n A)` matching `Matrix.permutationUnitary`,
whose unitary conjugation implements `CStarMatrix.reindexₐ R A σ`.

## Main definitions

* `CStarMatrix.reindexMatrix`: the `0`-`1` matrix in `CStarMatrix m n A` associated to `e : m ≃ n`,
  wrapping `e.toPEquiv.toMatrix`.
* `CStarMatrix.permutationUnitary`: the group homomorphism
  `Equiv.Perm n →* unitary (CStarMatrix n n A)` sending `σ` to `reindexMatrix A σ⁻¹`.

## Main results

* `CStarMatrix.reindexMatrix_trans`, `CStarMatrix.conjTranspose_reindexMatrix`,
  `CStarMatrix.reindexMatrix_mul`, `CStarMatrix.mul_reindexMatrix`: functoriality, adjoint, and
  row/column reindexing identities transported from `PEquiv.toMatrix`.
* `CStarMatrix.conjTranspose_reindexMatrix_mul_mul`, `CStarMatrix.permutationUnitary_mul_mul_star`:
  conjugating by `(reindexMatrix A e)ᴴ` on the left (or by `permutationUnitary A σ` on a square
  matrix) implements `reindexₐ R A`.
-/

public section

namespace CStarMatrix

variable {l m n o R A : Type*}

/-- The `0`-`1` reindexing matrix in `CStarMatrix m n A` associated to an equivalence `e : m ≃ n`,
defined via `PEquiv.toMatrix` so that on `σ : Equiv.Perm n` it agrees with `σ.permMatrix A`. -/
def reindexMatrix (A : Type*) [DecidableEq n] [Zero A] [One A] (e : m ≃ n) : CStarMatrix m n A :=
  ofMatrix e.toPEquiv.toMatrix

@[simp] theorem ofMatrix_symm_reindexMatrix [DecidableEq n] [Zero A] [One A] (e : m ≃ n) :
    ofMatrix.symm (reindexMatrix A e) = e.toPEquiv.toMatrix := (rfl)

/-- `ofMatrix` sends `e.toPEquiv.toMatrix` to `CStarMatrix.reindexMatrix A e`. -/
theorem ofMatrix_toMatrix_toPEquiv [DecidableEq n] [Zero A] [One A] (e : m ≃ n) :
    ofMatrix (e.toPEquiv.toMatrix : Matrix m n A) = reindexMatrix A e := (rfl)

@[simp] theorem reindexMatrix_apply [DecidableEq n] [Zero A] [One A] (e : m ≃ n) (i : m) (j : n) :
    reindexMatrix A e i j = if e i = j then 1 else 0 := by
  simp [reindexMatrix, PEquiv.toMatrix_apply, eq_comm]

@[simp] theorem reindexMatrix_refl [DecidableEq n] [Zero A] [One A] :
    reindexMatrix A (Equiv.refl n) = 1 :=
  ofMatrix.symm.injective (by simp)

theorem reindexMatrix_trans [Fintype n] [DecidableEq n] [DecidableEq o] [NonAssocSemiring A]
    (e₁ : m ≃ n) (e₂ : n ≃ o) :
    reindexMatrix A (e₁.trans e₂) = reindexMatrix A e₁ * reindexMatrix A e₂ :=
  ofMatrix.symm.injective <| by simp [Equiv.toPEquiv_trans, PEquiv.toMatrix_trans]

@[simp] theorem conjTranspose_reindexMatrix [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    (reindexMatrix A e).conjTranspose = reindexMatrix A e.symm := by
  ext i j; by_cases h : e j = i <;> simp [h, Equiv.eq_symm_apply, eq_comm]

@[simp] theorem star_reindexMatrix [DecidableEq n] [NonAssocSemiring A] [StarRing A]
    (σ : Equiv.Perm n) : star (reindexMatrix A σ) = reindexMatrix A σ⁻¹ :=
  conjTranspose_reindexMatrix σ

theorem reindexMatrix_mul [Fintype m] [DecidableEq m] [Semiring R] [NonAssocSemiring A]
    [Module R A] (e : l ≃ m) (M : CStarMatrix m n A) :
    reindexMatrix A e * M = reindexₗ R A e.symm (.refl n) M :=
  ofMatrix.symm.injective <| by simp [PEquiv.toMatrix_toPEquiv_mul, Matrix.reindex_apply]

theorem mul_reindexMatrix [Fintype m] [DecidableEq n] [Semiring R] [NonAssocSemiring A]
    [Module R A] (M : CStarMatrix l m A) (e : m ≃ n) :
    M * reindexMatrix A e = reindexₗ R A (.refl l) e M :=
  ofMatrix.symm.injective <| by simp [PEquiv.mul_toMatrix_toPEquiv, Matrix.reindex_apply]

@[simp] theorem reindexMatrix_mul_symm [Fintype n] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] (e : m ≃ n) : reindexMatrix A e * reindexMatrix A e.symm = 1 := by
  rw [← reindexMatrix_trans, Equiv.self_trans_symm, reindexMatrix_refl]

@[simp] theorem reindexMatrix_symm_mul [Fintype m] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] (e : m ≃ n) : reindexMatrix A e.symm * reindexMatrix A e = 1 := by
  rw [← reindexMatrix_trans, Equiv.symm_trans_self, reindexMatrix_refl]

/-- Multiplying `reindexMatrix A e` on the right by its conjugate transpose gives `1`. -/
theorem reindexMatrix_mul_conjTranspose [Fintype n] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    reindexMatrix A e * (reindexMatrix A e).conjTranspose = 1 := by
  rw [conjTranspose_reindexMatrix, reindexMatrix_mul_symm]

/-- Multiplying `reindexMatrix A e` on the left by its conjugate transpose gives `1`. -/
theorem conjTranspose_reindexMatrix_mul [Fintype m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    (reindexMatrix A e).conjTranspose * reindexMatrix A e = 1 := by
  classical rw [conjTranspose_reindexMatrix, reindexMatrix_symm_mul]

/-- Conjugating a matrix by `(reindexMatrix A e)ᴴ` on the left and `reindexMatrix A e` on the right
implements `reindexₐ R A e`. -/
theorem conjTranspose_reindexMatrix_mul_mul [Fintype m] [Fintype n] [DecidableEq n]
    [Semiring R] [NonAssocSemiring A] [StarRing A] [Module R A]
    (e : m ≃ n) (M : CStarMatrix m m A) :
    (reindexMatrix A e).conjTranspose * M * reindexMatrix A e = reindexₐ R A e M := by
  classical
  rw [conjTranspose_reindexMatrix, reindexMatrix_mul (R := R), mul_reindexMatrix (R := R)]
  exact ofMatrix.symm.injective <| by simp [reindexₐ_eq_reindexₗ, Matrix.submatrix_submatrix]

section PermutationUnitary

variable [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]

variable (A) in
/-- A permutation as a unitary in `CStarMatrix n n A`: `permutationUnitary A σ` has underlying
matrix `reindexMatrix A σ⁻¹`, a group homomorphism matching `Matrix.permutationUnitary`. -/
def permutationUnitary : Equiv.Perm n →* unitary (CStarMatrix n n A) where
  toFun σ := ⟨ofMatrix (Matrix.permutationUnitary (R := A) σ),
    ofMatrix_mem_unitary_iff.mpr (Matrix.permutationUnitary (R := A) σ).property⟩
  map_one' := Subtype.ext <| congrArg ofMatrix <|
    congrArg Subtype.val (map_one (Matrix.permutationUnitary (n := n) (R := A)))
  map_mul' σ τ := Subtype.ext <| congrArg ofMatrix <|
    congrArg Subtype.val (map_mul (Matrix.permutationUnitary (n := n) (R := A)) σ τ)

@[simp] theorem coe_permutationUnitary (σ : Equiv.Perm n) :
    (permutationUnitary A σ : CStarMatrix n n A) = reindexMatrix A σ⁻¹ :=
  ofMatrix.symm.injective <| by simp [permutationUnitary]

theorem ofMatrix_symm_coe_permutationUnitary (σ : Equiv.Perm n) :
    ofMatrix.symm (permutationUnitary A σ : CStarMatrix n n A) = σ⁻¹.permMatrix A := by
  simp

@[simp] theorem star_permutationUnitary (σ : Equiv.Perm n) :
    star (permutationUnitary A σ) = permutationUnitary A σ⁻¹ := by
  rw [Unitary.star_eq_inv, ← map_inv]

/-- Conjugating a square `CStarMatrix` by `permutationUnitary A σ` implements `reindexₐ R A σ`. -/
theorem permutationUnitary_mul_mul_star [Semiring R] [Module R A]
    (σ : Equiv.Perm n) (M : CStarMatrix n n A) :
    (permutationUnitary A σ : CStarMatrix n n A) * M *
        star (permutationUnitary A σ : CStarMatrix n n A) = reindexₐ R A σ M := by
  simpa [Equiv.Perm.inv_def, star_eq_conjTranspose] using
    conjTranspose_reindexMatrix_mul_mul (R := R) σ M

end PermutationUnitary

end CStarMatrix
