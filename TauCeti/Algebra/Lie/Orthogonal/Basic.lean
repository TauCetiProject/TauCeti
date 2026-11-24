/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Basic.Real.Star
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Algebra.Group.Pi.Units

/-!
# Basic facts about the orthogonal Lie algebras

Mathlib carries two unrelated descriptions of the skew-symmetric real matrices: the orthogonal Lie
algebra `LieAlgebra.Orthogonal.so n ℝ`, cut out by the skew-adjointness condition `Aᵀ = -A` for the
identity bilinear form, and `skewAdjoint (Matrix n n ℝ)`, the skew-adjoint part of the star ring
`Matrix n n ℝ`.  This file identifies them: over `ℝ` the star of a matrix is its conjugate
transpose, which is its transpose.

The bridge is purely algebraic, with no exponential or topological content, so it is stated here
and consumed by the exponential and Lie-subgroup files that compare `so` with star-algebra
statements about the unitary — that is, orthogonal — group of `Matrix n n ℝ`.

The file also records the elementary identities of the indefinite Gram matrix
`J = LieAlgebra.Orthogonal.indefiniteDiagonal p q R = diag(1, …, 1, -1, …, -1)`, on which the
groups preserving its form are built: it is invertible, `J * J = 1`, it is Hermitian, and it is the
block matrix `fromBlocks 1 0 0 (-1)`; it acts on vectors by scaling their coordinates by `±1`. It
records symmetry of the split even orthogonal Gram matrix
`LieAlgebra.Orthogonal.JD ι R` and the invariance of its bilinear form under renaming the
hyperbolic pairs, and symmetry and invertibility of the split odd orthogonal Gram matrix
`LieAlgebra.Orthogonal.JB ι R`.

## Main results

* `Matrix.mem_so_iff_mem_skewAdjoint` identifies the real orthogonal Lie algebra with the
  skew-adjoint matrices.
* `LieAlgebra.Orthogonal.mul_mul_transpose_mem_so`: the orthogonal Lie algebra is stable under
  `A ↦ M A Mᵀ`, in particular under conjugation by orthogonal matrices.
* `LieAlgebra.Orthogonal.isUnit_indefiniteDiagonal`: the Gram matrix of the indefinite form is
  invertible.
* `LieAlgebra.Orthogonal.indefiniteDiagonal_mul_indefiniteDiagonal`,
  `LieAlgebra.Orthogonal.inv_indefiniteDiagonal`,
  `LieAlgebra.Orthogonal.indefiniteDiagonal_apply_self_eq_one_or_eq_neg_one`,
  `LieAlgebra.Orthogonal.indefiniteDiagonal_apply_self_ne_zero`,
  `LieAlgebra.Orthogonal.indefiniteDiagonal_eq_fromBlocks`,
  `LieAlgebra.Orthogonal.isHermitian_indefiniteDiagonal` and
  `LieAlgebra.Orthogonal.star_indefiniteDiagonal`: it squares to one, so is its own inverse,
  its diagonal entries are `±1`, hence nonzero, it is the block matrix `fromBlocks 1 0 0 (-1)`, and
  it is Hermitian, that is, self-adjoint.
* `LieAlgebra.Orthogonal.indefiniteDiagonal_mulVec_apply` and
  `LieAlgebra.Orthogonal.vecMul_indefiniteDiagonal_apply`: it scales the coordinates of a vector by
  its diagonal entries.
* `LieAlgebra.Orthogonal.isSymm_JD`: the split even orthogonal Gram matrix is symmetric.
* `LieAlgebra.Orthogonal.toBilin'_JD_comp_sumMap`: the split even orthogonal form is unchanged by
  renaming its hyperbolic pairs along an equivalence.
* `LieAlgebra.Orthogonal.isSymm_JB` and `LieAlgebra.Orthogonal.isUnit_JB`: the split odd
  orthogonal Gram matrix is symmetric and is invertible when two is a unit.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over `ℝ` the orthogonal Lie algebra is the skew-adjoint part of the matrix algebra: the star
of a real matrix is its conjugate transpose, which is its transpose. -/
theorem mem_so_iff_mem_skewAdjoint (A : Matrix n n ℝ) :
    A ∈ LieAlgebra.Orthogonal.so n ℝ ↔ A ∈ skewAdjoint (Matrix n n ℝ) := by
  rw [LieAlgebra.Orthogonal.mem_so, skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

end Matrix

namespace LieAlgebra.Orthogonal

open Matrix in
/-- The orthogonal Lie algebra is stable under `A ↦ M A Mᵀ` for every square matrix `M`; for an
orthogonal `M` this is conjugation by `M`. -/
theorem mul_mul_transpose_mem_so {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M : Matrix n n R) {A : Matrix n n R} (hA : A ∈ so n R) : M * A * Mᵀ ∈ so n R := by
  rw [mem_so] at hA ⊢
  simp [Matrix.transpose_mul, hA, Matrix.mul_assoc]

variable {p q R : Type*} [DecidableEq p] [DecidableEq q] [Fintype p] [Fintype q] [CommRing R]

open Matrix in
/-- The Gram matrix `diag(1, …, 1, -1, …, -1)` of the indefinite form is invertible; it is its
own inverse. -/
theorem isUnit_indefiniteDiagonal : IsUnit (indefiniteDiagonal p q R) :=
  isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i ↦ by cases i <;> simp)

open Matrix in
/-- The Gram matrix `diag(1, …, 1, -1, …, -1)` of the indefinite form squares to one. -/
@[simp]
theorem indefiniteDiagonal_mul_indefiniteDiagonal :
    indefiniteDiagonal p q R * indefiniteDiagonal p q R = 1 := by
  rw [indefiniteDiagonal, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  ext (i | i) <;> simp

open Matrix in
/-- The Gram matrix `diag(1, …, 1, -1, …, -1)` of the indefinite form is its own inverse. -/
@[simp]
theorem inv_indefiniteDiagonal : (indefiniteDiagonal p q R)⁻¹ = indefiniteDiagonal p q R :=
  inv_eq_left_inv indefiniteDiagonal_mul_indefiniteDiagonal

open Matrix in
/-- The Gram matrix of the indefinite form acts on a vector by scaling its coordinates by the
diagonal entries `±1`. -/
@[simp]
theorem indefiniteDiagonal_mulVec_apply (v : p ⊕ q → R) (i : p ⊕ q) :
    (indefiniteDiagonal p q R *ᵥ v) i = indefiniteDiagonal p q R i i * v i := by
  simp [indefiniteDiagonal, mulVec_diagonal]

open Matrix in
/-- The Gram matrix of the indefinite form acts on a row vector by scaling its coordinates by the
diagonal entries `±1`. -/
@[simp]
theorem vecMul_indefiniteDiagonal_apply (v : p ⊕ q → R) (i : p ⊕ q) :
    (v ᵥ* indefiniteDiagonal p q R) i = v i * indefiniteDiagonal p q R i i := by
  simp [indefiniteDiagonal, vecMul_diagonal]

omit [Fintype p] [Fintype q] in
/-- Each diagonal entry of the Gram matrix of the indefinite form is `1` or `-1`. -/
theorem indefiniteDiagonal_apply_self_eq_one_or_eq_neg_one (i : p ⊕ q) :
    indefiniteDiagonal p q R i i = 1 ∨ indefiniteDiagonal p q R i i = -1 := by
  cases i <;> simp [indefiniteDiagonal]

omit [Fintype p] [Fintype q] in
/-- The diagonal entries of the Gram matrix of the indefinite form are nonzero. -/
theorem indefiniteDiagonal_apply_self_ne_zero [Nontrivial R] (i : p ⊕ q) :
    indefiniteDiagonal p q R i i ≠ 0 := by
  rcases indefiniteDiagonal_apply_self_eq_one_or_eq_neg_one (p := p) (q := q) (R := R) i
    with h | h <;> simp [h]

omit [Fintype p] [Fintype q] in
open Matrix in
/-- The Gram matrix of the indefinite form is the block matrix `fromBlocks 1 0 0 (-1)`. -/
theorem indefiniteDiagonal_eq_fromBlocks :
    indefiniteDiagonal p q R = fromBlocks 1 0 0 (-1) := by
  ext (i | i) (j | j) <;> simp [indefiniteDiagonal, Matrix.one_apply, diagonal_apply, neg_ite]

omit [Fintype p] [Fintype q] in
open Matrix in
/-- The Gram matrix of the indefinite form is Hermitian. -/
@[simp]
theorem isHermitian_indefiniteDiagonal [StarRing R] : (indefiniteDiagonal p q R).IsHermitian := by
  rw [Matrix.IsHermitian, indefiniteDiagonal, diagonal_conjTranspose]
  congr 1
  ext (i | i) <;> simp

omit [Fintype p] [Fintype q] in
/-- The Gram matrix of the indefinite form is self-adjoint. -/
@[simp]
theorem star_indefiniteDiagonal [StarRing R] :
    star (indefiniteDiagonal p q R) = indefiniteDiagonal p q R :=
  isHermitian_indefiniteDiagonal

variable {ι : Type*} [DecidableEq ι]

/-- The Gram matrix of the split even orthogonal form is symmetric. -/
@[simp]
theorem isSymm_JD : (JD ι R).IsSymm := by
  simp [Matrix.IsSymm, JD, Matrix.fromBlocks_transpose]

/-- The split even orthogonal form does not depend on the names of the hyperbolic pairs:
renaming both isotropic blocks along an equivalence preserves its values. -/
theorem toBilin'_JD_comp_sumMap {κ : Type*} [DecidableEq κ] [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (v w : κ ⊕ κ → R) :
    (JD ι R).toBilin' (fun s => v (Sum.map e e s)) (fun s => w (Sum.map e e s)) =
      (JD κ R).toBilin' v w := by
  simp only [Matrix.toBilin'_apply', JD, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec,
    Matrix.one_mulVec, zero_add, add_zero, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Function.comp_apply, Sum.map_inl, Sum.map_inr]
  exact congrArg₂ (· + ·) (Equiv.sum_comp e fun j => v (.inl j) * w (.inr j))
    (Equiv.sum_comp e fun j => v (.inr j) * w (.inl j))

/-- The Gram matrix of the split odd orthogonal form is symmetric. -/
@[simp]
theorem isSymm_JB : (JB ι R).IsSymm := by
  simp [Matrix.IsSymm, JB, JD, Matrix.fromBlocks_transpose]

/-- The Gram matrix of the split odd orthogonal form is invertible when two is a unit. -/
theorem isUnit_JB [Fintype ι] (h2 : IsUnit (2 : R)) : IsUnit (JB ι R) := by
  obtain ⟨u, hu⟩ := h2
  refine isUnit_iff_exists_inv.mpr
    ⟨Matrix.fromBlocks ((↑(u⁻¹) : R) • 1) 0 0 (JD ι R), ?_⟩
  simp [JB, JD, Matrix.fromBlocks_multiply, Matrix.mul_smul, ← hu, smul_smul]

end LieAlgebra.Orthogonal
