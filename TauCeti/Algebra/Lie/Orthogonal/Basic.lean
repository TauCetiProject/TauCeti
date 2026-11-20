/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Basic.Real.Star
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

The file also records invertibility of the indefinite Gram matrix
`LieAlgebra.Orthogonal.indefiniteDiagonal p q R`, symmetry of the split even orthogonal Gram
matrix `LieAlgebra.Orthogonal.JD ι R` and the invariance of its bilinear form under renaming the
hyperbolic pairs, and symmetry and invertibility of the split odd orthogonal Gram matrix
`LieAlgebra.Orthogonal.JB ι R`.

## Main results

* `Matrix.mem_so_iff_mem_skewAdjoint` identifies the real orthogonal Lie algebra with the
  skew-adjoint matrices.
* `LieAlgebra.Orthogonal.isUnit_indefiniteDiagonal`: the Gram matrix of the indefinite form is
  invertible.
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

variable {p q R : Type*} [DecidableEq p] [DecidableEq q] [Fintype p] [Fintype q] [CommRing R]

open Matrix in
/-- The Gram matrix `diag(1, …, 1, -1, …, -1)` of the indefinite form is invertible; it is its
own inverse. -/
theorem isUnit_indefiniteDiagonal : IsUnit (indefiniteDiagonal p q R) :=
  isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i ↦ by cases i <;> simp)

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
