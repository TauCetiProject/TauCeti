/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.SkewAdjoint.Star
public import Mathlib.Basic.Real.Star
import Mathlib.Algebra.Group.Pi.Units

/-!
# Basic facts about the orthogonal Lie algebras

Over a commutative ring `R` with trivial star, the matrix involution is transposition. Thus
Mathlib's orthogonal Lie algebra `LieAlgebra.Orthogonal.so n R`, defined by `Aᵀ = -A`, has
the same carrier as `skewAdjoint (Matrix n n R)`. This file identifies those carriers and the
corresponding skew-adjoint Lie subalgebra.

These identities express skew-adjointness calculations for unitary matrix groups in the
canonical orthogonal Lie algebra.

The file also records invertibility of the indefinite Gram matrix
`LieAlgebra.Orthogonal.indefiniteDiagonal p q R`, and symmetry and invertibility of the split
odd orthogonal Gram matrix `LieAlgebra.Orthogonal.JB ι R`.

## Main results

* `Matrix.mem_so_iff_mem_skewAdjoint` identifies orthogonal Lie-algebra membership with
  skew-adjointness over a commutative ring with trivial star.
* `Matrix.skewAdjoint_lieSubalgebra_eq_so`: the skew-adjoint Lie subalgebra is `so` over
  any commutative ring with trivial star.
* `LieAlgebra.Orthogonal.isUnit_indefiniteDiagonal`: the Gram matrix of the indefinite form is
  invertible.
* `LieAlgebra.Orthogonal.isSymm_JB` and `LieAlgebra.Orthogonal.isUnit_JB`: the split odd
  orthogonal Gram matrix is symmetric and is invertible when two is a unit.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over a commutative ring with trivial star, the orthogonal Lie algebra is the skew-adjoint
part of the matrix algebra: conjugate transposition is transposition. -/
theorem mem_so_iff_mem_skewAdjoint {R : Type*} [CommRing R] [StarRing R] [TrivialStar R]
    (A : Matrix n n R) :
    A ∈ LieAlgebra.Orthogonal.so n R ↔ A ∈ skewAdjoint (Matrix n n R) := by
  rw [LieAlgebra.Orthogonal.mem_so, skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

/-- Over a commutative ring with trivial star, the skew-adjoint matrix Lie subalgebra is `so`. -/
@[simp]
theorem skewAdjoint_lieSubalgebra_eq_so {R : Type*} [CommRing R] [StarRing R] [TrivialStar R] :
    skewAdjoint.lieSubalgebra R (Matrix n n R) = LieAlgebra.Orthogonal.so n R := by
  apply SetLike.coe_injective
  rw [skewAdjoint.coe_lieSubalgebra]
  ext A
  exact (mem_so_iff_mem_skewAdjoint A).symm

end Matrix

namespace LieAlgebra.Orthogonal

variable {p q R : Type*} [DecidableEq p] [DecidableEq q] [Fintype p] [Fintype q] [CommRing R]

open Matrix in
/-- The Gram matrix `diag(1, …, 1, -1, …, -1)` of the indefinite form is invertible; it is its
own inverse. -/
theorem isUnit_indefiniteDiagonal : IsUnit (indefiniteDiagonal p q R) :=
  isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i ↦ by cases i <;> simp)

variable {ι : Type*} [DecidableEq ι]

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
