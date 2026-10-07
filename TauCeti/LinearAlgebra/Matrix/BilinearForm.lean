/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Bilinear forms attached to matrices

Mathlib's `Matrix.toBilin'` reads a square matrix `M` over a commutative semiring `R` as the
bilinear form `(x, y) ↦ xᵀ M y` on `n → R`. This file records facts about these forms that
Mathlib lacks. The identity matrix gives the standard form `∑ i, x i * y i`, which takes the value
`1` on every standard basis vector, so over a nontrivial `R` it is alternating only when the index
type is empty (over the trivial semiring `1 = 0` and every form is alternating). Since the identity
matrix is symmetric and invertible, the standard form over a nontrivial `R` is in every positive
dimension a nondegenerate symmetric form that is not alternating, the model for the orthonormal
normal form of such forms.

In the other direction, `LinearMap.BilinForm.toMatrix` reads a bilinear form in a basis as its
Gram matrix. For a nondegenerate form, the Gram matrix in the `B`-dual basis is the inverse
transpose of the Gram matrix in the original basis; for a symmetric form it is the inverse Gram
matrix, which is how the dual of a lattice is described in coordinates.

Over `ℤ` a change of basis multiplies the Gram determinant by the square of a unit, which is `1`,
so the Gram determinant of an integral bilinear form on a free `ℤ`-module of finite rank does not
depend on the basis.

## Main results

* `Matrix.isAlt_toBilin'_one_iff`: for `R` nontrivial, the standard form on `n → R` is alternating
  exactly when `n` is empty.
* `LinearMap.BilinForm.toMatrix_dualBasis`: the Gram matrix of a nondegenerate form in a `B`-dual
  basis is the inverse transpose of its Gram matrix in the original basis.
* `LinearMap.BilinForm.det_toMatrix_eq_det_toMatrix`: over `ℤ`, the Gram determinant does not
  depend on the basis.
-/

public section

namespace Matrix

/-- Over a nontrivial commutative semiring `R`, the standard form `∑ i, x i * y i` on `n → R` is
alternating only when `n` is empty: it takes the value `1 ≠ 0` on every standard basis vector. -/
@[simp]
theorem isAlt_toBilin'_one_iff {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R]
    [Nontrivial R] : (toBilin' (1 : Matrix n n R)).IsAlt ↔ IsEmpty n := by
  refine ⟨fun h => ⟨fun i => by simpa using h (Pi.single i 1)⟩, fun hn x => ?_⟩
  simp [Subsingleton.elim x 0]

end Matrix

namespace LinearMap.BilinForm

open Matrix Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

/-- The Gram matrix of a nondegenerate bilinear form in the `B`-dual basis of `b` is the inverse of
the transpose of its Gram matrix in `b`. For a symmetric form this is the inverse Gram matrix. -/
theorem toMatrix_dualBasis (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) :
    toMatrix (B.dualBasis hB b) B = (toMatrix b B)ᵀ⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  ext i j
  calc (toMatrix (B.dualBasis hB b) B * (toMatrix b B)ᵀ) i j
      = B (B.dualBasis hB b i)
          (∑ k, (B.dualBasis hB b).repr (b j) k • B.dualBasis hB b k) := by
        simp [Matrix.mul_apply, toMatrix_apply, dualBasis_repr_apply, mul_comm]
    _ = (1 : Matrix ι ι K) i j := by
        rw [(B.dualBasis hB b).sum_repr, apply_dualBasis_left, Matrix.one_apply]
        simp only [eq_comm]

section Int

variable {M ι κ : Type*} [AddCommGroup M] [Module ℤ M] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- **Over `ℤ` the Gram determinant does not depend on the basis.** A change of basis multiplies
the Gram determinant by the square of the determinant of the change-of-basis matrix, a unit of
`ℤ`. The two bases may have different index types. -/
theorem det_toMatrix_eq_det_toMatrix (B : LinearMap.BilinForm ℤ M) (b : Basis ι ℤ M)
    (c : Basis κ ℤ M) : (toMatrix b B).det = (toMatrix c B).det := by
  let c' := c.reindex (c.indexEquiv b)
  have hc : (toMatrix c' B).det = (toMatrix c B).det := by
    rw [← Matrix.det_submatrix_equiv_self (c.indexEquiv b).symm (toMatrix c B)]
    congr 1
    ext i j
    simp [c', toMatrix_apply]
  have hunit : (b.toMatrix c').det ^ 2 = 1 := by
    rw [sq_eq_one_iff, ← Int.isUnit_iff, ← Basis.det_apply]
    exact b.isUnit_det c'
  rw [← hc, ← toMatrix_mul_basis_toMatrix (b := b) c' B, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, mul_right_comm, ← sq, hunit, one_mul]

end Int

end LinearMap.BilinForm
