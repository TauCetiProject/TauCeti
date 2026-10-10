/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
import Mathlib.Tactic.LinearCombination

/-!
# Basic lemmas for the split odd orthogonal Lie algebra

This file records the entry relations satisfied by a matrix in Mathlib's split type-`B` Lie
algebra, indexed by `Unit ⊕ ι ⊕ ι`. They do not depend on a choice of Cartan subalgebra or root
system. They are the type-`B` counterparts of the type-`D` relations
`LieAlgebra.Orthogonal.typeD.apply_inr_inr`, `LieAlgebra.Orthogonal.typeD.apply_inl_inr` and
`LieAlgebra.Orthogonal.typeD.apply_inr_inl`.

## Main results

* `LieAlgebra.Orthogonal.typeB.apply_inl_inl`: the anisotropic diagonal entry vanishes when `2`
  is regular.
* `LieAlgebra.Orthogonal.typeB.apply_inr_inl_inl` and
  `LieAlgebra.Orthogonal.typeB.apply_inr_inr_inl`: the anisotropic column is determined by the
  anisotropic row.
* `LieAlgebra.Orthogonal.typeB.apply_inr_inl_inr_inr` and
  `LieAlgebra.Orthogonal.typeB.apply_inr_inr_inr_inl`: the two off-diagonal isotropic blocks are
  skew-symmetric.
* `LieAlgebra.Orthogonal.typeB.apply_inr_inr_inr_inr`: the lower-right isotropic block is the
  negative transpose of the upper-left one.
-/

public section

namespace LieAlgebra.Orthogonal.typeB

open Matrix

variable {K ι : Type*} [CommRing K] [DecidableEq ι] [Fintype ι]

/-- The skew-adjointness equation defining the split type-`B` Lie algebra, as an equation between
matrices. -/
private theorem transpose_mul_JB (A : LieAlgebra.Orthogonal.typeB ι K) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K)ᵀ * LieAlgebra.Orthogonal.JB ι K =
      LieAlgebra.Orthogonal.JB ι K * (-(A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K)) := by
  have hA := A.2
  -- Unfold membership in `typeB` to membership in its skew-adjoint matrix submodule; Mathlib
  -- provides no public elimination lemma for this subtype membership.
  change (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) ∈
    skewAdjointMatricesSubmodule (LieAlgebra.Orthogonal.JB ι K) at hA
  rw [mem_skewAdjointMatricesSubmodule] at hA
  -- `Matrix.IsSkewAdjoint` is definitionally the displayed equation, with no equation lemma.
  exact hA

/-- In a type-`B` matrix, the anisotropic diagonal entry vanishes when `2` is regular. -/
theorem apply_inl_inl (h2 : IsRegular (2 : K)) (A : LieAlgebra.Orthogonal.typeB ι K)
    (u v : Unit) : (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl u) (.inl v) = 0 := by
  have h := congr_fun (congr_fun (transpose_mul_JB A) (.inl ())) (.inl ())
  simp [LieAlgebra.Orthogonal.JB, Matrix.mul_apply] at h
  apply h2.left
  apply h2.left
  linear_combination h

/-- In a type-`B` matrix, the anisotropic column at the first isotropic half is determined by the
anisotropic row at the second. -/
theorem apply_inr_inl_inl (A : LieAlgebra.Orthogonal.typeB ι K) (i : ι) (u : Unit) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl i)) (.inl u) =
      -(2 * (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl u) (.inr (.inr i))) := by
  simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
    Matrix.one_apply] using congr_fun (congr_fun (transpose_mul_JB A) (.inl ())) (.inr (.inr i))

/-- In a type-`B` matrix, the anisotropic column at the second isotropic half is determined by the
anisotropic row at the first. -/
theorem apply_inr_inr_inl (A : LieAlgebra.Orthogonal.typeB ι K) (i : ι) (u : Unit) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inr i)) (.inl u) =
      -(2 * (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inl u) (.inr (.inl i))) := by
  simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
    Matrix.one_apply] using congr_fun (congr_fun (transpose_mul_JB A) (.inl ())) (.inr (.inl i))

/-- In a type-`B` matrix, the upper-right isotropic block is skew-symmetric. -/
theorem apply_inr_inl_inr_inr (A : LieAlgebra.Orthogonal.typeB ι K) (i j : ι) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl i)) (.inr (.inr j)) =
      -(A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl j)) (.inr (.inr i)) := by
  simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
    Matrix.one_apply] using
    congr_fun (congr_fun (transpose_mul_JB A) (.inr (.inr j))) (.inr (.inr i))

/-- In a type-`B` matrix, the lower-left isotropic block is skew-symmetric. -/
theorem apply_inr_inr_inr_inl (A : LieAlgebra.Orthogonal.typeB ι K) (i j : ι) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inr i)) (.inr (.inl j)) =
      -(A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inr j)) (.inr (.inl i)) := by
  simpa [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
    Matrix.one_apply] using
    congr_fun (congr_fun (transpose_mul_JB A) (.inr (.inl j))) (.inr (.inl i))

/-- In a type-`B` matrix, the lower-right isotropic block is the negative transpose of the
upper-left one. -/
theorem apply_inr_inr_inr_inr (A : LieAlgebra.Orthogonal.typeB ι K) (i j : ι) :
    (A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inr i)) (.inr (.inr j)) =
      -(A : Matrix (Unit ⊕ ι ⊕ ι) (Unit ⊕ ι ⊕ ι) K) (.inr (.inl j)) (.inr (.inl i)) := by
  have h := congr_fun (congr_fun (transpose_mul_JB A) (.inr (.inl i))) (.inr (.inr j))
  simp [LieAlgebra.Orthogonal.JB, LieAlgebra.Orthogonal.JD, Matrix.mul_apply,
    Matrix.one_apply] at h
  linear_combination h

end LieAlgebra.Orthogonal.typeB
