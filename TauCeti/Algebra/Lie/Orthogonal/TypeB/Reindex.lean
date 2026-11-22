/-
Copyright (c) 2026 Robert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert
-/
module

public import Mathlib.Algebra.Lie.Classical

/-!
# Reindexing the native type-B Lie algebra

An equivalence of the isotropic index types reindexes both signed blocks and fixes
the norm-two coordinate. This preserves the native odd orthogonal form and gives
a Lie equivalence over any commutative ring.

## Main results

* `LieAlgebra.Orthogonal.reindex_JB`: reindexing both isotropic blocks fixes the split odd
  orthogonal Gram matrix.
* `LieAlgebra.Orthogonal.typeBReindexLieEquiv`: the resulting Lie equivalence of native type-B
  Lie algebras.
-/

public section

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace LieAlgebra.Orthogonal

universe u v

variable {I J : Type u} [DecidableEq I] [Fintype I] [DecidableEq J] [Fintype J]
  (A : Type v) [CommRing A]

omit [Fintype I] [Fintype J] in
/-- Reindexing both isotropic blocks by an equivalence, and fixing the norm-two coordinate,
carries the split odd orthogonal Gram matrix to the one on the new index type. -/
theorem reindex_JB (e : I ≃ J) :
    Matrix.reindex (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr e e))
      (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr e e)) (JB I A) = JB J A := by
  ext i j
  rcases i with u | (i | i) <;> rcases j with v | (j | j) <;>
    simp [Matrix.reindex_apply, JB, JD, Matrix.one_apply]

/-- Reindex both isotropic blocks and keep the norm-two coordinate fixed. -/
def typeBReindexLieEquiv (e : I ≃ J) : typeB I A ≃ₗ⁅A⁆ typeB J A :=
  (skewAdjointMatricesLieSubalgebraEquivTranspose (JB I A)
    (Matrix.reindexAlgEquiv A A
      (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr e e)))
    (Matrix.transpose_reindex _ _)).trans
      (LieEquiv.ofEq _ _ (by simp only [Matrix.coe_reindexAlgEquiv, reindex_JB, typeB]))

/-- The underlying matrix is reindexed in both signed blocks. -/
@[simp]
theorem typeBReindexLieEquiv_apply_val (e : I ≃ J) (X : typeB I A) :
    (typeBReindexLieEquiv A e X : Matrix (Unit ⊕ J ⊕ J) (Unit ⊕ J ⊕ J) A) =
      Matrix.reindex (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr e e))
        (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr e e)) X := by
  rfl

/-- The inverse equivalence reindexes by the inverse equivalence of isotropic indices. -/
@[simp]
theorem typeBReindexLieEquiv_symm_apply_val (e : I ≃ J) (Y : typeB J A) :
    ((typeBReindexLieEquiv A e).symm Y : Matrix (Unit ⊕ I ⊕ I) (Unit ⊕ I ⊕ I) A) =
      Matrix.reindex (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr e.symm e.symm))
        (Equiv.sumCongr (Equiv.refl Unit) (Equiv.sumCongr e.symm e.symm)) Y := by
  rfl

end LieAlgebra.Orthogonal
