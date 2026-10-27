/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Basic
public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Root.Generators

/-!
# The even orthogonal block in the odd orthogonal Lie algebra

The isotropic block of a native type-`B` matrix is a native type-`D` matrix. The basic linear
maps `toTypeD` and `ofTypeD` project to this block and extend it by zero.

When multiplication by `2` is injective, `blockEquiv` separates the two short-root coordinate
families from this block. Its inverse uses the native positive and negative short-root
generators. This supplies the block decomposition used in the full type-`B` root basis.
-/

public section

namespace LieAlgebra.Orthogonal.typeB

open Matrix

variable {R ι : Type*} [CommRing R] [DecidableEq ι] [Fintype ι]

open TauCeti

/-- Separate the two short-root coordinate families from the even orthogonal block.
This is a linear equivalence; the three summands are not independent Lie ideals. -/
def blockEquiv (h2 : IsRegular (2 : R)) :
    typeB ι R ≃ₗ[R] (ι → R) × ((ι → R) × typeD ι R) where
  toFun X := (fun i => -X.val (.inl ()) (.inr (.inr i)),
    (fun i => X.val (.inl ()) (.inr (.inl i)), toTypeD X))
  invFun x := (∑ i, x.1 i • typeBShortRootGenerator i) +
    (∑ i, x.2.1 i • typeBShortNegativeRootGenerator i) + ofTypeD x.2.2
  left_inv X := by
    apply Subtype.ext
    ext (a | (a | a)) (b | (b | b)) <;>
      simp [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
        Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        Matrix.single_apply, Matrix.toBlocks₂₂, apply_inl_inl X h2, eq_comm]
  right_inv x := by
    rcases x with ⟨a, b, Y⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · ext i
      simp [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
        Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        Matrix.single_apply, eq_comm]
    · ext i
      simp [typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
        Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul,
        Matrix.single_apply, eq_comm]
    · apply Subtype.ext
      ext i j
      simp [Matrix.toBlocks₂₂, typeBShortRootMatrix_def, typeBShortNegativeRootMatrix_def,
        Matrix.sum_apply, Matrix.sub_apply, smul_eq_mul, Matrix.of_apply]
  map_add' X Y := by
    ext <;> simp [add_comm]
  map_smul' c X := by
    ext <;> simp [mul_neg]

/-- The positive short-root coordinates are negatives of the last anisotropic row entries. -/
@[simp]
theorem blockEquiv_apply_fst (h2 : IsRegular (2 : R)) (X : typeB ι R) (i : ι) :
    (blockEquiv h2 X).1 i = -X.val (.inl ()) (.inr (.inr i)) := by
  rfl

/-- The negative short-root coordinates are the first anisotropic row entries. -/
@[simp]
theorem blockEquiv_apply_snd_fst (h2 : IsRegular (2 : R)) (X : typeB ι R) (i : ι) :
    (blockEquiv h2 X).2.1 i = X.val (.inl ()) (.inr (.inl i)) := by
  rfl

/-- The remaining coordinate is the full even orthogonal block. -/
@[simp]
theorem blockEquiv_apply_snd_snd (h2 : IsRegular (2 : R)) (X : typeB ι R) :
    (blockEquiv h2 X).2.2 = toTypeD X := by
  rfl

/-- Reconstruction uses the existing short-root generators and zero extension. -/
theorem blockEquiv_symm_apply (h2 : IsRegular (2 : R))
    (a b : ι → R) (Y : typeD ι R) :
    (blockEquiv h2).symm (a, (b, Y)) =
      (∑ i, a i • typeBShortRootGenerator i) +
        (∑ i, b i • typeBShortNegativeRootGenerator i) + ofTypeD Y := by
  rfl

/-- A zero-extended even orthogonal matrix has no short-root coordinates. -/
@[simp]
theorem blockEquiv_ofTypeD (h2 : IsRegular (2 : R)) (Y : typeD ι R) :
    blockEquiv h2 (ofTypeD Y) = (0, (0, Y)) := by
  ext <;> simp

/-- A positive short-root generator is a delta in the first coordinate family. -/
@[simp]
theorem blockEquiv_shortRootGenerator (h2 : IsRegular (2 : R)) (i : ι) :
    blockEquiv h2 (typeBShortRootGenerator i) = (Pi.single i 1, (0, 0)) := by
  ext <;> simp [typeBShortRootMatrix_def, Matrix.toBlocks₂₂, Matrix.single_apply,
    Pi.single_apply, eq_comm]

/-- A negative short-root generator is a delta in the second coordinate family. -/
@[simp]
theorem blockEquiv_shortNegativeRootGenerator (h2 : IsRegular (2 : R)) (i : ι) :
    blockEquiv h2 (typeBShortNegativeRootGenerator i) = (0, (Pi.single i 1, 0)) := by
  ext <;> simp [typeBShortNegativeRootMatrix_def, Matrix.toBlocks₂₂, Matrix.single_apply,
    Pi.single_apply, eq_comm]

end LieAlgebra.Orthogonal.typeB
