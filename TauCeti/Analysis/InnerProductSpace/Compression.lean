/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Compressions of operators

For bounded operators `A : E → E` and `X : F → E` between Hilbert spaces, the *compression* of
`A` along `X` is the operator `X† A X` on `F`, `ContinuousLinearMap.compression A X`. When `X` is
an isometry it is `A` cut down to the subspace `range X`, read in the coordinates of `F`. This
file records its basic algebra: it is additive and homogeneous in `A`, commutes with adjoints,
preserves symmetry, and compressing in two steps is compressing along the composite.

Compressions model operators on a trial subspace in the Rayleigh–Ritz procedure, and compress
representations to invariant subspaces.
-/

public section

noncomputable section

open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

namespace ContinuousLinearMap

variable (A : E →L[𝕜] E) (X : F →L[𝕜] E)

/-- The *compression* `X† A X` of an operator `A` on `E` along an operator `X : F →L[𝕜] E`. When
`X` is an isometry, it is `A` cut down to the trial subspace `range X`, in the coordinates of
`F`. -/
def compression : F →L[𝕜] F :=
  adjoint X ∘L A ∘L X

theorem compression_def : A.compression X = adjoint X ∘L A ∘L X :=
  (rfl)

@[simp]
theorem compression_apply (x : F) : A.compression X x = adjoint X (A (X x)) :=
  (rfl)

/-- Compression sends the zero operator to zero. -/
@[simp]
theorem compression_zero : (0 : E →L[𝕜] E).compression X = 0 := by
  ext x
  simp

/-- Compression preserves addition in the operator argument. -/
@[simp]
theorem compression_add (B : E →L[𝕜] E) :
    (A + B).compression X = A.compression X + B.compression X := by
  ext x
  simp

/-- Compression preserves subtraction in the operator argument. -/
@[simp]
theorem compression_sub (B : E →L[𝕜] E) :
    (A - B).compression X = A.compression X - B.compression X := by
  ext x
  simp

/-- Compression preserves scalar multiplication in the operator argument. -/
@[simp]
theorem compression_smul (c : 𝕜) : (c • A).compression X = c • A.compression X := by
  ext x
  simp

/-- The matrix coefficients of the compression are those of `A` on the images under `X`. -/
theorem inner_compression_apply (x y : F) :
    ⟪x, A.compression X y⟫_𝕜 = ⟪X x, A (X y)⟫_𝕜 :=
  adjoint_inner_right X x (A (X y))

@[simp]
theorem compression_id : A.compression (ContinuousLinearMap.id 𝕜 E) = A := by
  ext x
  simp [compression_def, adjoint_id]

/-- Compressing in two steps is compressing along the composite. -/
theorem compression_comp {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [CompleteSpace G] (Y : G →L[𝕜] F) :
    A.compression (X ∘L Y) = (A.compression X).compression Y := by
  simp only [compression_def, adjoint_comp, comp_assoc]

/-- The adjoint of the compression is the compression of the adjoint. -/
@[simp]
theorem adjoint_compression : adjoint (A.compression X) = (adjoint A).compression X := by
  simp only [compression_def, adjoint_comp, adjoint_adjoint, comp_assoc]

/-- The compression of a symmetric operator is symmetric. -/
theorem isSymmetric_compression {A : E →L[𝕜] E} (hA : (A : E →ₗ[𝕜] E).IsSymmetric) :
    (A.compression X : F →ₗ[𝕜] F).IsSymmetric :=
  isSelfAdjoint_iff_isSymmetric.1 <| (isSelfAdjoint_iff_isSymmetric.2 hA).adjoint_conj X

end ContinuousLinearMap
