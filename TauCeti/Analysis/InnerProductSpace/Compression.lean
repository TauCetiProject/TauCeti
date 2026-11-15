/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Compressions of operators

For bounded operators `A : E → E` and `X : F → E` between Hilbert spaces, the *compression* of
`A` along `X` is the operator `X† A X` on `F`, `ContinuousLinearMap.compression A X`. When `X` is
an isometry it is `A` cut down to the subspace `range X`, read in the coordinates of `F`. This
file records its basic algebra: it is additive and homogeneous in `A`, commutes with adjoints,
preserves symmetry, and compressing in two steps is compressing along the composite. Compressing
to the orthogonal complement of an eigenvector creates no new eigenvalues
(`ContinuousLinearMap.hasEigenvalue_of_hasEigenvalue_compression_orthogonal_span_singleton`).

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

/-- If `u` is an eigenvector of `A`, with eigenvalue `λ`, then `A` is block upper triangular along
`E = 𝕜 u ⊕ u^⊥`, so every eigenvalue of the compression of `A` to `u^⊥` is an eigenvalue of `A`.
An eigenvector `k ∈ u^⊥` of the compression, with eigenvalue `μ`, gives the eigenvector `u` of `A`
if `μ = λ`, and the eigenvector `k + ⟪u, A k⟫ / (‖u‖² (μ - λ)) • u` of `A` otherwise. -/
theorem hasEigenvalue_of_hasEigenvalue_compression_orthogonal_span_singleton {A : E →L[𝕜] E}
    {u : E} {lam μ : 𝕜} (hu : u ≠ 0) (hAu : A u = lam • u)
    (hμ : Module.End.HasEigenvalue
      (A.compression (𝕜 ∙ u)ᗮ.subtypeL : Module.End 𝕜 (𝕜 ∙ u)ᗮ) μ) :
    Module.End.HasEigenvalue (A : Module.End 𝕜 E) μ := by
  set K := (𝕜 ∙ u)ᗮ
  obtain ⟨k, hk, hk0⟩ := hμ.exists_hasEigenvector
  have hQk : K.orthogonalProjectionOnto (A k) = μ • k := by
    rw [← Module.End.mem_eigenspace_iff.mp hk]
    simp [K, Submodule.adjoint_subtypeL]
  -- Splitting `A k` along `𝕜 u ⊕ K`.
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp ((𝕜 ∙ u).starProjection_apply_mem (A k))
  have hAk : A k = b • u + μ • (k : E) := by
    conv_lhs => rw [← (𝕜 ∙ u).starProjection_add_starProjection_orthogonal (A k)]
    rw [← hb, Submodule.starProjection_apply, hQk, Submodule.coe_smul]
  by_cases hμl : μ = lam
  · subst hμl
    exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hAu, hu⟩
  -- Otherwise `k + b / (μ - λ) • u` is an eigenvector of `A` with eigenvalue `μ`.
  have hne : μ - lam ≠ 0 := sub_ne_zero.mpr hμl
  set z : E := (k : E) + (b / (μ - lam)) • u
  have hAz : A z = μ • z := by
    simp only [z, map_add, map_smul, hAk, hAu, smul_add, smul_smul]
    have : b + b / (μ - lam) * lam = μ * (b / (μ - lam)) := by
      field_simp
      ring
    rw [← this, add_smul]
    abel
  have hz0 : z ≠ 0 := by
    intro hz
    apply hk0
    have := congrArg K.orthogonalProjectionOnto hz
    rwa [map_add, map_smul, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
      Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, smul_zero,
      add_zero, map_zero] at this
  exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.mpr hAz, hz0⟩

end ContinuousLinearMap
