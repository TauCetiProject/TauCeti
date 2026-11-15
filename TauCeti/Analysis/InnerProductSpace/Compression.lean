/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Eigenspace.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Compressions of operators

For bounded operators `A : E → E` and `X : F → E` between Hilbert spaces, the *compression* of
`A` along `X` is the operator `X† A X` on `F`, `ContinuousLinearMap.compression A X`. When `X` is
an isometry it is `A` cut down to the subspace `range X`, read in the coordinates of `F`. This
file records its basic algebra: it is additive and homogeneous in `A`, commutes with adjoints and
`star`, satisfies `‖X† A X‖ ≤ ‖X‖² ‖A‖`, preserves symmetry, and compressing in two steps is
compressing along the composite. When `X` is an isometry, compression is contractive, preserves `1`,
and intertwines and is multiplicative at operators commuting with the range projection `X ∘L X†`.
For a complete subspace `U`, `U.subtypeL ∘L U.subtypeL† = U.starProjection`
(`Submodule.subtypeL_comp_adjoint_subtypeL`) and `A.compression U.subtypeL` is
`U.orthogonalProjectionOnto ∘L A ∘L U.subtypeL` (`ContinuousLinearMap.compression_subtypeL`).
Compressing to the orthogonal complement of an eigenvector creates no new eigenvalues
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

/-- Compression preserves the star operation on operators. -/
@[simp]
theorem compression_star : (star A).compression X = star (A.compression X) := by
  simp only [star_eq_adjoint, adjoint_compression]

/-- Operator norm bound for a compression: `‖X† A X‖ ≤ ‖X‖² ‖A‖`. -/
theorem opNorm_compression_le : ‖A.compression X‖ ≤ ‖X‖ ^ 2 * ‖A‖ := by
  calc
    ‖A.compression X‖ = ‖adjoint X ∘L A ∘L X‖ := by rw [compression_def]
    _ ≤ ‖adjoint X‖ * ‖A ∘L X‖ := opNorm_comp_le _ _
    _ ≤ ‖X‖ * (‖A‖ * ‖X‖) := by
      rw [LinearIsometryEquiv.norm_map]
      gcongr
      exact opNorm_comp_le _ _
    _ = ‖X‖ ^ 2 * ‖A‖ := by ring

/-- Compressing `1` along an isometry yields `1`. -/
theorem compression_one_of_isometry {X : F →L[𝕜] E} (hX : Isometry X) :
    (1 : E →L[𝕜] E).compression X = 1 := by
  rw [compression_def, one_def, id_comp, (isometry_iff_adjoint_comp_self X).mp hX]

/-- Compressing along an isometry is contractive, including on the zero space. -/
theorem opNorm_compression_le_of_isometry {X : F →L[𝕜] E} (hX : Isometry X) :
    ‖A.compression X‖ ≤ ‖A‖ := by
  have hXle : ‖X‖ ≤ 1 := X.opNorm_le_bound zero_le_one fun x ↦ by
    rw [hX.norm_map_of_map_zero (map_zero X), one_mul]
  calc
    ‖A.compression X‖ ≤ ‖X‖ ^ 2 * ‖A‖ := A.opNorm_compression_le X
    _ ≤ 1 ^ 2 * ‖A‖ := by gcongr
    _ = ‖A‖ := by ring

/-- If `A` commutes with the range projection `X ∘L X†` of an isometry `X`, then `X` intertwines
`A.compression X` with `A`. -/
theorem comp_compression_of_commute {A : E →L[𝕜] E} {X : F →L[𝕜] E}
    (hX : Isometry X) (hA : Commute (X ∘L adjoint X) A) :
    X ∘L A.compression X = A ∘L X := by
  have hXX : adjoint X ∘L X = 1 := (isometry_iff_adjoint_comp_self X).mp hX
  calc
    X ∘L A.compression X = ((X ∘L adjoint X) * A) ∘L X := by
      simp only [compression_def, mul_def, comp_assoc]
    _ = (A * (X ∘L adjoint X)) ∘L X := by rw [hA.eq]
    _ = A ∘L X ∘L (adjoint X ∘L X) := by simp only [mul_def, comp_assoc]
    _ = A ∘L X := by rw [hXX, one_def, comp_id]

/-- If `A` commutes with the range projection `X ∘L X†` of an isometry `X`, then `X†` intertwines
`A` with `A.compression X`. -/
theorem compression_comp_adjoint_of_commute {A : E →L[𝕜] E} {X : F →L[𝕜] E}
    (hX : Isometry X) (hA : Commute (X ∘L adjoint X) A) :
    A.compression X ∘L adjoint X = adjoint X ∘L A := by
  have hXX : adjoint X ∘L X = 1 := (isometry_iff_adjoint_comp_self X).mp hX
  calc
    A.compression X ∘L adjoint X = adjoint X ∘L (A * (X ∘L adjoint X)) := by
      simp only [compression_def, mul_def, comp_assoc]
    _ = adjoint X ∘L ((X ∘L adjoint X) * A) := by rw [← hA.eq]
    _ = (adjoint X ∘L X) ∘L adjoint X ∘L A := by simp only [mul_def, comp_assoc]
    _ = adjoint X ∘L A := by rw [hXX, one_def, id_comp]

/-- Compression along an isometry `X` is multiplicative on the left at any operator commuting with
the range projection `X ∘L X†`. -/
theorem compression_mul_of_commute_left {A : E →L[𝕜] E} (B : E →L[𝕜] E) {X : F →L[𝕜] E}
    (hX : Isometry X) (hA : Commute (X ∘L adjoint X) A) :
    (A * B).compression X = A.compression X * B.compression X := by
  calc
    (A * B).compression X = (adjoint X ∘L A) ∘L B ∘L X := by
      simp only [compression_def, mul_def, comp_assoc]
    _ = (A.compression X ∘L adjoint X) ∘L B ∘L X := by
      rw [compression_comp_adjoint_of_commute hX hA]
    _ = A.compression X * B.compression X := by simp only [compression_def, mul_def, comp_assoc]

/-- Compression along an isometry `X` is multiplicative on the right at any operator commuting with
the range projection `X ∘L X†`. -/
theorem compression_mul_of_commute_right (A : E →L[𝕜] E) {B : E →L[𝕜] E} {X : F →L[𝕜] E}
    (hX : Isometry X) (hB : Commute (X ∘L adjoint X) B) :
    (A * B).compression X = A.compression X * B.compression X := by
  calc
    (A * B).compression X = adjoint X ∘L A ∘L (B ∘L X) := by
      simp only [compression_def, mul_def, comp_assoc]
    _ = adjoint X ∘L A ∘L (X ∘L B.compression X) := by rw [comp_compression_of_commute hX hB]
    _ = A.compression X * B.compression X := by simp only [compression_def, mul_def, comp_assoc]

/-- If `A` and `B` commute with the range projection `X ∘L X†` of an isometry `X` and their
compressions along `X` commute, then `A * B` and `B * A` agree on the range of `X`. -/
theorem mul_comp_eq_of_commute_compression {A B : E →L[𝕜] E} {X : F →L[𝕜] E}
    (hX : Isometry X) (hA : Commute (X ∘L adjoint X) A) (hB : Commute (X ∘L adjoint X) B)
    (hAB : Commute (A.compression X) (B.compression X)) :
    (A * B) ∘L X = (B * A) ∘L X := by
  calc
    (A * B) ∘L X = X ∘L (A * B).compression X :=
      (comp_compression_of_commute hX (hA.mul_right hB)).symm
    _ = X ∘L (A.compression X * B.compression X) := by
      rw [compression_mul_of_commute_left B hX hA]
    _ = X ∘L (B.compression X * A.compression X) := by rw [hAB.eq]
    _ = X ∘L (B * A).compression X := by
      rw [← compression_mul_of_commute_left A hX hB]
    _ = (B * A) ∘L X := comp_compression_of_commute hX (hB.mul_right hA)

/-- Compressing `A` along `U.subtypeL` is `U.orthogonalProjectionOnto ∘L A ∘L U.subtypeL`. -/
theorem compression_subtypeL (U : Submodule 𝕜 E) [CompleteSpace U] :
    A.compression U.subtypeL = U.orthogonalProjectionOnto ∘L A ∘L U.subtypeL := by
  rw [compression_def, U.adjoint_subtypeL]

/-- Compressing `1` to a complete submodule `U` yields `1`. -/
@[simp]
theorem compression_one_subtypeL (U : Submodule 𝕜 E) [CompleteSpace U] :
    (1 : E →L[𝕜] E).compression U.subtypeL = 1 :=
  compression_one_of_isometry U.subtypeₗᵢ.isometry

/-- Compressing the orthogonal projection onto `U` along `U.subtypeL` yields `1`. -/
@[simp]
theorem compression_starProjection_self (U : Submodule 𝕜 E) [CompleteSpace U] :
    U.starProjection.compression U.subtypeL = 1 := by
  ext x
  simp [compression_apply, U.adjoint_subtypeL]

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

namespace Submodule

/-- For a complete subspace `U` of a Hilbert space `E`, `U.subtypeL ∘L U.subtypeL†` is the
orthogonal projection `U.starProjection`. -/
theorem subtypeL_comp_adjoint_subtypeL (U : Submodule 𝕜 E) [CompleteSpace U] :
    U.subtypeL ∘L ContinuousLinearMap.adjoint U.subtypeL = U.starProjection := by
  rw [U.adjoint_subtypeL, ← U.starProjection_def]

end Submodule
