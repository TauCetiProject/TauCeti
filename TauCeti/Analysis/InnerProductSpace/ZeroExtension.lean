/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Zero extension of a rectangular map to the square `L²` product

A linear map `A : E →ₗ[𝕜] F` between inner product spaces extends by zero to an endomorphism
`(x, y) ↦ (0, A x)` of the `L²` product `E × F`. For finite-dimensional `E` and `F` this
endomorphism has the same zero-padded singular values as `A`, so statements about square
operators transfer to rectangular maps.

For subspaces `S` of `F` and `T` of `E`, block extension sends a map
`T →ₗ[𝕜] S` to `E →ₗ[𝕜] F` by projecting onto `T` and including the
result in `F`. It also preserves all singular values.

## Main declarations

* `LinearMap.zeroExtension`: the zero extension `(x, y) ↦ (0, A x)`.
* `LinearMap.singularValues_zeroExtension`: the zero extension has the singular values of `A`.
* `LinearMap.blockExtend`: extend a map from a subspace block by zero.
* `LinearMap.blockExtend_singularValues`: block extension preserves singular values.
* `LinearMap.blockExtend_orthogonalProjection_comp_eq_of_mem`: supported maps
  coincide with the zero extension of their compressed blocks.

## Source

Adapted from the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(`ForTauCeti/Analysis/InnerProductSpace/ZeroExtension.lean`).
Original copyright (c) 2026 Kitware, Inc.; Apache-2.0.
-/

public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace LinearMap

/-- The **zero extension** of `A : E →ₗ[𝕜] F` to an endomorphism of the `L²` product `E × F`:
the map `(x, y) ↦ (0, A x)`. -/
noncomputable def zeroExtension (A : E →ₗ[𝕜] F) : WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ inr 𝕜 E F ∘ₗ A ∘ₗ WithLp.fstₗ 2 𝕜 E F

@[simp]
theorem zeroExtension_apply (A : E →ₗ[𝕜] F) (z : WithLp 2 (E × F)) :
    A.zeroExtension z = WithLp.toLp 2 (0, A z.fst) :=
  (rfl)

/-- **Singular values of the zero extension**: extending `A : E →ₗ[𝕜] F` by zero to an
endomorphism of the `L²` product `E × F` leaves its zero-padded singular-value sequence
unchanged. -/
@[simp]
theorem singularValues_zeroExtension [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (A : E →ₗ[𝕜] F) : A.zeroExtension.singularValues = A.singularValues := by
  -- `A.zeroExtension = B ∘ fst` for `B = (0, A ·)`, and the adjoint of `fst` is the inclusion
  -- of the first factor; both `B` and that inclusion preserve norms.
  set B : E →ₗ[𝕜] WithLp 2 (E × F) :=
    (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ inr 𝕜 E F ∘ₗ A
  have hB : B.singularValues = A.singularValues :=
    singularValues_eq_of_norm_apply_eq fun x ↦ by simp [B, WithLp.norm_toLp_snd]
  have hA : A.zeroExtension = B ∘ₗ WithLp.fstₗ 2 𝕜 E F := rfl
  rw [hA, ← singularValues_adjoint, adjoint_comp, WithLp.adjoint_fstₗ, ← hB,
    ← singularValues_adjoint B]
  exact singularValues_eq_of_norm_apply_eq fun x ↦ by simp [WithLp.norm_toLp_fst]

/-! ### Zero extension of orthogonally projected subspace blocks -/

section BlockExtension

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
  (S : Submodule 𝕜 F) (T : Submodule 𝕜 E)
  [S.HasOrthogonalProjection] [T.HasOrthogonalProjection]

/-- Zero extension of `X : T → S` to an operator `E → F`, by projecting onto
`T`, applying `X`, and including the result in `F`. -/
noncomputable def blockExtend : (T →ₗ[𝕜] S) →ₗ[𝕜] (E →ₗ[𝕜] F) :=
  (LinearMap.compRight 𝕜 S.subtype) ∘ₗ
    (LinearMap.lcomp 𝕜 S T.orthogonalProjectionOnto.toLinearMap)

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [S.HasOrthogonalProjection] in
@[simp]
theorem blockExtend_apply (X : T →ₗ[𝕜] S) (x : E) :
    blockExtend S T X x = (X (T.orthogonalProjectionOnto x) : F) := by
  simp [blockExtend]

omit [S.HasOrthogonalProjection] in
/-- Zero extension by isometric inclusion and orthogonal projection preserves
all singular values, including multiplicities and trailing zeros. -/
@[simp]
theorem blockExtend_singularValues (X : T →ₗ[𝕜] S) :
    (blockExtend S T X).singularValues = X.singularValues := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace T := FiniteDimensional.complete 𝕜 T
  have hadj : LinearMap.adjoint T.subtypeₗᵢ.toLinearMap =
      T.orthogonalProjectionOnto.toLinearMap := by
    have hsubtype : T.subtypeₗᵢ.toLinearMap.toContinuousLinearMap = T.subtypeL := by
      ext x
      rfl
    rw [LinearMap.adjoint_eq_toCLM_adjoint, hsubtype, T.adjoint_subtypeL]
  -- The isometric inclusion and the adjoint inclusion preserve singular values.
  change (S.subtypeₗᵢ.toLinearMap ∘ₗ X ∘ₗ
    T.orthogonalProjectionOnto.toLinearMap).singularValues = X.singularValues
  rw [← hadj]
  -- Express the inclusion as the underlying map of the isometric embedding;
  -- then both singular-value invariance lemmas match explicitly.
  change (S.subtypeₗᵢ.toLinearMap ∘ₗ X ∘ₗ
    LinearMap.adjoint T.subtypeₗᵢ.toLinearMap).singularValues = X.singularValues
  simp only [LinearMap.singularValues_linearIsometry_comp,
    LinearMap.singularValues_comp_adjoint_linearIsometry]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- An operator with range in `S` and vanishing on `Tᗮ` is the zero
extension of its compression to `T → S`. -/
theorem blockExtend_orthogonalProjection_comp_eq_of_mem (X : E →ₗ[𝕜] F)
    (hXS : ∀ x, X x ∈ S) (hXT : ∀ x ∈ Tᗮ, X x = 0) :
    blockExtend S T
      (S.orthogonalProjectionOnto.toLinearMap ∘ₗ X ∘ₗ T.subtypeL.toLinearMap) = X := by
  ext x
  -- Expand the named extension and identify the inclusion of the projected vector.
  change S.starProjection (X (T.starProjection x)) = X x
  rw [S.starProjection_eq_self_iff.mpr (hXS _)]
  have hz : X (x - T.starProjection x) = 0 :=
    hXT _ (T.sub_starProjection_mem_orthogonal x)
  have hx : X x - X (T.starProjection x) = 0 := by
    simpa only [map_sub] using hz
  exact (sub_eq_zero.mp hx).symm

end BlockExtension

end LinearMap
