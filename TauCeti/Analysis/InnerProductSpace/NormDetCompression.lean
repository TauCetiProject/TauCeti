/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Determinant of the compression of an operator and the squared norm determinant

Let `U` and `V` be finite-dimensional inner product spaces over `𝕜` (with `[RCLike 𝕜]`),
`u : U →ₗ[𝕜] V` a linear map, and `T : Module.End 𝕜 V` an endomorphism. Writing `pr` for the
orthogonal projection of `V` onto `u.range`, this file proves that
`(u.normDet ^ 2 : 𝕜) * (pr ∘ₗ T.domRestrict u.range).det = (u.adjoint ∘ₗ T ∘ₗ u).det`.
When `u` is injective, `u*` annihilates `u.rangeᗮ`, factoring `u* T u` as `(u* u)` composed with
a conjugate of the compression `pr ∘ₗ T|_{u.range}`. When `u` is not injective, both sides vanish.

## Provenance

Extracted and generalized from `grh-lean`
(https://github.com/lsernau/grh-lean at commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC), file `src/New/OneLift/LiftVolumeHeight.lean`
(`normDet_sq_mul_det_compression`).
-/

public section

namespace TauCeti

open LinearMap

/-- For any linear map `u : U →ₗ[𝕜] V` between finite-dimensional inner product spaces over
`[RCLike 𝕜]` and any endomorphism `T` of `V`, the determinant of the compression of `T` to
`u.range` multiplied by `u.normDet ^ 2` equals `(u.adjoint ∘ₗ T ∘ₗ u).det`. -/
theorem normDet_sq_mul_det_compression {𝕜 U V : Type*} [RCLike 𝕜]
    [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [FiniteDimensional 𝕜 U]
    [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (T : Module.End 𝕜 V) (u : U →ₗ[𝕜] V) :
    (↑(u.normDet ^ 2) : 𝕜) *
        (u.range.orthogonalProjectionOnto.toLinearMap ∘ₗ T.domRestrict u.range).det =
      (u.adjoint ∘ₗ T ∘ₗ u).det := by
  by_cases hu : Function.Injective u
  · let e : U ≃ₗ[𝕜] u.range := .ofInjective u hu
    let S : Module.End 𝕜 u.range :=
      u.range.orthogonalProjectionOnto.toLinearMap ∘ₗ T.domRestrict u.range
    have h_apply (z : u.range) : u (e.symm z) = z := congrArg Subtype.val (e.apply_symm_apply z)
    have h_comp : u.adjoint ∘ₗ T ∘ₗ u =
        (u.adjoint ∘ₗ u) ∘ₗ (e.symm.toLinearMap ∘ₗ S ∘ₗ e.symm.symm.toLinearMap) := by
      refine LinearMap.ext fun y ↦ ext_inner_left 𝕜 fun x ↦ ?_
      have h_proj : inner 𝕜 (u x) (u.range.starProjection (T (u y))) = inner 𝕜 (u x) (T (u y)) :=
        u.range.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨u x, x, rfl⟩ (T (u y))
      simpa [adjoint_inner_right, h_apply, S, e] using h_proj.symm
    rw [h_comp, det_comp, LinearMap.det_conj, ← u.normDet_sq, RCLike.ofReal_pow]
  · have hker : LinearMap.ker u ≠ ⊥ := mt LinearMap.ker_eq_bot.mp hu
    have hker1 : LinearMap.ker (u.adjoint ∘ₗ u) ≠ ⊥ :=
      ne_bot_of_le_ne_bot hker (LinearMap.ker_le_ker_comp u u.adjoint)
    have hker2 : LinearMap.ker (u.adjoint ∘ₗ T ∘ₗ u) ≠ ⊥ :=
      ne_bot_of_le_ne_bot hker (LinearMap.ker_le_ker_comp u (u.adjoint ∘ₗ T))
    have hdet1 : (u.adjoint ∘ₗ u).det = 0 := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker1
    have hdet2 : (u.adjoint ∘ₗ T ∘ₗ u).det = 0 := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker2
    rw [u.normDet_sq, hdet1, hdet2, zero_mul]

end TauCeti
