/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.LinearAlgebra.Determinant

import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Determinant of an operator compression to the range of an injection

Let `u : U →ₗ[𝕜] V` be an injective linear map between finite-dimensional inner product spaces
over `𝕜` (`[RCLike 𝕜]`), and let `T : Module.End 𝕜 V`. Because `u.adjoint` annihilates
`(LinearMap.range u)ᗮ`, the pullback `u.adjoint ∘ₗ T ∘ₗ u` factors as `u.adjoint ∘ₗ u` composed
with the conjugate of the compression `pr ∘ T|_{range u}` along `LinearEquiv.ofInjective u hu`
(`TauCeti.adjoint_comp_comp_eq_comp_compression`).

Taking determinants yields
`(u.adjoint ∘ₗ u).det * (pr ∘ T|_{range u}).det = (u.adjoint ∘ₗ T ∘ₗ u).det`
(`TauCeti.det_adjoint_comp_mul_det_compression`), which reduces to
`(pr ∘ T|_{range u}).det = (u.adjoint ∘ₗ T ∘ₗ u).det` when `u.adjoint ∘ₗ u = 1`
(`TauCeti.det_compression_eq_det_adjoint_comp`).

## Main results

* `TauCeti.adjoint_comp_comp_eq_comp_compression`: factorization of `u.adjoint ∘ₗ T ∘ₗ u` through
  the compression of `T` to `LinearMap.range u`.
* `TauCeti.det_adjoint_comp_mul_det_compression`: determinant product formula for the compression.
* `TauCeti.det_compression_eq_det_adjoint_comp`: equality of determinants when `u.adjoint ∘ₗ u = 1`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/New/OneLift/LiftVolumeHeight.lean`
(`New.normDet_sq_mul_det_compression`).
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 U V : Type*} [RCLike 𝕜]
  [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [Module.Finite 𝕜 U]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [Module.Finite 𝕜 V]

/-- For an injective linear map `u : U →ₗ[𝕜] V` and `T : Module.End 𝕜 V`, the operator
`u.adjoint ∘ₗ T ∘ₗ u` factors as `u.adjoint ∘ₗ u` composed with the conjugate of the compression
of `T` to `LinearMap.range u`. -/
theorem adjoint_comp_comp_eq_comp_compression (T : Module.End 𝕜 V) {u : U →ₗ[𝕜] V}
    (hu : Function.Injective u) :
    u.adjoint ∘ₗ T ∘ₗ u =
      (u.adjoint ∘ₗ u) ∘ₗ
        ((LinearEquiv.ofInjective u hu).symm.toLinearMap ∘ₗ
          ((LinearMap.range u).orthogonalProjectionOnto.toLinearMap ∘ₗ
            T.domRestrict (LinearMap.range u)) ∘ₗ
          (LinearEquiv.ofInjective u hu).toLinearMap) := by
  let e : U ≃ₗ[𝕜] LinearMap.range u := LinearEquiv.ofInjective u hu
  have happly (z : LinearMap.range u) : u (e.symm z) = z :=
    congrArg Subtype.val (e.apply_symm_apply z)
  refine LinearMap.ext fun y ↦ ext_inner_left 𝕜 fun x ↦ ?_
  have hproj : ⟪u x, ((LinearMap.range u).orthogonalProjectionOnto (T (u y)) : V)⟫_𝕜 =
      ⟪u x, T (u y)⟫_𝕜 :=
    (LinearMap.range u).inner_orthogonalProjectionOnto_eq_of_mem_left ⟨u x, x, rfl⟩ (T (u y))
  simpa [LinearMap.adjoint_inner_right, happly, e] using hproj.symm

/-- For an injective linear map `u : U →ₗ[𝕜] V` and `T : Module.End 𝕜 V`, the determinant of
`u.adjoint ∘ₗ u` times the determinant of the compression of `T` to `LinearMap.range u` equals the
determinant of `u.adjoint ∘ₗ T ∘ₗ u`. -/
theorem det_adjoint_comp_mul_det_compression (T : Module.End 𝕜 V) {u : U →ₗ[𝕜] V}
    (hu : Function.Injective u) :
    (u.adjoint ∘ₗ u).det *
        ((LinearMap.range u).orthogonalProjectionOnto.toLinearMap ∘ₗ
          T.domRestrict (LinearMap.range u)).det =
      (u.adjoint ∘ₗ T ∘ₗ u).det := by
  rw [adjoint_comp_comp_eq_comp_compression T hu, LinearMap.det_comp]
  exact congrArg ((u.adjoint ∘ₗ u).det * ·)
    (LinearMap.det_conj _ (LinearEquiv.ofInjective u hu).symm).symm

/-- If `u : U →ₗ[𝕜] V` satisfies `u.adjoint ∘ₗ u = 1`, then the determinant of the compression of
`T` to `LinearMap.range u` equals the determinant of `u.adjoint ∘ₗ T ∘ₗ u`. -/
theorem det_compression_eq_det_adjoint_comp (T : Module.End 𝕜 V) {u : U →ₗ[𝕜] V}
    (hiso : u.adjoint ∘ₗ u = 1) :
    ((LinearMap.range u).orthogonalProjectionOnto.toLinearMap ∘ₗ
        T.domRestrict (LinearMap.range u)).det =
      (u.adjoint ∘ₗ T ∘ₗ u).det := by
  have hu : Function.Injective u :=
    Function.LeftInverse.injective (g := u.adjoint) fun x ↦ by
      simpa using LinearMap.congr_fun hiso x
  simpa [hiso] using det_adjoint_comp_mul_det_compression T hu

end TauCeti
