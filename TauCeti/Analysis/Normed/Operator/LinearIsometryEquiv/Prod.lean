/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Componentwise products of linear isometric equivalences

Componentwise products of linear isometric equivalences on product spaces are again linear
isometric equivalences (`LinearIsometryEquiv.prodCongr`), with pointwise evaluation and inverse
given by `LinearIsometryEquiv.prodCongr_apply` and `LinearIsometryEquiv.prodCongr_symm`.
-/

public section

namespace LinearIsometryEquiv

variable {𝕜 E F E' F' : Type*} [Semiring 𝕜]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F']
  [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 E'] [Module 𝕜 F']

/-- Componentwise product of two linear isometric equivalences on `E × F`. -/
def prodCongr (e₁ : E ≃ₗᵢ[𝕜] E') (e₂ : F ≃ₗᵢ[𝕜] F') : E × F ≃ₗᵢ[𝕜] E' × F' :=
  { e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv with
    norm_map' x := by
      simp only [Prod.norm_def, LinearEquiv.prodCongr_apply, coe_toLinearEquiv, norm_map] }

/-- Evaluation of `LinearIsometryEquiv.prodCongr` at a pair. -/
@[simp, norm_cast]
theorem prodCongr_apply (e₁ : E ≃ₗᵢ[𝕜] E') (e₂ : F ≃ₗᵢ[𝕜] F') (x : E × F) :
    prodCongr e₁ e₂ x = (e₁ x.1, e₂ x.2) := by
  simp [prodCongr]

/-- The inverse of `LinearIsometryEquiv.prodCongr e₁ e₂` is `prodCongr e₁.symm e₂.symm`. -/
@[simp]
theorem prodCongr_symm (e₁ : E ≃ₗᵢ[𝕜] E') (e₂ : F ≃ₗᵢ[𝕜] F') :
    (prodCongr e₁ e₂).symm = prodCongr e₁.symm e₂.symm :=
  LinearIsometryEquiv.ext fun x ↦ (prodCongr e₁ e₂).injective (by simp)

end LinearIsometryEquiv
