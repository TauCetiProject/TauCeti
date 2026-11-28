/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.LinearAlgebra.Prod

/-!
# Linear isometric equivalences on product spaces

This file provides linear isometric equivalences on product spaces `E × F`:

* `LinearIsometryEquiv.prodCongr`: componentwise products of linear isometric equivalences, with
  pointwise evaluation (`LinearIsometryEquiv.prodCongr_apply`) and inverse
  (`LinearIsometryEquiv.prodCongr_symm`).
* `LinearIsometryEquiv.negFst`: the reflection `(x, y) ↦ (-x, y)` negating the first coordinate,
  which on `ℝ × ℝ` exchanges the two ends of a strip or cylinder. Precomposition with it
  preserves operator norms by Mathlib's `ContinuousLinearMap.opNorm_comp_linearIsometryEquiv`.
-/

public section

namespace LinearIsometryEquiv

section ProdCongr

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

end ProdCongr

section NegFst

variable (R E F : Type*) [Semiring R] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [Module R E] [Module R F]

/-- The reflection `(x, y) ↦ (-x, y)` of `E × F`, negating the first coordinate, as a linear
isometry equivalence. -/
def negFst : E × F ≃ₗᵢ[R] E × F where
  toLinearEquiv := (LinearEquiv.neg R).prodCongr (LinearEquiv.refl R F)
  norm_map' z := by simp [Prod.norm_def]

@[simp]
theorem negFst_apply (z : E × F) : negFst R E F z = (-z.1, z.2) := (rfl)

theorem coe_negFst : ⇑(negFst R E F) = Prod.map Neg.neg id := (rfl)

/-- The reflection `negFst` is an involution. -/
@[simp]
theorem symm_negFst : (negFst R E F).symm = negFst R E F := by
  ext z <;> rfl

end NegFst

end LinearIsometryEquiv
