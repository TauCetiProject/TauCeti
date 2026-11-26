/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Rescaling inner-product-scaling linear equivalences to linear isometries

When `T : E ≃ₗ[𝕜] F` scales the inner product by a positive real constant `r`
(`⟪T x, T y⟫_𝕜 = (r : 𝕜) * ⟪x, y⟫_𝕜`), composing `T` with `LinearEquiv.smulOfNeZero` at `(√r)⁻¹`
yields a linear isometry equivalence `LinearEquiv.rescaleLinearIsometryEquiv`.

## References

* N. Bourbaki, *Topological Vector Spaces*, Chapters 1–5, Springer (1987), Chapter V, §1.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace LinearEquiv

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Rescaling `T : E ≃ₗ[𝕜] F` satisfying `⟪T x, T y⟫_𝕜 = (r : 𝕜) * ⟪x, y⟫_𝕜` (`0 < r`) by `(√r)⁻¹`
gives a linear isometry equivalence `E ≃ₗᵢ[𝕜] F`. -/
def rescaleLinearIsometryEquiv (T : E ≃ₗ[𝕜] F) {r : ℝ} (hr : 0 < r)
    (hT : ∀ x y, ⟪T x, T y⟫_𝕜 = (r : 𝕜) * ⟪x, y⟫_𝕜) : E ≃ₗᵢ[𝕜] F :=
  have hsqrt : Real.sqrt r ≠ 0 := Real.sqrt_ne_zero'.mpr hr
  have hc : (((Real.sqrt r)⁻¹ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (inv_ne_zero hsqrt)
  (T.trans (LinearEquiv.smulOfNeZero 𝕜 F (((Real.sqrt r)⁻¹ : ℝ) : 𝕜) hc)).isometryOfInner
    fun x y ↦ by
      have hne : (Real.sqrt r : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hsqrt
      have hr' : (r : 𝕜) = (Real.sqrt r : 𝕜) * (Real.sqrt r : 𝕜) := by
        exact_mod_cast (Real.mul_self_sqrt hr.le).symm
      simp only [trans_apply, smulOfNeZero_apply, inner_smul_left, inner_smul_right, hT,
        RCLike.ofReal_inv, RCLike.conj_inv, RCLike.conj_ofReal, hr']
      field_simp

/-- Evaluating `T.rescaleLinearIsometryEquiv hr hT` scales `T x` by `(√r)⁻¹`. -/
@[simp]
theorem rescaleLinearIsometryEquiv_apply (T : E ≃ₗ[𝕜] F) {r : ℝ} (hr : 0 < r)
    (hT : ∀ x y, ⟪T x, T y⟫_𝕜 = (r : 𝕜) * ⟪x, y⟫_𝕜) (x : E) :
    T.rescaleLinearIsometryEquiv hr hT x = (((Real.sqrt r)⁻¹ : ℝ) : 𝕜) • T x := by
  simp [rescaleLinearIsometryEquiv]

/-- Evaluating `(T.rescaleLinearIsometryEquiv hr hT).symm` scales `T.symm y` by `√r`. -/
@[simp]
theorem rescaleLinearIsometryEquiv_symm_apply (T : E ≃ₗ[𝕜] F) {r : ℝ} (hr : 0 < r)
    (hT : ∀ x y, ⟪T x, T y⟫_𝕜 = (r : 𝕜) * ⟪x, y⟫_𝕜) (y : F) :
    (T.rescaleLinearIsometryEquiv hr hT).symm y = ((Real.sqrt r : ℝ) : 𝕜) • T.symm y := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  simp [smul_smul, Real.sqrt_ne_zero'.mpr hr]

end LinearEquiv

end
