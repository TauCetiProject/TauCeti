/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.OperatorNorm
public import TauCeti.Analysis.Distribution.TestFunction.Postcomp

/-!
# Complexifying bilinear maps on supported smooth functions

A real-bilinear map `B` on real smooth functions supported in compact sets `K₁` and `K₂`, with
values in a complex normed space, extends to a complex-bilinear map on complex ones,
`(φ, ψ) ↦ B (Re φ) (Re ψ) - B (Im φ) (Im ψ) + i (B (Re φ) (Im ψ) + B (Im φ) (Re ψ))`
(`LinearMap.complexifySupportedIn`). On real functions it is `B` again
(`LinearMap.complexifySupportedIn_postcompLM_ofRealCLM`), and a bound of `B` by a product of
`C^k` seminorms gives one of the extension, with an extra factor `4`
(`LinearMap.norm_complexifySupportedIn_le`). This is how kernel theorems stated for complex test
functions apply to real ones.
-/

public section

noncomputable section

open Complex ContDiffMapSupportedIn TopologicalSpace
open scoped Distributions

namespace LinearMap

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D]
  [NormedSpace ℝ D] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {K₁ : Compacts E} {K₂ : Compacts D} {n : ℕ∞}

/-- The complex-bilinear extension
`(φ, ψ) ↦ B (Re φ) (Re ψ) - B (Im φ) (Im ψ) + i (B (Re φ) (Im ψ) + B (Im φ) (Re ψ))` of a
real-bilinear map on real smooth functions supported in compact sets to complex ones. -/
def complexifySupportedIn (B : 𝓓^{n}_{K₁}(E, ℝ) →ₗ[ℝ] 𝓓^{n}_{K₂}(D, ℝ) →ₗ[ℝ] F) :
    𝓓^{n}_{K₁}(E, ℂ) →ₗ[ℂ] 𝓓^{n}_{K₂}(D, ℂ) →ₗ[ℂ] F :=
  LinearMap.mk₂ ℂ (fun φ ψ ↦
      B (postcompLM (𝕜 := ℝ) reCLM φ) (postcompLM (𝕜 := ℝ) reCLM ψ) -
        B (postcompLM (𝕜 := ℝ) imCLM φ) (postcompLM (𝕜 := ℝ) imCLM ψ) +
      I • (B (postcompLM (𝕜 := ℝ) reCLM φ) (postcompLM (𝕜 := ℝ) imCLM ψ) +
        B (postcompLM (𝕜 := ℝ) imCLM φ) (postcompLM (𝕜 := ℝ) reCLM ψ)))
    (fun φ φ' ψ ↦ by simp only [map_add, LinearMap.add_apply]; module)
    (fun c φ ψ ↦ by
      simp only [postcompLM_reCLM_smul, postcompLM_imCLM_smul, map_sub, map_add, map_smul,
        LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, ← Complex.coe_smul]
      conv_rhs => rw [← re_add_im c]
      match_scalars <;> apply Complex.ext <;> simp)
    (fun φ ψ ψ' ↦ by simp only [map_add]; module)
    (fun c φ ψ ↦ by
      simp only [postcompLM_reCLM_smul, postcompLM_imCLM_smul, map_sub, map_add, map_smul,
        ← Complex.coe_smul]
      conv_rhs => rw [← re_add_im c]
      match_scalars <;> apply Complex.ext <;> simp)

theorem complexifySupportedIn_apply (B : 𝓓^{n}_{K₁}(E, ℝ) →ₗ[ℝ] 𝓓^{n}_{K₂}(D, ℝ) →ₗ[ℝ] F)
    (φ : 𝓓^{n}_{K₁}(E, ℂ)) (ψ : 𝓓^{n}_{K₂}(D, ℂ)) :
    complexifySupportedIn B φ ψ =
      B (postcompLM (𝕜 := ℝ) reCLM φ) (postcompLM (𝕜 := ℝ) reCLM ψ) -
        B (postcompLM (𝕜 := ℝ) imCLM φ) (postcompLM (𝕜 := ℝ) imCLM ψ) +
      I • (B (postcompLM (𝕜 := ℝ) reCLM φ) (postcompLM (𝕜 := ℝ) imCLM ψ) +
        B (postcompLM (𝕜 := ℝ) imCLM φ) (postcompLM (𝕜 := ℝ) reCLM ψ)) := by
  simp only [complexifySupportedIn, mk₂_apply]

/-- On real functions, the complex-bilinear extension of `B` is `B`. -/
@[simp]
theorem complexifySupportedIn_postcompLM_ofRealCLM
    (B : 𝓓^{n}_{K₁}(E, ℝ) →ₗ[ℝ] 𝓓^{n}_{K₂}(D, ℝ) →ₗ[ℝ] F)
    (φ : 𝓓^{n}_{K₁}(E, ℝ)) (ψ : 𝓓^{n}_{K₂}(D, ℝ)) :
    complexifySupportedIn B (postcompLM (𝕜 := ℝ) ofRealCLM φ)
      (postcompLM (𝕜 := ℝ) ofRealCLM ψ) = B φ ψ := by
  simp [complexifySupportedIn_apply]

/-- A bound of `B` by a product of `C^k` seminorms gives one of its complex-bilinear extension. -/
theorem norm_complexifySupportedIn_le
    {B : 𝓓^{n}_{K₁}(E, ℝ) →ₗ[ℝ] 𝓓^{n}_{K₂}(D, ℝ) →ₗ[ℝ] F} {C : ℝ} {k : ℕ} (hC : 0 ≤ C)
    (hB : ∀ φ ψ, ‖B φ ψ‖ ≤ C * ContDiffMapSupportedIn.supSeminorm ℝ E ℝ n K₁ k φ *
      ContDiffMapSupportedIn.supSeminorm ℝ D ℝ n K₂ k ψ)
    (φ : 𝓓^{n}_{K₁}(E, ℂ)) (ψ : 𝓓^{n}_{K₂}(D, ℂ)) :
    ‖complexifySupportedIn B φ ψ‖ ≤ 4 * C * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ n K₁ k φ *
      ContDiffMapSupportedIn.supSeminorm ℂ D ℂ n K₂ k ψ := by
  have h {T₁ T₂ : ℂ →L[ℝ] ℝ} (h₁ : ‖T₁‖ ≤ 1) (h₂ : ‖T₂‖ ≤ 1) :
      ‖B (postcompLM (𝕜 := ℝ) T₁ φ) (postcompLM (𝕜 := ℝ) T₂ ψ)‖ ≤
        C * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ n K₁ k φ *
          ContDiffMapSupportedIn.supSeminorm ℂ D ℂ n K₂ k ψ :=
    (hB _ _).trans (by gcongr <;> exact supSeminorm_postcompLM_le ‹_› k _)
  have hre : ‖reCLM‖ ≤ 1 := reCLM_norm.le
  have him : ‖imCLM‖ ≤ 1 := imCLM_norm.le
  rw [complexifySupportedIn_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_I, one_mul]
  linarith [norm_sub_le (B (postcompLM (𝕜 := ℝ) reCLM φ) (postcompLM (𝕜 := ℝ) reCLM ψ))
      (B (postcompLM (𝕜 := ℝ) imCLM φ) (postcompLM (𝕜 := ℝ) imCLM ψ)),
    norm_add_le (B (postcompLM (𝕜 := ℝ) reCLM φ) (postcompLM (𝕜 := ℝ) imCLM ψ))
      (B (postcompLM (𝕜 := ℝ) imCLM φ) (postcompLM (𝕜 := ℝ) reCLM ψ)),
    h hre hre, h him him, h hre him, h him hre]

end LinearMap
