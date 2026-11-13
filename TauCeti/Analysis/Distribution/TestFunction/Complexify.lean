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
values in a complex vector space, extends to a complex-bilinear map on complex ones,
`(φ, ψ) ↦ B (Re φ) (Re ψ) - B (Im φ) (Im ψ) + i (B (Re φ) (Im ψ) + B (Im φ) (Re ψ))`
(`LinearMap.complexifySupportedIn`). On real functions it is `B` again
(`LinearMap.complexifySupportedIn_postcompCLM_ofRealCLM`), it is the only complex-bilinear map
with this property (`LinearMap.eq_complexifySupportedIn`), and it is real-linear in `B`. A bound
of `B` by a product of `C^k` seminorms gives one of the extension, with an extra factor `4`
(`LinearMap.norm_complexifySupportedIn_le`). This is how kernel theorems stated for complex test
functions apply to real ones.
-/

public section

noncomputable section

open Complex ContDiffMapSupportedIn TopologicalSpace
open scoped Distributions

namespace LinearMap

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D]
  [NormedSpace ℝ D] {K₁ : Compacts E} {K₂ : Compacts D} {n₁ n₂ : ℕ∞}

section Module

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [Module ℂ F] [IsScalarTower ℝ ℂ F]

/-- The complex-bilinear extension
`(φ, ψ) ↦ B (Re φ) (Re ψ) - B (Im φ) (Im ψ) + i (B (Re φ) (Im ψ) + B (Im φ) (Re ψ))` of a
real-bilinear map on real smooth functions supported in compact sets to complex ones. -/
def complexifySupportedIn (B : 𝓓^{n₁}_{K₁}(E, ℝ) →ₗ[ℝ] 𝓓^{n₂}_{K₂}(D, ℝ) →ₗ[ℝ] F) :
    𝓓^{n₁}_{K₁}(E, ℂ) →ₗ[ℂ] 𝓓^{n₂}_{K₂}(D, ℂ) →ₗ[ℂ] F :=
  LinearMap.mk₂ ℂ (fun φ ψ ↦
      B (postcompCLM (𝕜 := ℝ) reCLM φ) (postcompCLM (𝕜 := ℝ) reCLM ψ) -
        B (postcompCLM (𝕜 := ℝ) imCLM φ) (postcompCLM (𝕜 := ℝ) imCLM ψ) +
      I • (B (postcompCLM (𝕜 := ℝ) reCLM φ) (postcompCLM (𝕜 := ℝ) imCLM ψ) +
        B (postcompCLM (𝕜 := ℝ) imCLM φ) (postcompCLM (𝕜 := ℝ) reCLM ψ)))
    (fun φ φ' ψ ↦ by simp only [map_add, LinearMap.add_apply]; module)
    (fun c φ ψ ↦ by
      simp only [postcompCLM_reCLM_smul, postcompCLM_imCLM_smul, map_sub, map_add, map_smul,
        LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
        RCLike.real_smul_eq_coe_smul (K := ℂ)]
      conv_rhs => rw [← re_add_im c]
      match_scalars <;> apply Complex.ext <;> simp)
    (fun φ ψ ψ' ↦ by simp only [map_add]; module)
    (fun c φ ψ ↦ by
      simp only [postcompCLM_reCLM_smul, postcompCLM_imCLM_smul, map_sub, map_add, map_smul,
        RCLike.real_smul_eq_coe_smul (K := ℂ)]
      conv_rhs => rw [← re_add_im c]
      match_scalars <;> apply Complex.ext <;> simp)

theorem complexifySupportedIn_apply (B : 𝓓^{n₁}_{K₁}(E, ℝ) →ₗ[ℝ] 𝓓^{n₂}_{K₂}(D, ℝ) →ₗ[ℝ] F)
    (φ : 𝓓^{n₁}_{K₁}(E, ℂ)) (ψ : 𝓓^{n₂}_{K₂}(D, ℂ)) :
    complexifySupportedIn B φ ψ =
      B (postcompCLM (𝕜 := ℝ) reCLM φ) (postcompCLM (𝕜 := ℝ) reCLM ψ) -
        B (postcompCLM (𝕜 := ℝ) imCLM φ) (postcompCLM (𝕜 := ℝ) imCLM ψ) +
      I • (B (postcompCLM (𝕜 := ℝ) reCLM φ) (postcompCLM (𝕜 := ℝ) imCLM ψ) +
        B (postcompCLM (𝕜 := ℝ) imCLM φ) (postcompCLM (𝕜 := ℝ) reCLM ψ)) := by
  simp only [complexifySupportedIn, mk₂_apply]

/-- On real functions, the complex-bilinear extension of `B` is `B`. -/
@[simp]
theorem complexifySupportedIn_postcompCLM_ofRealCLM
    (B : 𝓓^{n₁}_{K₁}(E, ℝ) →ₗ[ℝ] 𝓓^{n₂}_{K₂}(D, ℝ) →ₗ[ℝ] F)
    (φ : 𝓓^{n₁}_{K₁}(E, ℝ)) (ψ : 𝓓^{n₂}_{K₂}(D, ℝ)) :
    complexifySupportedIn B (postcompCLM (𝕜 := ℝ) ofRealCLM φ)
      (postcompCLM (𝕜 := ℝ) ofRealCLM ψ) = B φ ψ := by
  simp [complexifySupportedIn_apply]

/-- The complex-bilinear extension of `B` is the only complex-bilinear map which agrees with `B`
on real functions. -/
theorem eq_complexifySupportedIn {B : 𝓓^{n₁}_{K₁}(E, ℝ) →ₗ[ℝ] 𝓓^{n₂}_{K₂}(D, ℝ) →ₗ[ℝ] F}
    {C : 𝓓^{n₁}_{K₁}(E, ℂ) →ₗ[ℂ] 𝓓^{n₂}_{K₂}(D, ℂ) →ₗ[ℂ] F}
    (hC : ∀ φ ψ, C (postcompCLM (𝕜 := ℝ) ofRealCLM φ) (postcompCLM (𝕜 := ℝ) ofRealCLM ψ) =
      B φ ψ) :
    C = complexifySupportedIn B := by
  ext φ ψ
  rw [complexifySupportedIn_apply, ← postcompCLM_re_add_I_smul_im φ,
    ← postcompCLM_re_add_I_smul_im ψ]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hC,
    postcompCLM_reCLM_ofRealCLM, postcompCLM_imCLM_ofRealCLM, postcompCLM_reCLM_smul,
    postcompCLM_imCLM_smul, I_re, I_im, one_smul, zero_smul, sub_zero, add_zero, zero_add,
    smul_add, smul_smul, I_mul_I, neg_smul]
  module

/-- The complex-bilinear extension is additive in `B`. -/
@[simp]
theorem complexifySupportedIn_add (B B' : 𝓓^{n₁}_{K₁}(E, ℝ) →ₗ[ℝ] 𝓓^{n₂}_{K₂}(D, ℝ) →ₗ[ℝ] F) :
    complexifySupportedIn (B + B') = complexifySupportedIn B + complexifySupportedIn B' := by
  ext φ ψ
  simp only [complexifySupportedIn_apply, LinearMap.add_apply]
  module

/-- The complex-bilinear extension commutes with real scalar multiplication of `B`. -/
@[simp]
theorem complexifySupportedIn_smul (c : ℝ)
    (B : 𝓓^{n₁}_{K₁}(E, ℝ) →ₗ[ℝ] 𝓓^{n₂}_{K₂}(D, ℝ) →ₗ[ℝ] F) :
    complexifySupportedIn (c • B) = (c : ℂ) • complexifySupportedIn B := by
  ext φ ψ
  simp only [complexifySupportedIn_apply, LinearMap.smul_apply,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  module

end Module

/-- Postcomposition with a real-linear map `ℂ →L[ℝ] ℝ` of norm at most one, such as the real and
imaginary parts, does not increase the `C^k` seminorms. -/
private theorem supSeminorm_postcompCLM_le_of_norm_le_one {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {K : Compacts G} {m : ℕ∞} {T : ℂ →L[ℝ] ℝ} (hT : ‖T‖ ≤ 1) (k : ℕ)
    (χ : 𝓓^{m}_{K}(G, ℂ)) :
    ContDiffMapSupportedIn.supSeminorm ℝ G ℝ m K k (postcompCLM T χ) ≤
      ContDiffMapSupportedIn.supSeminorm ℂ G ℂ m K k χ :=
  (supSeminorm_postcompCLM_le T k χ).trans <| by
    rw [supSeminorm_eq_of_scalars ℝ ℂ]
    exact mul_le_of_le_one_left (apply_nonneg _ _) hT

/-- A bound of `B` by a product of `C^k` seminorms gives one of its complex-bilinear extension. -/
theorem norm_complexifySupportedIn_le {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {B : 𝓓^{n₁}_{K₁}(E, ℝ) →ₗ[ℝ] 𝓓^{n₂}_{K₂}(D, ℝ) →ₗ[ℝ] F} {C : ℝ} {k₁ k₂ : ℕ} (hC : 0 ≤ C)
    (hB : ∀ φ ψ, ‖B φ ψ‖ ≤ C * ContDiffMapSupportedIn.supSeminorm ℝ E ℝ n₁ K₁ k₁ φ *
      ContDiffMapSupportedIn.supSeminorm ℝ D ℝ n₂ K₂ k₂ ψ)
    (φ : 𝓓^{n₁}_{K₁}(E, ℂ)) (ψ : 𝓓^{n₂}_{K₂}(D, ℂ)) :
    ‖complexifySupportedIn B φ ψ‖ ≤
      4 * C * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ n₁ K₁ k₁ φ *
        ContDiffMapSupportedIn.supSeminorm ℂ D ℂ n₂ K₂ k₂ ψ := by
  have h {T₁ T₂ : ℂ →L[ℝ] ℝ} (h₁ : ‖T₁‖ ≤ 1) (h₂ : ‖T₂‖ ≤ 1) :
      ‖B (postcompCLM T₁ φ) (postcompCLM T₂ ψ)‖ ≤
        C * ContDiffMapSupportedIn.supSeminorm ℂ E ℂ n₁ K₁ k₁ φ *
          ContDiffMapSupportedIn.supSeminorm ℂ D ℂ n₂ K₂ k₂ ψ :=
    (hB _ _).trans (by gcongr <;> exact supSeminorm_postcompCLM_le_of_norm_le_one ‹_› _ _)
  have hre : ‖reCLM‖ ≤ 1 := reCLM_norm.le
  have him : ‖imCLM‖ ≤ 1 := imCLM_norm.le
  rw [complexifySupportedIn_apply]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_I, one_mul]
  linarith [norm_sub_le (B (postcompCLM (𝕜 := ℝ) reCLM φ) (postcompCLM (𝕜 := ℝ) reCLM ψ))
      (B (postcompCLM (𝕜 := ℝ) imCLM φ) (postcompCLM (𝕜 := ℝ) imCLM ψ)),
    norm_add_le (B (postcompCLM (𝕜 := ℝ) reCLM φ) (postcompCLM (𝕜 := ℝ) imCLM ψ))
      (B (postcompCLM (𝕜 := ℝ) imCLM φ) (postcompCLM (𝕜 := ℝ) reCLM ψ)),
    h hre hre, h him him, h hre him, h him hre]

end LinearMap
