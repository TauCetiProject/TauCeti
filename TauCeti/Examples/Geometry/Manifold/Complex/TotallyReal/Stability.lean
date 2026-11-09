/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Manifold.Complex.TotallyReal.Stability

/-!
# Regression examples: stability of totally real embeddings

For the inclusion of the real line into `ℂ`, operators near multiplication by `I` in the model
chart keep the real line maximal totally real, by the local chart form of stability. The radius
is finite: the identity operator does not keep the real line maximal totally real.
-/

open Complex Function
open scoped Manifold

namespace TauCeti

/-- Operators near multiplication by `I` in the model chart of `ℂ` keep the real line maximal
totally real, by the local chart form applied to the inclusion `ℝ → ℂ`. -/
example : ∃ ε > 0, ∀ A : ℂ →L[ℝ] ℂ, dist A (ContinuousLinearMap.lsmul ℝ ℂ I) < ε →
    IsMaximalTotallyReal A.toLinearMap (LinearMap.range ofRealCLM.toLinearMap) := by
  -- The doubled frame `(a, b) ↦ a + I b` is bijective, so the real line is maximal totally real.
  have hmax : IsMaximalTotallyReal (ContinuousLinearMap.lsmul ℝ ℂ I : ℂ →L[ℝ] ℂ).toLinearMap
      (LinearMap.range ofRealCLM.toLinearMap) := by
    refine isMaximalTotallyReal_range_of_bijective_coprod ⟨fun a b hab ↦ ?_, fun z ↦ ?_⟩
    · simp only [LinearMap.coprod_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ofRealCLM_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul] at hab
      have hre := congrArg re hab
      have him := congrArg im hab
      simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, add_im, mul_im] at hre him
      exact Prod.ext (by linarith) (by linarith)
    · refine ⟨(z.re, z.im), ?_⟩
      simp only [LinearMap.coprod_apply, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
        ofRealCLM_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      rw [mul_comm]
      exact re_add_im z
  have hinj : Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ofRealCLM 0) := by
    rw [ContinuousLinearMap.mfderiv_eq]
    exact ofReal_injective
  have hJ : Injective ((ContinuousLinearMap.lsmul ℝ ℂ I : ℂ →L[ℝ] ℂ).comp
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ofRealCLM 0)) :=
    (smul_right_injective ℂ I_ne_zero).comp hinj
  obtain ⟨ε, hε, hev⟩ := exists_pos_eventually_isMaximalTotallyReal_range_mfderiv
    (ι := ofRealCLM) (x₀ := 0) ofRealCLM.contMDiff.contMDiffAt hinj hJ
    (by rw [ContinuousLinearMap.mfderiv_eq]; exact hmax)
  refine ⟨ε, hε, fun A hA ↦ ?_⟩
  have h := hev.self_of_nhds A
  simp only [inCoordinates_tangent_bundle_core_model_space, ContinuousLinearMap.mfderiv_eq] at h
  exact h hA

/-- The radius is finite. The identity operator does not keep the real line maximal totally
real, since the real line is its own image. -/
example : ¬ IsMaximalTotallyReal (LinearMap.id : ℂ →ₗ[ℝ] ℂ)
    (LinearMap.range ofRealCLM.toLinearMap) := by
  intro h
  have hb := h.disjoint
  rw [Submodule.map_id, disjoint_self] at hb
  have h1 : (1 : ℂ) ∈ LinearMap.range ofRealCLM.toLinearMap := ⟨1, by simp⟩
  rw [hb, Submodule.mem_bot] at h1
  exact one_ne_zero h1

end TauCeti
