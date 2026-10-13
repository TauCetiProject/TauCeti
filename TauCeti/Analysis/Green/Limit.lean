/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.AbsolutelyContinuous
public import TauCeti.Analysis.Green.WindingWeight.Basic
public import TauCeti.MeasureTheory.Integral.CurveIntegral.Convergence
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Passage to the limit in the two Green integrals

Uniform convergence of absolutely continuous curves and `L¹` convergence of derivatives
preserve circulation of compactly supported continuous fields. `L¹` convergence of the winding
weights preserves the curl area integral for globally `C¹`, compactly supported fields.
Both integrals are integrable; index vanishing identifies the whole-plane area integral
with its restriction to the field domain.
-/

public section

noncomputable section

open MeasureTheory Set Filter Function
open scoped Topology

namespace TauCeti.Green

private theorem oneForm_eq_clm (P Q : ℂ → ℝ) :
    oneForm P Q = fun z ↦ P z • Complex.reCLM + Q z • Complex.imCLM := by
  ext z v
  simp [oneForm_apply]

/-- A continuous planar field gives a continuous field of real linear 1-forms. -/
theorem continuous_oneForm {P Q : ℂ → ℝ} (hP : Continuous P) (hQ : Continuous Q) :
    Continuous (oneForm P Q) := by
  rw [oneForm_eq_clm]
  exact (hP.smul continuous_const).add (hQ.smul continuous_const)

private theorem exists_bound_oneForm {P Q : ℂ → ℝ}
    (hP : Continuous P) (hQ : Continuous Q)
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q) :
    ∃ C, ∀ z, ‖oneForm P Q z‖ ≤ C := by
  obtain ⟨CP, hCP⟩ := hcP.exists_bound_of_continuous hP
  obtain ⟨CQ, hCQ⟩ := hcQ.exists_bound_of_continuous hQ
  refine ⟨CP * ‖Complex.reCLM‖ + CQ * ‖Complex.imCLM‖, fun z ↦ ?_⟩
  rw [oneForm_eq_clm]
  exact (norm_add_le _ _).trans (by
    simp only [norm_smul]
    gcongr
    · exact hCP z
    · exact hCQ z)

/-- Uniform convergence of AC curves and derivative `L¹` convergence preserve the actual
circulation integral of compactly supported continuous planar fields. -/
theorem tendsto_integral_circulationFun {γn : ℕ → ℝ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγn : ∀ n, AbsolutelyContinuousOnInterval (γn n) a b) (hab : a ≤ b)
    {P Q : ℂ → ℝ} (hP : Continuous P) (hQ : Continuous Q)
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q)
    (hconv : TendstoUniformlyOn γn γ atTop (Icc a b))
    (hdconv : Tendsto (fun n ↦ ∫ t in a..b, ‖deriv (γn n) t - deriv γ t‖)
      atTop (nhds 0)) :
    Tendsto (fun n ↦ ∫ t in a..b, circulationFun P Q (γn n) t) atTop
      (nhds (∫ t in a..b, circulationFun P Q γ t)) := by
  obtain ⟨C, hC⟩ := exists_bound_oneForm hP hQ hcP hcQ
  simpa only [← circulationFun_eq_oneForm] using
    hγ.tendsto_integral_oneForm_of_tendstoUniformlyOn hγn hab
      (continuous_oneForm hP hQ) hC hconv hdconv

/-- Globally real `C¹` fields have continuous curl. -/
theorem continuous_curl {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    Continuous (curl P Q) := by
  have heq : curl P Q = fun z ↦ fderiv ℝ Q z 1 - fderiv ℝ P z Complex.I :=
    funext fun z ↦ curl_def P Q z
  rw [heq]
  exact ((ContinuousLinearMap.apply ℝ ℝ 1).continuous.comp
    (hQ.continuous_fderiv (by simp))).sub
      ((ContinuousLinearMap.apply ℝ ℝ Complex.I).continuous.comp
        (hP.continuous_fderiv (by simp)))

/-- Compact support of the field implies compact support of its curl. -/
theorem hasCompactSupport_curl {P Q : ℂ → ℝ}
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q) : HasCompactSupport (curl P Q) := by
  have hQ := (hcQ.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ ↦ L 1) (by simp)
  have hP := (hcP.fderiv ℝ).comp_left (g := fun L : ℂ →L[ℝ] ℝ ↦ L Complex.I) (by simp)
  convert hQ.sub hP using 1
  ext z
  exact curl_def P Q z

/-- The winding-weighted curl of globally `C¹`, compactly supported fields is integrable
for every closed AC curve. -/
theorem integrable_windingWeight_mul_curl {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q) :
    Integrable (fun z ↦ windingWeight γ a b z * curl P Q z) := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_curl hcP hcQ).exists_bound_of_continuous
    (continuous_curl hP hQ)
  exact (integrable_windingWeight hγ hclosed).mul_bdd
    (continuous_curl hP hQ).aestronglyMeasurable (Eventually.of_forall hC)

/-- Actual winding-weighted curl integrals converge under `L¹` convergence of the weights.
There is no uniform bound on the winding numbers. -/
theorem tendsto_integral_windingWeight_mul_curl
    {γn : ℕ → ℝ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγn : ∀ n, AbsolutelyContinuousOnInterval (γn n) a b)
    (hclosed : γ a = γ b) (hclosedn : ∀ n, γn n a = γn n b)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q)
    (hwconv : Tendsto
      (fun n ↦ ∫ z : ℂ, |windingWeight (γn n) a b z - windingWeight γ a b z|)
      atTop (nhds 0)) :
    Tendsto (fun n ↦ ∫ z : ℂ, windingWeight (γn n) a b z * curl P Q z) atTop
      (nhds (∫ z : ℂ, windingWeight γ a b z * curl P Q z)) := by
  obtain ⟨C, hC⟩ := (hasCompactSupport_curl hcP hcQ).exists_bound_of_continuous
    (continuous_curl hP hQ)
  exact tendsto_integral_mul_of_integral_abs_sub
    (fun n ↦ integrable_windingWeight (hγn n) (hclosedn n))
    (integrable_windingWeight hγ hclosed) (continuous_curl hP hQ).aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using Eventually.of_forall hC) hwconv

/-- Index vanishing outside a domain identifies the whole-plane weighted area integral
with its restriction to that domain. This equality needs no field regularity. -/
theorem integral_windingWeight_mul_eq_setIntegral {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ}
    (hindex : ∀ z ∉ U, Contour.windingNumber γ a b z = 0) (R : ℂ → ℝ) :
    (∫ z : ℂ, windingWeight γ a b z * R z) =
      ∫ z in U, windingWeight γ a b z * R z := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  by_cases ht : z ∈ γ '' uIcc a b
  · rw [windingWeight_eq_zero_of_mem ht, zero_mul]
  · rw [windingWeight_eq_of_notMem ht, hindex z hz, Complex.zero_re, zero_mul]

/-- The weighted curl integrals over an index-vanishing domain converge when the winding
weights converge in `L¹`. The approximating indices need vanish outside the domain only
eventually. -/
theorem tendsto_setIntegral_windingWeight_mul_curl
    {γn : ℕ → ℝ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγn : ∀ n, AbsolutelyContinuousOnInterval (γn n) a b)
    (hclosed : γ a = γ b) (hclosedn : ∀ n, γn n a = γn n b)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q)
    (hwconv : Tendsto
      (fun n ↦ ∫ z : ℂ, |windingWeight (γn n) a b z - windingWeight γ a b z|)
      atTop (nhds 0))
    (hindex : ∀ z ∉ U, Contour.windingNumber γ a b z = 0)
    (hindexn : ∀ᶠ n in atTop, ∀ z ∉ U, Contour.windingNumber (γn n) a b z = 0) :
    Tendsto (fun n ↦ ∫ z in U, windingWeight (γn n) a b z * curl P Q z) atTop
      (nhds (∫ z in U, windingWeight γ a b z * curl P Q z)) := by
  rw [← integral_windingWeight_mul_eq_setIntegral hindex]
  apply (tendsto_integral_windingWeight_mul_curl hγ hγn hclosed hclosedn
    hP hQ hcP hcQ hwconv).congr'
  filter_upwards [hindexn] with n hn
  exact integral_windingWeight_mul_eq_setIntegral hn (curl P Q)

/-- Passage to the limit in both actual Green integrals. Any approximating Green identities
valid eventually pass to the closed AC limit, using uniform, derivative `L¹`, and weight `L¹`
convergence. In particular this applies to the endpoint-preserving polygonal approximations. -/
theorem integral_circulationFun_eq_setIntegral_of_approximation
    {γn : ℕ → ℝ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {U : Set ℂ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγn : ∀ n, AbsolutelyContinuousOnInterval (γn n) a b) (hab : a ≤ b)
    (hclosed : γ a = γ b) (hclosedn : ∀ n, γn n a = γn n b)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q)
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q)
    (hconv : TendstoUniformlyOn γn γ atTop (Icc a b))
    (hdconv : Tendsto (fun n ↦ ∫ t in a..b, ‖deriv (γn n) t - deriv γ t‖)
      atTop (nhds 0))
    (hwconv : Tendsto
      (fun n ↦ ∫ z : ℂ, |windingWeight (γn n) a b z - windingWeight γ a b z|)
      atTop (nhds 0))
    (hindex : ∀ z ∉ U, Contour.windingNumber γ a b z = 0)
    (hindexn : ∀ᶠ n in atTop, ∀ z ∉ U, Contour.windingNumber (γn n) a b z = 0)
    (hgreen : ∀ᶠ n in atTop, (∫ t in a..b, circulationFun P Q (γn n) t) =
      ∫ z in U, windingWeight (γn n) a b z * curl P Q z) :
    (∫ t in a..b, circulationFun P Q γ t) =
      ∫ z in U, windingWeight γ a b z * curl P Q z := by
  exact tendsto_nhds_unique
    ((tendsto_integral_circulationFun hγ hγn hab hP.continuous hQ.continuous
      hcP hcQ hconv hdconv).congr' hgreen)
    (tendsto_setIntegral_windingWeight_mul_curl hγ hγn hclosed hclosedn hP hQ
      hcP hcQ hwconv hindex hindexn)

end TauCeti.Green
