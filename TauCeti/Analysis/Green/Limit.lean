/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.AbsolutelyContinuous
public import TauCeti.Analysis.Green.WindingWeight.Basic
public import TauCeti.MeasureTheory.Integral.CurveIntegral.Convergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable

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

/-- Uniform convergence of AC curves and derivative `L¹` convergence preserve the actual
circulation integral of compactly supported continuous planar fields. -/
theorem _root_.AbsolutelyContinuousOnInterval.tendsto_integral_circulationFun
    {γn : ℕ → ℝ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
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
      (Continuous.oneForm hP hQ) hC hconv hdconv

/-- The winding-weighted curl of globally `C¹` fields is integrable for every closed AC curve. -/
theorem _root_.AbsolutelyContinuousOnInterval.integrable_windingWeight_mul_curl
    {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    Integrable (fun z ↦ windingWeight γ a b z * curl P Q z) := by
  have hc := hγ.hasCompactSupport_windingWeight hclosed
  apply (integrableOn_iff_integrable_of_support_subset
    ((support_mul_subset_left _ _).trans (subset_tsupport _))).mp
  exact (hγ.integrable_windingWeight hclosed).integrableOn.mul_continuousOn
    (ContDiff.continuous_curl hP hQ).continuousOn hc

/-- Actual winding-weighted curl integrals converge under `L¹` convergence of the weights.
There is no uniform bound on the winding numbers. -/
theorem _root_.AbsolutelyContinuousOnInterval.tendsto_integral_windingWeight_mul_curl
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
  obtain ⟨C, hC⟩ := (HasCompactSupport.curl hcP hcQ).exists_bound_of_continuous
    (ContDiff.continuous_curl hP hQ)
  exact tendsto_integral_mul_of_integral_abs_sub
    (fun n ↦ AbsolutelyContinuousOnInterval.integrable_windingWeight (hγn n) (hclosedn n))
    (hγ.integrable_windingWeight hclosed) (ContDiff.continuous_curl hP hQ).aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using Eventually.of_forall hC) hwconv

/-- The weighted curl integrals over an index-vanishing domain converge when the winding
weights converge in `L¹`. The approximating indices need vanish outside the domain only
eventually. -/
theorem _root_.AbsolutelyContinuousOnInterval.tendsto_setIntegral_windingWeight_mul_curl
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
  apply (hγ.tendsto_integral_windingWeight_mul_curl hγn hclosed hclosedn
    hP hQ hcP hcQ hwconv).congr'
  filter_upwards [hindexn] with n hn
  exact integral_windingWeight_mul_eq_setIntegral hn (curl P Q)

/-- Passage to the limit in both actual Green integrals. Any approximating Green identities
valid eventually pass to the closed AC limit, using uniform, derivative `L¹`, and weight `L¹`
convergence. In particular this applies to the endpoint-preserving polygonal approximations. -/
theorem _root_.AbsolutelyContinuousOnInterval.integral_circulationFun_eq_setIntegral
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
    ((hγ.tendsto_integral_circulationFun hγn hab hP.continuous hQ.continuous
      hcP hcQ hconv hdconv).congr' hgreen)
    (hγ.tendsto_setIntegral_windingWeight_mul_curl hγn hclosed hclosedn hP hQ
      hcP hcQ hwconv hindex hindexn)

end TauCeti.Green
