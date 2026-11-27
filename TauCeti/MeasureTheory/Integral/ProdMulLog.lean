/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import Mathlib.Analysis.Convex.Integral

/-!
# Integrability of marginal `x log x` transforms

For finite measures, integrability of a function and its `x log x` transform on the product
implies integrability of both marginal transforms. The function may be signed.
-/

public section

open MeasureTheory Set

namespace MeasureTheory.Measure

/-- For an a.e. nonnegative function, integrability of `g` and `g log g` passes to the marginal
and its `x log x` transform when both measures are finite. -/
private theorem integrable_marginal_mul_log_left_of_nonneg
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α × β → ℝ} (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ := by
  by_cases hν : ν = 0
  · simp [hν]
  have : NeZero ν := ⟨hν⟩
  let c : ℝ := ν.real univ
  have hc : 0 < c := measureReal_univ_pos
  have hmeas : AEStronglyMeasurable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ :=
    (Real.continuous_mul_log.measurable.comp_aemeasurable
      hg.integral_prod_left.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  apply ((hlog.integral_prod_left.norm.add (integrable_const 1)).add
    (hg.integral_prod_left.norm.mul_const |Real.log c|)).mono' hmeas
  filter_upwards [ae_ae_of_ae_prod hnonneg, hg.prod_right_ae, hlog.prod_right_ae]
    with x hx hxi hli
  have ha := integral_nonneg_of_ae hx
  have hlower := Real.self_sub_one_le_mul_log ha
  have hupper := Real.convexOn_mul_log.map_average_le
    Real.continuous_mul_log.continuousOn isClosed_Ici hx hxi hli
  have hc_eq : ν.real univ = c := rfl
  simp only [average_eq, smul_eq_mul, hc_eq] at hupper
  have hlog_eq :
      c * ((c⁻¹ * ∫ y, g (x, y) ∂ν) * Real.log (c⁻¹ * ∫ y, g (x, y) ∂ν)) =
        (∫ y, g (x, y) ∂ν) * Real.log (∫ y, g (x, y) ∂ν) -
          (∫ y, g (x, y) ∂ν) * Real.log c := by
    have h := congrArg (fun t : ℝ ↦ c * t)
      (Real.mul_log_mul c⁻¹ (∫ y, g (x, y) ∂ν))
    simp only [Real.log_inv] at h
    field_simp at h ⊢
    linarith
  have hupper' := mul_le_mul_of_nonneg_left hupper hc.le
  rw [hlog_eq, mul_inv_cancel_left₀ hc.ne'] at hupper'
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg ha]
  apply abs_le.mpr
  constructor
  · linarith [abs_nonneg (∫ y, g (x, y) * Real.log (g (x, y)) ∂ν),
      mul_nonneg ha (abs_nonneg (Real.log c))]
  · nlinarith [le_abs_self (∫ y, g (x, y) * Real.log (g (x, y)) ∂ν),
      le_abs_self (Real.log c)]

/-- Integrability of a function and its `x log x` transform passes to the marginal's `x log x`
transform for finite measures, including signed functions. -/
theorem integrable_marginal_mul_log_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α × β → ℝ} (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ := by
  let gabs : α × β → ℝ := fun p ↦ |g p|
  let m : α → ℝ := fun x ↦ ∫ y, g (x, y) ∂ν
  let M : α → ℝ := fun x ↦ ∫ y, gabs (x, y) ∂ν
  have hgabs : Integrable gabs (μ.prod ν) := by
    simpa [gabs] using hg.norm
  have hgabs_meas : AEStronglyMeasurable gabs (μ.prod ν) := by
    simpa [gabs, Real.norm_eq_abs] using hg.norm.aestronglyMeasurable
  have hlogabs_meas : AEStronglyMeasurable
      (fun p ↦ gabs p * Real.log (gabs p)) (μ.prod ν) :=
    (Real.continuous_mul_log.measurable.comp_aemeasurable
      hgabs_meas.aemeasurable).aestronglyMeasurable
  have hlogabs : Integrable (fun p ↦ gabs p * Real.log (gabs p)) (μ.prod ν) := by
    refine hlog.norm.mono' hlogabs_meas ?_
    filter_upwards with p
    simp [gabs, Real.norm_eq_abs, Real.log_abs]
  have hnonneg : 0 ≤ᵐ[μ.prod ν] gabs := by
    filter_upwards with p
    exact abs_nonneg (g p)
  have hMlog : Integrable (fun x ↦ M x * Real.log (M x)) μ :=
    integrable_marginal_mul_log_left_of_nonneg μ ν hnonneg hgabs hlogabs
  have hm : Integrable m μ := hg.integral_prod_left
  have hmeas : AEStronglyMeasurable (fun x ↦ m x * Real.log (m x)) μ :=
    (Real.continuous_mul_log.measurable.comp_aemeasurable
      hm.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ,
      ‖m x * Real.log (m x)‖ ≤ ‖M x * Real.log (M x)‖ + 1 := by
    filter_upwards with x
    have hm_bound : |m x| ≤ M x := by
      simpa [m, M, gabs, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun y ↦ g (x, y))
    exact Real.norm_mul_log_le_of_abs_le hm_bound
  have hmarg : Integrable (fun x ↦ m x * Real.log (m x)) μ :=
    (hMlog.norm.add (integrable_const (1 : ℝ))).mono' hmeas hbound
  simpa [m] using hmarg

/-- Integrability of a function and its `x log x` transform passes to the second marginal's
`x log x` transform for finite measures, including signed functions. -/
theorem integrable_marginal_mul_log_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : α × β → ℝ} (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν := by
  simpa only [Function.comp_apply, Prod.swap_prod_mk] using
    integrable_marginal_mul_log_left ν μ hg.swap hlog.swap

end MeasureTheory.Measure
