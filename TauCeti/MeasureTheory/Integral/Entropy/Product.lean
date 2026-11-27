/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Entropy.Basic
import TauCeti.InformationTheory.KullbackLeibler.Convex
import TauCeti.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# Functional entropy and product measures

The product chain rule applies to signed functions when `g`, `g log g`, and the first marginal's
`x log x` transform are integrable. An integral log-sum inequality yields entropy
convexity under unnormalized mixtures and product subadditivity for a.e. nonnegative functions.
The mixture inequality integrates both sides against the mixing measure without dividing by its
mass. For finite factors, integrability of `g` and `g log g` on the product suffices. The s-finite
mixture and subadditivity results require both marginal transforms to be integrable; the chain
rule and averaging inequality require only the first.
Product subadditivity bounds joint entropy by the sum of integrated coordinate entropies;
factorwise logarithmic Sobolev bounds can therefore be applied to the sections for tensorization.
-/

public section

open MeasureTheory Set

namespace MeasureTheory.Measure

/-- The functional entropy chain rule when `g`, `g log g`, and the first marginal's `x log x`
transform are integrable. -/
theorem entropy_prod_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmarg : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ) :
    entropy (μ.prod ν) g =
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) +
        entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) := by
  simp only [entropy_def]
  rw [integral_prod g hg, integral_prod _ hlog,
    integral_sub hlog.integral_prod_left hmarg]
  ring

/-- Section entropies are integrable when the joint and first marginal `x log x`
transforms are integrable. -/
theorem integrable_entropy_prod_left {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmarg : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ) :
    Integrable (fun x ↦ entropy ν (fun y ↦ g (x, y))) μ := by
  convert hlog.integral_prod_left.sub hmarg using 1
  funext x
  simp only [entropy_def, Pi.sub_apply]

/-- Section entropies in the second coordinate are integrable under the corresponding
joint and marginal `x log x` hypotheses. -/
theorem integrable_entropy_prod_right {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmarg : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν) :
    Integrable (fun y ↦ entropy μ (fun x ↦ g (x, y))) ν := by
  convert hlog.integral_prod_right.sub hmarg using 1
  funext y
  simp only [entropy_def, Pi.sub_apply]

private theorem norm_mul_log_le_of_abs_le {s t : ℝ} (hst : |s| ≤ t) :
    ‖s * Real.log s‖ ≤ ‖t * Real.log t‖ + 1 := by
  have ht : 0 ≤ t := (abs_nonneg s).trans hst
  have hnorm : ‖s * Real.log s‖ = ‖|s| * Real.log |s|‖ := by simp [Real.log_abs]
  rw [hnorm]
  by_cases hs : |s| ≤ 1
  · have hnonpos := Real.mul_log_nonpos (abs_nonneg s) hs
    calc
      _ = -(|s| * Real.log |s|) := by
        rw [Real.norm_eq_abs, abs_of_nonpos hnonpos]
      _ = Real.negMulLog |s| := by simp [Real.negMulLog_eq_neg]
      _ ≤ 1 - |s| := Real.negMulLog_le_one_sub_self (abs_nonneg s)
      _ ≤ 1 := by linarith [abs_nonneg s]
      _ ≤ ‖t * Real.log t‖ + 1 := by linarith [norm_nonneg (t * Real.log t)]
  · have hsone : 1 < |s| := lt_of_not_ge hs
    have htone : 1 < t := lt_of_lt_of_le hsone hst
    have hexp : Real.exp (-1) ≤ 1 := (Real.exp_lt_one_iff.mpr (by norm_num)).le
    have hmul := Real.mul_log_strictMonoOn.monotoneOn
      (show |s| ∈ Set.Ici (Real.exp (-1)) from hexp.trans hsone.le)
      (show t ∈ Set.Ici (Real.exp (-1)) from hexp.trans htone.le) hst
    have hleft : 0 ≤ |s| * Real.log |s| :=
      mul_nonneg (abs_nonneg _) (Real.log_nonneg hsone.le)
    have hright : 0 ≤ t * Real.log t :=
      mul_nonneg ht (Real.log_nonneg htone.le)
    calc
      ‖|s| * Real.log |s|‖ = |s| * Real.log |s| := by
        rw [Real.norm_eq_abs, abs_of_nonneg hleft]
      _ ≤ t * Real.log t := hmul
      _ ≤ ‖t * Real.log t‖ + 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hright]
        linarith

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
    have h := congrArg (fun t : ℝ ↦ -c * t)
      (Real.negMulLog_mul c⁻¹ (∫ y, g (x, y) ∂ν))
    simp only [Real.negMulLog_eq_neg, Real.log_inv] at h
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
    exact norm_mul_log_le_of_abs_le hm_bound
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

/-- Averaging out a probability-measure coordinate cannot increase functional entropy for an
a.e. nonnegative function, when the function, its `x log x` transform, and the marginal `x log x`
are integrable. -/
theorem entropy_integral_prod_left_le_entropy_prod_of_integrable_marginal_mul_log
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [IsProbabilityMeasure ν]
    (g : α × β → ℝ) (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmarg : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤ entropy (μ.prod ν) g := by
  have hsection : ∀ᵐ x ∂μ, 0 ≤ entropy ν (fun y ↦ g (x, y)) := by
    filter_upwards [ae_ae_of_ae_prod hnonneg, hg.prod_right_ae, hlog.prod_right_ae]
      with x hx hxi hli
    exact entropy_nonneg ν hx hxi hli
  rw [entropy_prod_eq μ ν g hg hlog hmarg]
  have := integral_nonneg_of_ae hsection
  linarith

/-- Averaging an a.e. nonnegative function over a probability coordinate cannot increase entropy
when the outer measure is finite and the function and its `x log x` transform are integrable. -/
theorem entropy_integral_prod_left_le_entropy_prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (g : α × β → ℝ) (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤ entropy (μ.prod ν) g :=
  entropy_integral_prod_left_le_entropy_prod_of_integrable_marginal_mul_log μ ν g hnonneg hg hlog
    (integrable_marginal_mul_log_left μ ν hg hlog)

/-- Integrating section entropies is the difference of the joint and marginal `x log x`
integrals. -/
private theorem integral_entropy_prod_right {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmargy : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν) :
    (∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν) =
      (∫ p, g p * Real.log (g p) ∂(μ.prod ν)) -
        ∫ y, (∫ x, g (x, y) ∂μ) * Real.log (∫ x, g (x, y) ∂μ) ∂ν := by
  simp only [entropy_def]
  rw [integral_sub hlog.integral_prod_right hmargy, ← integral_prod_symm _ hlog]

/-- For an a.e. nonnegative function, entropy is convex under mixtures if
the function, its `x log x` transform, both marginal `x log x` terms, and the marginal cross-log
are integrable. The support condition says that a zero marginal forces the function to vanish
a.e. in that section. -/
private theorem entropy_integral_le_integral_entropy_aux {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmargx : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ)
    (hmargy : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν)
    (hcross : Integrable (fun p ↦ g p * Real.log (∫ x, g (x, p.2) ∂μ))
      (μ.prod ν))
    (hzero : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, (∫ x, g (x, y) ∂μ) = 0 → g (x, y) = 0) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤
      ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  let a : α → ℝ := fun x ↦ ∫ y, g (x, y) ∂ν
  let b : β → ℝ := fun y ↦ ∫ x, g (x, y) ∂μ
  let m : ℝ := ∫ p, g p ∂(μ.prod ν)
  have hai : Integrable a μ := hg.integral_prod_left
  have hbi : Integrable b ν := hg.integral_prod_right
  have ham : ∫ x, a x ∂μ = m := (integral_prod g hg).symm
  have hbm : ∫ y, b y ∂ν = m := (integral_prod_symm g hg).symm
  have hb : 0 ≤ᵐ[ν] b := μ.ae_nonneg_integral_prod_right ν hnonneg
  have hpoint : ∀ᵐ x ∂μ, a x * Real.log (a x) - a x * Real.log m ≤
      ∫ y, g (x, y) * Real.log (g (x, y)) - g (x, y) * Real.log (b y) ∂ν := by
    filter_upwards [ae_ae_of_ae_prod hnonneg, hg.prod_right_ae,
      hlog.prod_right_ae, hcross.prod_right_ae, hzero] with x hx hxi hli hci hz
    have h := integral_log_sum_split_le ν hx hb hz hxi hbi (hli.sub hci)
    rw [hbm] at h
    simpa only [a, b] using h
  have hleft := hmargx.sub (hai.mul_const (Real.log m))
  have hright := (hlog.sub hcross).integral_prod_left
  have hint := integral_mono_ae hleft hright hpoint
  have hcross_eq : (∫ p, g p * Real.log (b p.2) ∂(μ.prod ν)) =
      ∫ y, b y * Real.log (b y) ∂ν := by
    rw [integral_prod_symm _ hcross]
    apply integral_congr_ae
    filter_upwards with y
    exact integral_mul_const (μ := μ) (Real.log (b y)) (fun x : α ↦ g (x, y))
  have hfubini : (∫ x, ∫ y, g (x, y) * Real.log (g (x, y)) -
      g (x, y) * Real.log (b y) ∂ν ∂μ) =
      ∫ p, g p * Real.log (g p) - g p * Real.log (b p.2) ∂(μ.prod ν) := by
    simpa only [Pi.sub_apply] using (integral_prod _ (hlog.sub hcross)).symm
  have hint' : (∫ x, a x * Real.log (a x) - a x * Real.log m ∂μ) ≤
      ∫ x, ∫ y, g (x, y) * Real.log (g (x, y)) -
        g (x, y) * Real.log (b y) ∂ν ∂μ := by
    simpa only [Pi.sub_apply] using hint
  have hleft_eq : (∫ x, a x * Real.log (a x) - a x * Real.log m ∂μ) =
      (∫ x, a x * Real.log (a x) ∂μ) - m * Real.log m := by
    rw [integral_sub hmargx (hai.mul_const _), integral_mul_const, ham]
  have hright_eq : (∫ x, ∫ y, g (x, y) * Real.log (g (x, y)) -
      g (x, y) * Real.log (b y) ∂ν ∂μ) =
      (∫ p, g p * Real.log (g p) ∂(μ.prod ν)) -
        ∫ y, b y * Real.log (b y) ∂ν := by
    rw [hfubini, integral_sub hlog hcross, hcross_eq]
  rw [hleft_eq, hright_eq] at hint'
  rw [entropy_def, ham]
  rw [integral_entropy_prod_right μ ν g hlog hmargy]
  exact hint'

/-- Entropy is convex under unnormalized mixtures for an a.e. nonnegative function and s-finite
measures, including when its total mass is zero. Both sides integrate against `ν` without
dividing by its mass. The function and its `x log x` transform must be integrable on the product,
and both marginal `x log x` transforms must be integrable. -/
theorem entropy_integral_le_integral_entropy_of_integrable_marginals_mul_log {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (g : α × β → ℝ)
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmargx : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ)
    (hmargy : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤
      ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  have hweight : AEMeasurable (fun y ↦ Real.log (∫ x, g (x, y) ∂μ)) ν :=
    Real.measurable_log.comp_aemeasurable
      hg.integral_prod_right.aestronglyMeasurable.aemeasurable
  exact entropy_integral_le_integral_entropy_aux μ ν g hnonneg hg hlog hmargx
    hmargy (μ.integrable_mul_comp_snd_of_integrable_marginal_mul ν hnonneg
      hg.aestronglyMeasurable hg.prod_left_ae hweight hmargy)
    (ae_ae_of_ae_prod (μ.ae_eq_zero_of_marginal_right_eq_zero ν hnonneg
      hg.aestronglyMeasurable hg.prod_left_ae))

/-- Product entropy subadditivity for an a.e. nonnegative function when the function and its
`x log x` transform are integrable on the product, and both marginal transforms are integrable. -/
theorem entropy_prod_le_of_integrable_marginals_mul_log {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (g : α × β → ℝ) (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν))
    (hmargx : Integrable (fun x ↦ (∫ y, g (x, y) ∂ν) *
      Real.log (∫ y, g (x, y) ∂ν)) μ)
    (hmargy : Integrable (fun y ↦ (∫ x, g (x, y) ∂μ) *
      Real.log (∫ x, g (x, y) ∂μ)) ν) :
    entropy (μ.prod ν) g ≤
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) +
        ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  rw [entropy_prod_eq μ ν g hg hlog hmargx]
  have h := entropy_integral_le_integral_entropy_of_integrable_marginals_mul_log
    μ ν g hnonneg hg hlog hmargx hmargy
  linarith

/-- Entropy is convex when integrating sections of an a.e. nonnegative function against `ν`,
with the reference measure `μ` fixed. Both sides integrate against `ν` without dividing by its
mass. Both measures are finite and the function and its `x log x` transform are integrable. -/
theorem entropy_integral_le_integral_entropy {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (g : α × β → ℝ)
    (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy μ (fun x ↦ ∫ y, g (x, y) ∂ν) ≤
      ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν := by
  exact entropy_integral_le_integral_entropy_of_integrable_marginals_mul_log μ ν g hnonneg hg hlog
    (integrable_marginal_mul_log_left μ ν hg hlog)
    (integrable_marginal_mul_log_right μ ν hg hlog)

/-- Product entropy subadditivity for an a.e. nonnegative function under finite measures,
assuming integrability of the function and its `x log x` transform. -/
theorem entropy_prod_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (g : α × β → ℝ) (hnonneg : 0 ≤ᵐ[μ.prod ν] g)
    (hg : Integrable g (μ.prod ν))
    (hlog : Integrable (fun p ↦ g p * Real.log (g p)) (μ.prod ν)) :
    entropy (μ.prod ν) g ≤
      (∫ x, entropy ν (fun y ↦ g (x, y)) ∂μ) +
        ∫ y, entropy μ (fun x ↦ g (x, y)) ∂ν :=
  entropy_prod_le_of_integrable_marginals_mul_log μ ν g hnonneg hg hlog
    (integrable_marginal_mul_log_left μ ν hg hlog)
    (integrable_marginal_mul_log_right μ ν hg hlog)

end MeasureTheory.Measure
