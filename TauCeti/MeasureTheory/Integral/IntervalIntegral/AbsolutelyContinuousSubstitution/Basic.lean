/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Substitution by absolutely continuous changes of parameter

Absolutely continuous substitutions satisfy change of variables for continuous integrands.
For monotone substitutions, the derivative-weighted pushforward of interval volume is interval
volume on the image, giving change of variables and transformed integrability for arbitrary
integrable normed-space-valued integrands. This accommodates constant pieces and unbounded
parameter speeds. The same pushforward sends almost every time at which the derivative does not
vanish off any null subset of the image interval
(`AbsolutelyContinuousOnInterval.ae_notMem_of_deriv_ne_zero_of_monotoneOn`).

Substituting the primitive `G u = ∫ v in c..u, g v` of an interval integrable `g` gives
`|∫ u in c..d, g u * exp |G u|| = exp |G d| - 1`
(`IntervalIntegrable.abs_integral_mul_exp_abs_integral`), the exponential bound for linear
equations with integrable coefficients.
-/

public section

open MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

/-- The derivative of a function monotone on a closed interval is nonnegative almost everywhere
on that interval; endpoint derivatives are immaterial. -/
private theorem ae_deriv_nonneg_of_monotoneOn {θ : ℝ → ℝ} {a b : ℝ}
    (hmono : MonotoneOn θ (Icc a b)) :
    ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ deriv θ t := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)]
  exact hmono.derivWithin_nonneg

/-- Substitution of an absolutely continuous function in the integral of a continuous real
integrand. The substitution need not be monotone. -/
theorem integral_comp_mul_deriv_of_continuous {θ : ℝ → ℝ} {a b : ℝ}
    (hθ : AbsolutelyContinuousOnInterval θ a b) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ t in a..b, f (θ t) * deriv θ t = ∫ u in θ a..θ b, f u := by
  let A : ℝ → ℝ := fun t ↦ ∫ u in θ a..t, f u
  have hAd : ∀ t, HasDerivAt A (f t) t := fun t ↦
    (hf.integral_hasStrictDerivAt (θ a) t).hasDerivAt
  have hderiv : deriv A = f := funext fun t ↦ (hAd t).deriv
  have hAsmooth : ContDiff ℝ 1 A := contDiff_one_iff_deriv.mpr
    ⟨fun t ↦ (hAd t).differentiableAt, by rw [hderiv]; exact hf⟩
  have h := hθ.integral_fderiv_apply_eq_sub
    (by filter_upwards [hθ.ae_differentiableAt] with t ht hmem
        exact (ht (uIoc_subset_uIcc hmem)).hasDerivAt) hAsmooth
  simpa [A, (hAd _).deriv, mul_comm] using h

/-- For an increasing absolutely continuous substitution, pushing interval volume weighted by
its derivative forward gives ordinary volume on the image interval. -/
theorem map_withDensity_deriv_of_monotoneOn {θ : ℝ → ℝ} {a b : ℝ}
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hmono : MonotoneOn θ (Icc a b)) :
    Measure.map θ ((volume.restrict (Icc a b)).withDensity
      (fun t ↦ ENNReal.ofReal (deriv θ t))) = volume.restrict (Icc (θ a) (θ b)) := by
  let μ := volume.restrict (Icc a b)
  let ν := μ.withDensity (fun t ↦ ENNReal.ofReal (deriv θ t))
  have hd : Integrable (deriv θ) μ := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hθ.intervalIntegrable_deriv
  have hnonneg : ∀ᵐ t ∂μ, 0 ≤ deriv θ t := ae_deriv_nonneg_of_monotoneOn hmono
  have hνfinite : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hd.aestronglyMeasurable hnonneg).mpr hd)
  let : IsFiniteMeasure ν := hνfinite
  have hθμ : AEMeasurable θ μ := by
    apply ContinuousOn.aemeasurable _ measurableSet_Icc
    simpa only [uIcc_of_le hab] using hθ.continuousOn
  have hθν : AEMeasurable θ ν :=
    hθμ.mono_ac (withDensity_absolutelyContinuous _ _)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hθν f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀ (measurable_deriv θ).ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  have heq : (fun t ↦ (ENNReal.ofReal (deriv θ t)).toReal • f (θ t)) =ᵐ[μ]
      (fun t ↦ f (θ t) * deriv θ t) := by
    filter_upwards [hnonneg] with t ht
    simp [ENNReal.toReal_ofReal ht, mul_comm]
  rw [integral_congr_ae heq]
  have hθab : θ a ≤ θ b := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  dsimp [μ]
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hθab]
  exact hθ.integral_comp_mul_deriv_of_continuous f.continuous

/-- A monotone absolutely continuous substitution `θ` maps almost every time of `[a, b]` at which
its derivative does not vanish outside any null subset of the image interval `[θ a, θ b]`. -/
theorem ae_notMem_of_deriv_ne_zero_of_monotoneOn {θ : ℝ → ℝ} {a b : ℝ}
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hmono : MonotoneOn θ (Icc a b)) {N : Set ℝ}
    (hN : volume.restrict (Icc (θ a) (θ b)) N = 0) :
    ∀ᵐ t, t ∈ Icc a b → deriv θ t ≠ 0 → θ t ∉ N := by
  rcases lt_or_ge b a with hba | hab
  · exact Filter.Eventually.of_forall fun t ht ↦ absurd (ht.1.trans ht.2) (not_le.2 hba)
  have hθμ : AEMeasurable θ (volume.restrict (Icc a b)) := by
    simpa only [uIcc_of_le hab] using hθ.continuousOn.aemeasurable measurableSet_uIcc
  have hθν := hθμ.mono_ac (withDensity_absolutelyContinuous _
    fun t ↦ ENNReal.ofReal (deriv θ t))
  have hN' := measure_eq_zero_iff_ae_notMem.1 hN
  rw [← hθ.map_withDensity_deriv_of_monotoneOn hab hmono] at hN'
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).1
      ((ae_withDensity_iff (measurable_deriv θ).ennreal_ofReal).1 (ae_of_ae_map hθν hN')),
    (ae_restrict_iff' measurableSet_Icc).1 (ae_deriv_nonneg_of_monotoneOn hmono)]
    with t ht hnn hmem hd
  exact ht hmem (ENNReal.ofReal_pos.2 ((hnn hmem).lt_of_ne' hd)).ne'

/-- Under a monotone absolutely continuous substitution, integrability of the derivative-weighted
composition is equivalent to integrability on the image interval. -/
theorem integrableOn_deriv_smul_comp_iff_of_monotoneOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    {θ : ℝ → ℝ} {a b : ℝ} (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hmono : MonotoneOn θ (Icc a b))
    (hf : AEStronglyMeasurable f (volume.restrict (Icc (θ a) (θ b)))) :
    IntegrableOn (fun t ↦ deriv θ t • f (θ t)) (Icc a b) volume ↔
      IntegrableOn f (Icc (θ a) (θ b)) volume := by
  have hmap := hθ.map_withDensity_deriv_of_monotoneOn hab hmono
  have hθμ : AEMeasurable θ (volume.restrict (Icc a b)) := by
    simpa only [uIcc_of_le hab] using hθ.continuousOn.aemeasurable measurableSet_uIcc
  have hθν := hθμ.mono_ac (withDensity_absolutelyContinuous _
    (fun t ↦ ENNReal.ofReal (deriv θ t)))
  simp only [IntegrableOn]
  rw [← hmap] at ⊢ hf
  rw [integrable_map_measure hf hθν,
    integrable_withDensity_iff_integrable_smul₀' (measurable_deriv θ).ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_deriv_nonneg_of_monotoneOn hmono] with t ht
  simp [ENNReal.toReal_ofReal ht]

/-- A monotone absolutely continuous substitution preserves integrability after multiplication
by its derivative. -/
theorem intervalIntegrable_deriv_smul_comp_of_monotoneOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    {θ : ℝ → ℝ} {a b : ℝ} (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hmono : MonotoneOn θ (Icc a b)) (hf : IntervalIntegrable f volume (θ a) (θ b)) :
    IntervalIntegrable (fun t ↦ deriv θ t • f (θ t)) volume a b := by
  have hθab := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have hfi := (intervalIntegrable_iff_integrableOn_Icc_of_le hθab).mp hf
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    ((hθ.integrableOn_deriv_smul_comp_iff_of_monotoneOn hab hmono hfi.aestronglyMeasurable).mpr hfi)

/-- Change of variables for a monotone absolutely continuous substitution and an integrable
vector-valued integrand. Constant pieces and unbounded parameter speeds are allowed. -/
theorem integral_deriv_smul_comp_of_monotoneOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    {θ : ℝ → ℝ} {a b : ℝ} (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hmono : MonotoneOn θ (Icc a b)) (hf : IntervalIntegrable f volume (θ a) (θ b)) :
    ∫ t in a..b, deriv θ t • f (θ t) = ∫ u in θ a..θ b, f u := by
  have hmap := hθ.map_withDensity_deriv_of_monotoneOn hab hmono
  have hθab := hmono (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  have hfi := (intervalIntegrable_iff_integrableOn_Icc_of_le hθab).mp hf
  have hθμ : AEMeasurable θ (volume.restrict (Icc a b)) := by
    simpa only [uIcc_of_le hab] using hθ.continuousOn.aemeasurable measurableSet_uIcc
  have hθν := hθμ.mono_ac (withDensity_absolutelyContinuous _
    (fun t ↦ ENNReal.ofReal (deriv θ t)))
  have hfm : AEStronglyMeasurable f
      (Measure.map θ ((volume.restrict (Icc a b)).withDensity
        (fun t ↦ ENNReal.ofReal (deriv θ t)))) := by
    rw [hmap]
    exact hfi.aestronglyMeasurable
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hθab,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc, ← hmap,
    integral_map hθν hfm,
    integral_withDensity_eq_integral_toReal_smul₀ (measurable_deriv θ).ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_deriv_nonneg_of_monotoneOn hmono] with t ht
  simp [ENNReal.toReal_ofReal ht]

end AbsolutelyContinuousOnInterval

/-- For `g` interval integrable on `c..d`, with primitive `G u = ∫ v in c..u, g v`,
`|∫ u in c..d, g u * exp |G u|| = exp |G d| - 1`, whatever the order of `c` and `d` and the sign
of `g`. This gives the exponential bound for linear equations with integrable coefficients. -/
theorem IntervalIntegrable.abs_integral_mul_exp_abs_integral {g : ℝ → ℝ} {c d : ℝ}
    (hg : IntervalIntegrable g volume c d) :
    |∫ u in c..d, g u * Real.exp (|∫ v in c..u, g v|)| = Real.exp |∫ v in c..d, g v| - 1 := by
  -- Substitute `G` in `∫ exp |y|`, using `deriv G = g` almost everywhere.
  have hc : Continuous fun y : ℝ ↦ Real.exp |y| := by fun_prop
  have h := (hg.absolutelyContinuousOnInterval_intervalIntegral
    left_mem_uIcc).integral_comp_mul_deriv_of_continuous hc
  have hderiv : ∀ᵐ s, s ∈ uIoc c d →
      Real.exp |∫ v in c..s, g v| * deriv (fun s ↦ ∫ v in c..s, g v) s =
        g s * Real.exp |∫ v in c..s, g v| := by
    filter_upwards [hg.ae_hasDerivAt_integral] with s hs hsI
    rw [(hs (uIoc_subset_uIcc hsI) c left_mem_uIcc).deriv, mul_comm]
  rw [intervalIntegral.integral_congr_ae hderiv, intervalIntegral.integral_same] at h
  rw [h]
  -- `|∫ y in 0..x, exp |y|| = exp |x| - 1`, computing the integral on each side of `0`.
  rcases le_total 0 (∫ v in c..d, g v) with hx | hx
  · have : ∫ y in 0..∫ v in c..d, g v, Real.exp |y| = Real.exp (∫ v in c..d, g v) - 1 := by
      rw [← Real.exp_zero]
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy ↦ ?_)
        (hc.intervalIntegrable _ _)
      rw [uIcc_of_le hx] at hy
      simpa [abs_of_nonneg hy.1] using Real.hasDerivAt_exp y
    rw [this, abs_of_nonneg hx, abs_of_nonneg (sub_nonneg.2 (Real.one_le_exp hx))]
  · have : ∫ y in 0..∫ v in c..d, g v, Real.exp |y| =
        -(Real.exp (-∫ v in c..d, g v) - 1) := by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y ↦ -Real.exp (-y))
        (a := 0) (b := ∫ v in c..d, g v) (fun y hy ↦ ?_) (hc.intervalIntegrable _ _)
      · simp only [this, neg_zero, Real.exp_zero]
        ring
      · rw [uIcc_of_ge hx] at hy
        simpa [abs_of_nonpos hy.2] using (hasDerivAt_neg y).exp.fun_neg
    rw [this, abs_neg, abs_of_nonpos hx,
      abs_of_nonneg (sub_nonneg.2 (Real.one_le_exp (neg_nonneg.2 hx)))]
