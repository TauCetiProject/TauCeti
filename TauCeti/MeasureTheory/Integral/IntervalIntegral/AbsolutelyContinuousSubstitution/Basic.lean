/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Substitution by absolutely continuous changes of parameter

Absolutely continuous substitutions satisfy change of variables for continuous integrands.
For monotone substitutions, the derivative-weighted pushforward of interval volume is interval
volume on the image, giving change of variables and transformed integrability for arbitrary
integrable normed-space-valued integrands. This accommodates constant pieces and unbounded
parameter speeds.
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
