/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import TauCeti.MeasureTheory.Integral.Bochner.OperatorField
import Mathlib.MeasureTheory.Function.Holder

/-!
# Convergence of integrals of bounded 1-forms

Bounded continuous 1-forms preserve convergence of actual integrals along absolutely
continuous curves under uniform convergence of curves and `L¹` convergence of derivatives.
The statements use the raw-curve integral `∫ t in a..b, ω (γ t) (deriv γ t)`.
For a `Path`, Mathlib's `curveIntegral_eq_intervalIntegral_deriv` gives this representation.
No uniform bound on the approximating velocities is assumed.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace AbsolutelyContinuousOnInterval

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {a b : ℝ} {γ : ℝ → E}
  {ω : E → E →L[ℝ] F}

/-- A bounded continuous 1-form is integrable along an absolutely continuous curve. -/
theorem intervalIntegrable_oneForm_of_continuous_bounded
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hω : Continuous ω)
    {C : ℝ} (hbound : ∀ z, ‖ω z‖ ≤ C) :
    IntervalIntegrable (fun t ↦ ω (γ t) (deriv γ t)) volume a b := by
  rw [intervalIntegrable_iff]
  exact (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).integrable_of_bilin_of_bdd_left C
    ((hω.comp_continuousOn (hγ.continuousOn.mono uIoc_subset_uIcc)).aestronglyMeasurable
      measurableSet_uIoc) (Eventually.of_forall fun t ↦ hbound (γ t))
    hγ.intervalIntegrable_deriv_of_finiteDimensional.def'


/-- Uniform convergence of AC curves and `L¹` convergence of their derivatives imply
convergence of the raw integrals `∫ t in a..b, ω (γ t) (deriv γ t)`
of any bounded continuous 1-form. -/
theorem tendsto_integral_oneForm_of_tendstoUniformlyOn {γn : ℕ → ℝ → E}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hγn : ∀ n, AbsolutelyContinuousOnInterval (γn n) a b) (hab : a ≤ b)
    (hω : Continuous ω) {C : ℝ} (hbound : ∀ z, ‖ω z‖ ≤ C)
    (hconv : TendstoUniformlyOn γn γ atTop (Icc a b))
    (hdconv : Tendsto (fun n ↦ ∫ t in a..b, ‖deriv (γn n) t - deriv γ t‖)
      atTop (nhds 0)) :
    Tendsto (fun n ↦ ∫ t in a..b, ω (γn n t) (deriv (γn n) t)) atTop
      (nhds (∫ t in a..b, ω (γ t) (deriv γ t))) := by
  simp only [intervalIntegral.integral_of_le hab] at hdconv ⊢
  apply tendsto_integral_clm_apply_of_integral_norm_sub
  · intro n
    exact ((hω.comp_continuousOn ((hγn n).continuousOn.mono
      (by simpa only [uIcc_of_le hab] using Ioc_subset_Icc_self))).aestronglyMeasurable
        measurableSet_Ioc)
  · exact ((hω.comp_continuousOn (hγ.continuousOn.mono
      (by simpa only [uIcc_of_le hab] using Ioc_subset_Icc_self))).aestronglyMeasurable
        measurableSet_Ioc)
  · intro n
    exact Eventually.of_forall fun t ↦ hbound (γn n t)
  · exact Eventually.of_forall fun t ↦ hbound (γ t)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hω.tendsto (γ t)).comp (hconv.tendsto_at (Ioc_subset_Icc_self ht))
  · intro n
    simpa only [uIoc_of_le hab, IntegrableOn] using
      (hγn n).intervalIntegrable_deriv_of_finiteDimensional.def'
  · simpa only [uIoc_of_le hab, IntegrableOn] using
      hγ.intervalIntegrable_deriv_of_finiteDimensional.def'
  · exact hdconv

end AbsolutelyContinuousOnInterval
