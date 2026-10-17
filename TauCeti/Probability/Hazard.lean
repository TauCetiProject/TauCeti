/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.Probability.Cdf
import TauCeti.Probability.Density
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Survival functions and hazard rates

For a probability measure `μ` on `ℝ`, the survival function is `S = 1 - cdf μ`. When the cdf has
derivative `f`, the hazard rate is `f / S` and the cumulative hazard is `-log S`. Both are only
meaningful where survival is positive, and every identity below assumes positive survival on the
interval it concerns; outside it the expressions keep the ordinary totalized division and logarithm.

The central identity reconstructs the survival function from the hazard rate,
`S x = S a * exp (-∫ t in a..x, f t / S t)`, whenever the cdf is absolutely continuous between `a`
and `x`, survival is positive there, and `f` is the derivative of the cdf almost everywhere. It is
the fundamental theorem of calculus for the logarithmic derivative of `S`.

These hypotheses hold for a law presented as `volume.withDensity (ENNReal.ofReal ∘ f)` with a
nonnegative density `f`. The increment of its cdf over `a..b` is `∫ t in a..b, f t`, so its cdf is
absolutely continuous on every compact interval, has derivative `f` almost everywhere by the
Lebesgue differentiation theorem, and has derivative `f t` at every point `t` where `f` is
continuous. For a law carried by `[0, ∞)` survival starts at one, so the cumulative hazard alone
determines it: `S x = exp (-∫ t in 0..x, f t / S t)`.

## Main results

* `TauCeti.Probability.intervalIntegrable_hazard` — the hazard rate is integrable on an interval
  of positive survival;
* `TauCeti.Probability.one_sub_cdf_eq_mul_exp_neg_integral` — the hazard reconstruction of the
  survival function;
* `TauCeti.Probability.hasDerivAt_neg_log_one_sub_cdf` — the cumulative hazard has the hazard rate
  as its derivative wherever the cdf is differentiable and survival is positive;
* `TauCeti.Probability.cdf_sub_cdf_eq_integral_of_eq_withDensity`,
  `TauCeti.Probability.absolutelyContinuousOnInterval_cdf_of_eq_withDensity`,
  `TauCeti.Probability.ae_hasDerivAt_cdf_of_eq_withDensity` and
  `TauCeti.Probability.hasDerivAt_cdf_of_eq_withDensity` — the cdf of a law with a density is an
  indefinite integral of the density, hence absolutely continuous and differentiable with
  derivative the density almost everywhere and at its points of continuity;
* `TauCeti.Probability.one_sub_cdf_eq_exp_neg_integral_of_eq_withDensity` and
  `TauCeti.Probability.one_sub_cdf_eq_exp_neg_integral_rnDeriv` — survival is the exponential of
  minus the cumulative hazard for a law on `[0, ∞)` with a density, or absolutely continuous with
  respect to Lebesgue measure.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {μ : Measure ℝ} {f : ℝ → ℝ} {a x : ℝ}

/-! ### Hazard reconstruction -/

/-- **Derivative of the cumulative hazard.** Where the cdf has derivative `d` and survival is
positive, the cumulative hazard `-log (1 - cdf μ)` has derivative the hazard rate
`d / (1 - cdf μ t)`. -/
theorem hasDerivAt_neg_log_one_sub_cdf {t d : ℝ} (hd : HasDerivAt (cdf μ) d t)
    (ht : cdf μ t < 1) :
    HasDerivAt (fun s => -Real.log (1 - cdf μ s)) (d / (1 - cdf μ t)) t := by
  simpa [neg_div] using ((hd.const_sub 1).log (sub_pos.2 ht).ne').fun_neg

private theorem absolutelyContinuousOnInterval_one_sub_cdf
    (hac : AbsolutelyContinuousOnInterval (cdf μ) a x) :
    AbsolutelyContinuousOnInterval (fun t => 1 - cdf μ t) a x :=
  (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval.sub hac

private theorem ae_hasDerivAt_one_sub_cdf
    (hf : ∀ᵐ t, t ∈ uIoc a x → HasDerivAt (cdf μ) (f t) t) :
    ∀ᵐ t, t ∈ uIoc a x → HasDerivAt (fun t => 1 - cdf μ t) (-f t) t := by
  filter_upwards [hf] with t ht hmem
  exact (ht hmem).const_sub 1

private theorem one_sub_cdf_ne_zero (hS : ∀ t ∈ uIcc a x, cdf μ t < 1) :
    ∀ t ∈ uIcc a x, 1 - cdf μ t ≠ 0 :=
  fun t ht => (sub_pos.2 (hS t ht)).ne'

/-- **Integrability of the hazard rate.** If the cdf is absolutely continuous on the interval
between `a` and `x`, survival is positive there, and `f` is the derivative of the cdf almost
everywhere, then the hazard rate `f / (1 - cdf μ)` is interval integrable on `a..x`. -/
theorem intervalIntegrable_hazard (hac : AbsolutelyContinuousOnInterval (cdf μ) a x)
    (hS : ∀ t ∈ uIcc a x, cdf μ t < 1)
    (hf : ∀ᵐ t, t ∈ uIoc a x → HasDerivAt (cdf μ) (f t) t) :
    IntervalIntegrable (fun t => f t / (1 - cdf μ t)) volume a x := by
  have h : (fun t => f t / (1 - cdf μ t)) = -fun t => -f t / (1 - cdf μ t) := by
    ext t
    simp [neg_div]
  rw [h]
  exact ((absolutelyContinuousOnInterval_one_sub_cdf hac).intervalIntegrable_div_of_ae_hasDerivAt
    (one_sub_cdf_ne_zero hS) (ae_hasDerivAt_one_sub_cdf hf)).neg

/-- **Hazard reconstruction of the survival function.** If the cdf is absolutely continuous on the
interval between `a` and `x`, survival is positive there, and `f` is the derivative of the cdf
almost everywhere, then `1 - cdf μ x = (1 - cdf μ a) * exp (-∫ t in a..x, f t / (1 - cdf μ t))`.
-/
theorem one_sub_cdf_eq_mul_exp_neg_integral (hac : AbsolutelyContinuousOnInterval (cdf μ) a x)
    (hS : ∀ t ∈ uIcc a x, cdf μ t < 1)
    (hf : ∀ᵐ t, t ∈ uIoc a x → HasDerivAt (cdf μ) (f t) t) :
    1 - cdf μ x = (1 - cdf μ a) * Real.exp (-∫ t in a..x, f t / (1 - cdf μ t)) := by
  have h := (absolutelyContinuousOnInterval_one_sub_cdf hac).integral_div_eq_log_sub_log
    (one_sub_cdf_ne_zero hS) (ae_hasDerivAt_one_sub_cdf hf)
  simp only [neg_div, intervalIntegral.integral_neg] at h
  have ha : 0 < 1 - cdf μ a := sub_pos.2 (hS a left_mem_uIcc)
  have hx : 0 < 1 - cdf μ x := sub_pos.2 (hS x right_mem_uIcc)
  rw [h, Real.exp_sub, Real.exp_log hx, Real.exp_log ha]
  field_simp

/-! ### Laws with a density -/

section Density

variable [IsProbabilityMeasure μ]

/-- The density of a law is integrable, since the constant `1` is integrable under the law. -/
private theorem integrable_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) : Integrable f := by
  have h1 : Integrable (fun _ => (1 : ℝ)) μ := integrable_const 1
  rw [hμ, integrable_withDensity_ofReal_iff hfm hnn] at h1
  simpa using h1

/-- **The cdf increment of a law with a density.** For a law with nonnegative density `f`, the
increment of the cdf over `a..b` is the integral of the density over `a..b`. -/
theorem cdf_sub_cdf_eq_integral_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) (a b : ℝ) :
    cdf μ b - cdf μ a = ∫ t in a..b, f t := by
  wlog hab : a ≤ b generalizing a b
  · rw [intervalIntegral.integral_symm, ← this b a (le_of_not_ge hab), neg_sub]
  rw [← Measure.measureReal_Ioc_eq_cdf_sub μ hab, intervalIntegral.integral_of_le hab, hμ]
  exact measureReal_withDensity_ofReal (ae_restrict_of_ae hnn) measurableSet_Ioc
    (integrable_of_eq_withDensity hμ hfm hnn).integrableOn

private theorem cdf_eq_add_integral_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) (c : ℝ) :
    ⇑(cdf μ) = fun s => cdf μ c + ∫ t in c..s, f t := by
  ext s
  rw [← cdf_sub_cdf_eq_integral_of_eq_withDensity hμ hfm hnn c s]
  ring

/-- The cdf of a law with a nonnegative density is absolutely continuous on every compact
interval. -/
theorem absolutelyContinuousOnInterval_cdf_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (cdf μ) a b := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => cdf μ a) a b :=
    (LipschitzWith.const (cdf μ a)).lipschitzOnWith.absolutelyContinuousOnInterval
  rw [cdf_eq_add_integral_of_eq_withDensity hμ hfm hnn a]
  exact hc.add ((integrable_of_eq_withDensity hμ hfm hnn).intervalIntegrable
    |>.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc)

/-- **Lebesgue differentiation of the cdf.** The cdf of a law with a nonnegative density `f` has
derivative `f t` at almost every point `t`. -/
theorem ae_hasDerivAt_cdf_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) :
    ∀ᵐ t, HasDerivAt (cdf μ) (f t) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (integrable_of_eq_withDensity hμ hfm hnn).locallyIntegrable] with t ht
  rw [cdf_eq_add_integral_of_eq_withDensity hμ hfm hnn 0]
  exact (ht 0).const_add _

/-- The cdf of a law with a nonnegative density `f` has derivative `f t` at every point `t` where
the density is continuous. -/
theorem hasDerivAt_cdf_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) {t : ℝ} (hft : ContinuousAt f t) :
    HasDerivAt (cdf μ) (f t) t := by
  have hfi := integrable_of_eq_withDensity hμ hfm hnn
  rw [cdf_eq_add_integral_of_eq_withDensity hμ hfm hnn 0]
  exact (intervalIntegral.integral_hasDerivAt_right hfi.intervalIntegrable
    hfi.aestronglyMeasurable.stronglyMeasurableAtFilter hft).const_add _

/-- **Survival on the half-line from the cumulative hazard.** For a law with a nonnegative density
`f` carried by `[0, ∞)`, survival at `x ≥ 0` is `exp (-∫ t in 0..x, f t / (1 - cdf μ t))`
whenever it is positive. -/
theorem one_sub_cdf_eq_exp_neg_integral_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) (h0 : μ (Iio 0) = 0) (hx : 0 ≤ x) (hSx : cdf μ x < 1) :
    1 - cdf μ x = Real.exp (-∫ t in (0 : ℝ)..x, f t / (1 - cdf μ t)) := by
  have : NullSingletonClass μ := hμ ▸ inferInstance
  have hS : ∀ t ∈ uIcc 0 x, cdf μ t < 1 := fun t ht =>
    ((cdf μ).mono (uIcc_of_le hx ▸ ht).2).trans_lt hSx
  rw [one_sub_cdf_eq_mul_exp_neg_integral
    (absolutelyContinuousOnInterval_cdf_of_eq_withDensity hμ hfm hnn 0 x) hS
    ((ae_hasDerivAt_cdf_of_eq_withDensity hμ hfm hnn).mono fun _ ht _ => ht),
    Measure.cdf_eq_zero_of_measure_Iio_eq_zero μ h0, sub_zero, one_mul]

/-- **Survival on the half-line for an absolutely continuous law.** For a law that is absolutely
continuous with respect to Lebesgue measure and carried by `[0, ∞)`, survival at `x ≥ 0` is
`exp (-∫ t in 0..x, h t)` whenever it is positive, where the hazard rate `h` is the
Radon–Nikodym derivative divided by survival. -/
theorem one_sub_cdf_eq_exp_neg_integral_rnDeriv (hac : μ ≪ volume) (h0 : μ (Iio 0) = 0)
    (hx : 0 ≤ x) (hSx : cdf μ x < 1) :
    1 - cdf μ x =
      Real.exp (-∫ t in (0 : ℝ)..x, (μ.rnDeriv volume t).toReal / (1 - cdf μ t)) := by
  refine one_sub_cdf_eq_exp_neg_integral_of_eq_withDensity ?_
    (Measure.measurable_rnDeriv μ volume).ennreal_toReal.aemeasurable
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) h0 hx hSx
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ volume hac]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top μ volume] with t ht
  rw [ENNReal.ofReal_toReal ht.ne]

end Density

end TauCeti.Probability
