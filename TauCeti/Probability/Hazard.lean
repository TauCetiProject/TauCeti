/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import TauCeti.Probability.Cdf.Density
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Survival functions and hazard rates

For a probability measure `μ` on `ℝ`, the survival function is `S = 1 - cdf μ`. When the cdf has
derivative `f`, the hazard rate is `f / S` and the cumulative hazard is `-log S`. Both are only
meaningful where survival is positive, and every identity below assumes positive survival on the
interval it concerns; outside it the expressions keep the ordinary totalized division and logarithm.

The central identity reconstructs an arbitrary survival function from the hazard rate,
`S x = S a * exp (-∫ t in a..x, f t / S t)`, whenever `S` is absolutely continuous between `a`
and `x`, positive there, and has derivative `-f` almost everywhere. It is the fundamental theorem
of calculus for the logarithmic derivative of `S`.

These hypotheses hold for a law presented as `volume.withDensity (ENNReal.ofReal ∘ f)` with a
nonnegative density `f`. The increment of its cdf over `a..b` is `∫ t in a..b, f t`, so its cdf is
absolutely continuous on every compact interval, has derivative `f` almost everywhere by the
Lebesgue differentiation theorem, and has derivative `f t` at every point `t` where `f` is
continuous. For a law carried by `[0, ∞)` survival starts at one, so the cumulative hazard alone
determines it: `S x = exp (-∫ t in 0..x, f t / S t)`.

## Main results

* `TauCeti.Probability.intervalIntegrable_div_one_sub_cdf` — the hazard rate of a cdf is integrable
  on an interval of positive survival;
* `TauCeti.Probability.one_sub_cdf_eq_mul_exp_neg_integral` — the hazard reconstruction of the
  survival function;
* `TauCeti.Probability.hasDerivAt_neg_log_one_sub_cdf` — the cumulative hazard has the hazard rate
  as its derivative wherever the cdf is differentiable and survival is positive;
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

/-- **Integrability of the hazard rate.** If the cdf is absolutely continuous on the interval
between `a` and `x`, survival is positive there, and `f` is the derivative of the cdf almost
everywhere, then the hazard rate `f / (1 - cdf μ)` is interval integrable on `a..x`. -/
theorem intervalIntegrable_div_one_sub_cdf (hac : AbsolutelyContinuousOnInterval (cdf μ) a x)
    (hS : ∀ t ∈ uIcc a x, cdf μ t < 1)
    (hf : ∀ᵐ t, t ∈ uIoc a x → HasDerivAt (cdf μ) (f t) t) :
    IntervalIntegrable (fun t => f t / (1 - cdf μ t)) volume a x := by
  exact (survival_eq_exp_integral_hazard (absolutelyContinuousOnInterval_one_sub_cdf hac)
    (fun t ht => sub_pos.2 (hS t ht)) (ae_hasDerivAt_one_sub_cdf hf)).1

/-- **Hazard reconstruction of the survival function.** If the cdf is absolutely continuous on the
interval between `a` and `x`, survival is positive there, and `f` is the derivative of the cdf
almost everywhere, then `1 - cdf μ x = (1 - cdf μ a) * exp (-∫ t in a..x, f t / (1 - cdf μ t))`.
-/
theorem one_sub_cdf_eq_mul_exp_neg_integral (hac : AbsolutelyContinuousOnInterval (cdf μ) a x)
    (hS : ∀ t ∈ uIcc a x, cdf μ t < 1)
    (hf : ∀ᵐ t, t ∈ uIoc a x → HasDerivAt (cdf μ) (f t) t) :
    1 - cdf μ x = (1 - cdf μ a) * Real.exp (-∫ t in a..x, f t / (1 - cdf μ t)) := by
  exact (survival_eq_exp_integral_hazard (absolutelyContinuousOnInterval_one_sub_cdf hac)
    (fun t ht => sub_pos.2 (hS t ht)) (ae_hasDerivAt_one_sub_cdf hf)).2

/-! ### Laws with a density -/

section Density

variable [IsProbabilityMeasure μ]

/-- The hazard of a law with a nonnegative density is integrable on every compact interval
where survival stays positive. -/
theorem intervalIntegrable_div_one_sub_cdf_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) (a b : ℝ) (hS : ∀ t ∈ uIcc a b, cdf μ t < 1) :
    IntervalIntegrable (fun t => f t / (1 - cdf μ t)) volume a b :=
  intervalIntegrable_div_one_sub_cdf
    (absolutelyContinuousOnInterval_cdf_of_eq_withDensity hμ hfm hnn a b) hS
    ((ae_hasDerivAt_cdf_of_eq_withDensity hμ hfm hnn).mono fun _ ht _ => ht)

/-- **Survival on the half-line from the cumulative hazard.** For a law with a nonnegative density
`f` carried by `[0, ∞)`, survival at `x` is `exp (-∫ t in 0..x, f t / (1 - cdf μ t))`
whenever it is positive. -/
theorem one_sub_cdf_eq_exp_neg_integral_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) (h0 : μ (Iio 0) = 0) (hSx : cdf μ x < 1) :
    1 - cdf μ x = Real.exp (-∫ t in (0 : ℝ)..x, f t / (1 - cdf μ t)) := by
  have : NullSingletonClass μ := by rw [hμ]; infer_instance
  have hcdf0 : cdf μ 0 = 0 := Measure.cdf_eq_zero_of_measure_Iio_eq_zero μ h0
  have hmax : cdf μ (max 0 x) < 1 := by
    rcases le_total 0 x with hx | hx
    · simpa [max_eq_right hx] using hSx
    · simp [max_eq_left hx, hcdf0]
  have hS : ∀ t ∈ uIcc 0 x, cdf μ t < 1 := fun t ht =>
    (monotone_cdf μ ht.2).trans_lt hmax
  rw [one_sub_cdf_eq_mul_exp_neg_integral
    (absolutelyContinuousOnInterval_cdf_of_eq_withDensity hμ hfm hnn 0 x) hS
    ((ae_hasDerivAt_cdf_of_eq_withDensity hμ hfm hnn).mono fun _ ht _ => ht),
    one_sub_cdf_zero_eq_one h0, one_mul]

/-- For a law with a nonnegative density carried by `[0, ∞)`, the integral of the hazard from
zero is the cumulative hazard wherever survival is positive. -/
theorem integral_div_one_sub_cdf_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) (h0 : μ (Iio 0) = 0) (hSx : cdf μ x < 1) :
    ∫ t in (0 : ℝ)..x, f t / (1 - cdf μ t) = -Real.log (1 - cdf μ x) := by
  have h := congrArg Real.log
    (one_sub_cdf_eq_exp_neg_integral_of_eq_withDensity hμ hfm hnn h0 hSx)
  rw [Real.log_exp] at h
  linarith

/-- **Survival on the half-line for an absolutely continuous law.** For a law that is absolutely
continuous with respect to Lebesgue measure and carried by `[0, ∞)`, survival at `x` is
`exp (-∫ t in 0..x, h t)` whenever it is positive, where the hazard rate `h` is the
Radon–Nikodym derivative divided by survival. -/
theorem one_sub_cdf_eq_exp_neg_integral_rnDeriv (hac : μ ≪ volume) (h0 : μ (Iio 0) = 0)
    (hSx : cdf μ x < 1) :
    1 - cdf μ x =
      Real.exp (-∫ t in (0 : ℝ)..x, (μ.rnDeriv volume t).toReal / (1 - cdf μ t)) := by
  refine one_sub_cdf_eq_exp_neg_integral_of_eq_withDensity ?_
    (Measure.measurable_rnDeriv μ volume).ennreal_toReal.aemeasurable
    (ae_of_all _ fun _ => ENNReal.toReal_nonneg) h0 hSx
  conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ volume hac]
  refine withDensity_congr_ae ?_
  filter_upwards [Measure.rnDeriv_lt_top μ volume] with t ht
  rw [ENNReal.ofReal_toReal ht.ne]

end Density

end TauCeti.Probability
