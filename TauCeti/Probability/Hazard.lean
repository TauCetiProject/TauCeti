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

* `TauCeti.Probability.survival_eq_exp_integral_hazard` — a positive absolutely continuous
  survival function is reconstructed from its hazard rate;
* `TauCeti.Probability.intervalIntegrable_div_one_sub_cdf` — the hazard rate of a cdf is integrable
  on an interval of positive survival;
* `TauCeti.Probability.one_sub_cdf_eq_mul_exp_neg_integral` — the hazard reconstruction of the
  survival function;
* `TauCeti.Probability.hasDerivAt_neg_log_one_sub_cdf` — the cumulative hazard has the hazard rate
  as its derivative wherever the cdf is differentiable and survival is positive;
* `TauCeti.Probability.one_sub_cdf_zero_eq_one_of_absolutelyContinuous` — survival starts at one
  for an absolutely continuous law carried by the nonnegative half-line;
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

/-- **Survival reconstruction from the hazard rate.** If `S` is absolutely continuous on the
interval between `a` and `x`, is positive there, and has derivative `-f` almost everywhere, then
the hazard rate `f / S` is interval integrable and
`S x = S a * exp (-∫ t in a..x, f t / S t)`. -/
theorem survival_eq_exp_integral_hazard {S : ℝ → ℝ}
    (hS : AbsolutelyContinuousOnInterval S a x) (hpos : ∀ t ∈ uIcc a x, 0 < S t)
    (hderiv : ∀ᵐ t, t ∈ uIoc a x → HasDerivAt S (-f t) t) :
    IntervalIntegrable (fun t => f t / S t) volume a x ∧
      S x = S a * Real.exp (-∫ t in a..x, f t / S t) := by
  have hne : ∀ t ∈ uIcc a x, S t ≠ 0 := fun t ht => (hpos t ht).ne'
  have hint : IntervalIntegrable (fun t => f t / S t) volume a x := by
    have h : (fun t => f t / S t) = -fun t => -f t / S t := by
      ext t
      simp [neg_div]
    rw [h]
    exact (hS.intervalIntegrable_div_of_ae_hasDerivAt hne hderiv).neg
  refine ⟨hint, ?_⟩
  have h := hS.integral_div_eq_log_sub_log hne hderiv
  simp only [neg_div, intervalIntegral.integral_neg] at h
  have ha : 0 < S a := hpos a left_mem_uIcc
  have hx : 0 < S x := hpos x right_mem_uIcc
  rw [h, Real.exp_sub, Real.exp_log hx, Real.exp_log ha]
  field_simp

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

/-- **Survival starts at one.** An absolutely continuous probability law carried by the
nonnegative half-line has survival probability one at zero. -/
theorem one_sub_cdf_zero_eq_one_of_absolutelyContinuous [IsProbabilityMeasure μ]
    (hac : μ ≪ volume) (h0 : μ (Iio 0) = 0) :
    1 - cdf μ 0 = 1 := by
  have : NullSingletonClass μ := ⟨fun t => hac (measure_singleton t)⟩
  rw [Measure.cdf_eq_zero_of_measure_Iio_eq_zero μ h0, sub_zero]

/-! ### Laws with a density -/

section Density

variable [IsProbabilityMeasure μ]

/-- **Survival on the half-line from the cumulative hazard.** For a law with a nonnegative density
`f` carried by `[0, ∞)`, survival at `x ≥ 0` is `exp (-∫ t in 0..x, f t / (1 - cdf μ t))`
whenever it is positive. -/
theorem one_sub_cdf_eq_exp_neg_integral_of_eq_withDensity
    (hμ : μ = volume.withDensity fun t => ENNReal.ofReal (f t)) (hfm : AEMeasurable f)
    (hnn : 0 ≤ᵐ[volume] f) (h0 : μ (Iio 0) = 0) (hx : 0 ≤ x) (hSx : cdf μ x < 1) :
    1 - cdf μ x = Real.exp (-∫ t in (0 : ℝ)..x, f t / (1 - cdf μ t)) := by
  have hS : ∀ t ∈ uIcc 0 x, cdf μ t < 1 := fun t ht =>
    ((cdf μ).mono (uIcc_of_le hx ▸ ht).2).trans_lt hSx
  rw [one_sub_cdf_eq_mul_exp_neg_integral
    (absolutelyContinuousOnInterval_cdf_of_eq_withDensity hμ hfm hnn 0 x) hS
    ((ae_hasDerivAt_cdf_of_eq_withDensity hμ hfm hnn).mono fun _ ht _ => ht),
    one_sub_cdf_zero_eq_one_of_absolutelyContinuous
      (hμ ▸ withDensity_absolutelyContinuous volume _) h0, one_mul]

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
