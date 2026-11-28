/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.NumberTheory.LSeries.ComplexHurwitzSeries
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy
import TauCeti.Analysis.MellinTransform.Growth
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.InvSubOne
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Mellin–Laplace kernel for the complex Hurwitz zeta function

Bridges `TauCeti.complexHurwitzSeries_eq_integral` in
`TauCeti.NumberTheory.LSeries.ComplexHurwitzSeries` to the form
`∫₀^∞ t^{s−1} e^{−ct} / (1 − e^{−t}) dt = Γ(s) * complexHurwitzSeries s c` for `1 < Re s` and
`0 < Re c`.

Splitting off the exponential tail on `(1, ∞)` defines `TauCeti.hurwitzTailIntegral`, which
converges for all `s : ℂ` when `0 < Re c` and is jointly analytic on
`{p : ℂ × ℂ | 0 < p.2.re}`.

## Main results

* `TauCeti.integral_cpow_mul_exp_neg_mul_div_one_sub_exp_neg_eq_Gamma_mul_complexHurwitzSeries`:
  `∫₀^∞ t^{s−1} e^{−ct} / (1 − e^{−t}) dt = Γ(s) * complexHurwitzSeries s c` for `1 < s.re` and
  `0 < c.re`.
* `TauCeti.hurwitzTailIntegral`, `TauCeti.hurwitzTailIntegral_def`,
  `TauCeti.integrableOn_Ioi_one_cpow_mul_exp_neg_mul_div_one_sub_exp_neg`, and
  `TauCeti.analyticOnNhd_hurwitzTailIntegral`:
  the exponential tail integral on `(1, ∞)` and its joint analyticity on
  `{p : ℂ × ℂ | 0 < p.2.re}`.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- For `1 < s.re` and `0 < c.re`, the Mellin–Laplace integral of the Hurwitz kernel equals
`Gamma s * complexHurwitzSeries s c`. -/
theorem integral_cpow_mul_exp_neg_mul_div_one_sub_exp_neg_eq_Gamma_mul_complexHurwitzSeries
    {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t))) =
      Gamma s * complexHurwitzSeries s c := by
  have hs0 : 0 < s.re := by linarith
  rw [complexHurwitzSeries_eq_integral hs hc, mul_inv_cancel_left₀ (Gamma_ne_zero_of_re_pos hs0)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  ring_nf

/-- The exponential tail integral on `(1, ∞)`,
`∫ t in Ioi 1, (t : ℂ) ^ (s - 1) * (Complex.exp (-c * t) / (1 - Complex.exp (-t)))`. -/
noncomputable def hurwitzTailIntegral (s c : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))

/-- Defining equation for `hurwitzTailIntegral`. -/
theorem hurwitzTailIntegral_def (s c : ℂ) :
    hurwitzTailIntegral s c =
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t))) := (rfl)

/-- For `0 < c.re`, the tail integrand `t ↦ (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))`
is integrable on `Ioi 1`. -/
theorem integrableOn_Ioi_one_cpow_mul_exp_neg_mul_div_one_sub_exp_neg (s : ℂ) {c : ℂ}
    (hc : 0 < c.re) :
    IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (exp (-c * t) / (1 - exp (-t)))) (Ioi 1) :=
  integrableOn_cpow_smul_of_norm_le_exp_neg_mul_rpow hc one_pos
    (Measurable.aestronglyMeasurable (by fun_prop))
    (fun _ ht => by
      simpa only [Real.rpow_one] using norm_exp_neg_mul_div_one_sub_exp_neg_le one_pos ht.le c) s

/-- The exponential tail integral is jointly analytic on `{p : ℂ × ℂ | 0 < p.2.re}`. -/
theorem analyticOnNhd_hurwitzTailIntegral :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => hurwitzTailIntegral p.1 p.2) {p | 0 < p.2.re} := by
  refine TauCeti.analyticOnNhd_integral_of_dominated
    (isOpen_lt continuous_const (continuous_re.comp continuous_snd))
    (fun p hp =>
      (integrableOn_Ioi_one_cpow_mul_exp_neg_mul_div_one_sub_exp_neg p.1 hp).aestronglyMeasurable)
    ?_ ?_
  · intro p₀ hp₀
    rw [mem_ofPred_eq] at hp₀
    let η := p₀.2.re / 2
    have hη : 0 < η := by dsimp [η]; linarith
    refine ⟨{p : ℂ × ℂ | p.1.re < p₀.1.re + 1 ∧ η < p.2.re},
      ((isOpen_lt (continuous_re.comp continuous_fst) continuous_const).inter
        (isOpen_lt continuous_const (continuous_re.comp continuous_snd))).mem_nhds
        ⟨lt_add_one _, by dsimp [η]; linarith⟩,
      fun t : ℝ => (1 - Real.exp (-1))⁻¹ * (t ^ p₀.1.re * Real.exp (-η * t)),
      (integrableOn_rpow_mul_exp_neg_mul_Ioi_of_pos one_pos (Or.inl hη)).const_mul _, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht p ⟨hp1, hp2⟩
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), sub_re, one_re]
    exact rpow_mul_norm_exp_neg_mul_div_one_sub_exp_neg_le one_pos ht.le ht.le
      (by linarith [hp1]) hp2.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht p _
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (DifferentiableAt.const_cpow (by fun_prop)
      (Or.inl (ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'))).mul (by fun_prop)

end TauCeti

end
