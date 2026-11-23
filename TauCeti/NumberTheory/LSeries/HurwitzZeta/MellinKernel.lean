/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import TauCeti.Analysis.MellinTransform.ExpKernel
public import TauCeti.NumberTheory.LSeries.HurwitzZeta.Series
import TauCeti.Analysis.SpecialFunctions.Exp.InvSubOne
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate

/-!
# Mellin–Laplace kernel for the complex Hurwitz zeta function

Bridges the elementary Mellin–Laplace kernel estimates in
`TauCeti.Analysis.MellinTransform.ExpKernel` (`TauCeti.integrableOn_hurwitzMellinIntegrand`,
`TauCeti.exists_integrableOn_norm_hurwitzMellinIntegrand_le`, and
`TauCeti.hasSum_setIntegral_cpow_mul_exp_neg_mul`) to `TauCeti.complexHurwitzSeries`: for
`1 < Re s` and `0 < Re c`,
`∫₀^∞ t^{s−1} e^{−ct} / (1 − e^{−t}) dt = Γ(s) * complexHurwitzSeries s c`.

## Main results

* `TauCeti.integral_hurwitzMellinIntegrand_eq_Gamma_mul_complexHurwitzSeries`:
  `∫₀^∞ t^{s−1} e^{−ct} / (1 − e^{−t}) dt = Γ(s) * complexHurwitzSeries s c` for `1 < s.re` and
  `0 < c.re`.
-/

public section

noncomputable section

open Complex MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- For `1 < s.re` and `0 < c.re`, the Mellin–Laplace integral of the Hurwitz kernel equals
`Gamma s * complexHurwitzSeries s c`. -/
theorem integral_hurwitzMellinIntegrand_eq_Gamma_mul_complexHurwitzSeries {s c : ℂ}
    (hs : 1 < s.re) (hc : 0 < c.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t))) =
      Gamma s * complexHurwitzSeries s c := by
  have hs0 : 0 < s.re := by linarith
  have hkernel : EqOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (cexp (-c * t) / (1 - cexp (-t))))
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * (cexp ((1 - c) * t) / (cexp t - 1))) (Ioi 0) :=
    fun t _ => by simp only [Complex.exp_neg_mul_div_one_sub_exp_neg]
  rw [setIntegral_congr_fun measurableSet_Ioi hkernel]
  have hsum := hasSum_setIntegral_cpow_mul_exp_neg_mul hs hc subset_rfl
  have hterm : (fun k : ℕ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + c) * t))) =
      fun k : ℕ => Gamma s * ((k : ℂ) + c) ^ (-s) := funext fun k => by
    have hk : 0 < ((k : ℂ) + c).re := by
      simp only [add_re, natCast_re]
      positivity
    exact integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hs0 hk
  rw [hterm] at hsum
  exact hsum.unique ((hasSum_complexHurwitzSeries_of_re_pos hs hc).mul_left (Gamma s))

end TauCeti

end
