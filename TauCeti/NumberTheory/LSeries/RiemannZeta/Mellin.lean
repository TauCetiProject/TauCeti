/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Analysis.SpecialFunctions.Exp.InvSubOne
import TauCeti.NumberTheory.LSeries.HurwitzZeta.MellinKernel

/-!
# Mellin integral representation of the Riemann zeta function

Evaluates the Mellin–Laplace integral `∫₀^∞ t^{s−1}/(e^t − 1) dt = Γ(s) ζ(s)` for `1 < Re s`
(DLMF 25.5.1) by specializing
`TauCeti.integral_hurwitzMellinIntegrand_eq_Gamma_mul_complexHurwitzSeries` at `c = 1`, together
with the `s = 2` specialization `∫₀^∞ t/(e^t − 1) dt = π²/6`.

## Main results

* `TauCeti.integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta`:
  `∫₀^∞ t^{s−1}/(e^t − 1) dt = Γ(s) ζ(s)` for `1 < Re s`.
* `TauCeti.integral_Ioi_div_exp_sub_one_eq_pi_sq_div_six`: `∫₀^∞ t/(e^t − 1) dt = π²/6`.
-/

public section

noncomputable section

open Complex MeasureTheory Set

namespace TauCeti

/-- **DLMF 25.5.1**: `∫₀^∞ t^{s−1}/(e^t − 1) dt = Γ(s) ζ(s)` for `1 < Re s`. -/
theorem integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) / (cexp t - 1) = Gamma s * riemannZeta s := by
  have h := integral_hurwitzMellinIntegrand_eq_Gamma_mul_complexHurwitzSeries hs
    (by norm_num : 0 < (1 : ℂ).re)
  rw [complexHurwitzSeries_one hs] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [neg_one_mul, Complex.exp_neg_div_one_sub_exp_neg, div_eq_mul_inv]

/-- DLMF 8.22.3 at `s = 2`: `∫₀^∞ t/(e^t − 1) dt = π²/6`. -/
theorem integral_Ioi_div_exp_sub_one_eq_pi_sq_div_six :
    ∫ t in Ioi (0 : ℝ), t / (Real.exp t - 1) = Real.pi ^ 2 / 6 := by
  have h := integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta (s := 2) (by norm_num)
  rw [Complex.Gamma_ofNat_eq_factorial, riemannZeta_two, Nat.factorial_one,
    Nat.cast_one, one_mul] at h
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  push_cast
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  norm_num

end TauCeti

end
