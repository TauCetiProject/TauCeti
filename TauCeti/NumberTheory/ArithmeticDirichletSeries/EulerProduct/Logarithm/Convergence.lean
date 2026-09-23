/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowerSeries.Log.Deriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Eval
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic

/-!
# Convergence of local logarithmic-derivative series

The formal logarithmic derivative of a local Euler factor converges as far as the local power
series is zero-free. This removes the independent coefficient-summability hypothesis from the
evaluation theorem when zero-freeness is known on a disk.

For a height-one prime `P`, absolute convergence at a real parameter `σ` gives convergence of the
local power series on the disk of radius `N(P)⁻σ`. If that disk contains no zero, the formal
logarithmic derivative converges at `N(P) ^ (-s)` for every `s` with `σ < Re(s)`.

## Main results

* `TauCeti.EulerProductData.summable_coeff_localLogDerivSeries_of_zeroFree`: convergence of the
  formal local logarithmic derivative in a zero-free disk.
* `logDeriv_eulerFactor_eq_neg_log_mul_tsum_coeff_localLogDerivSeries_of_zeroFree`:
  evaluation of the formal series without a separate summability hypothesis.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti.EulerProductData

open Complex IsDedekindDomain
open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Convergence of a local formal logarithmic derivative on a zero-free disk.** Suppose the
local factor at `P` converges absolutely at the real point `σ`, and its power series has no zero
in the disk of radius `‖N(P) ^ (-σ)‖`. Then its formal logarithmic derivative converges at
`N(P) ^ (-s)` whenever `σ < Re(s)`. -/
theorem summable_coeff_localLogDerivSeries_of_zeroFree (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ} {s : ℂ}
    (hσ : LSeries.abscissaOfAbsConv (D.localArithmeticFactor P) < σ)
    (hne : ∀ z : ℂ,
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    Summable fun e : ℕ ↦
      PowerSeries.coeff e (D.localLogDerivSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e := by
  let r : NNReal := ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖₊
  -- The canonical local-factor radius bound supplies the analytic disk.
  have hr : (r : ENNReal) ≤
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦
        PowerSeries.coeff n (D.localPowerSeries P)).radius := by
    exact D.norm_absNorm_cpow_neg_le_radius_localPowerSeries P hσ
  have hz : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ₑ < (r : ENNReal) := by
    rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe]
    dsimp [r]
    exact NNReal.coe_lt_coe.mp (by simpa only [coe_nnnorm] using
      norm_absNorm_cpow_neg_lt_of_re_gt P hs)
  -- Zero-freeness lets the analytic logarithmic derivative inherit that radius.
  have hlog := PowerSeries.summable_coeff_logDeriv_mul_pow_of_zeroFree
    (D.localPowerSeries P) (D.constantCoeff_localPowerSeries P) hr
    (fun z hz' ↦ hne z (by
      rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe] at hz'
      dsimp [r] at hz'
      exact_mod_cast hz')) hz
  -- Multiplication by `X` shifts the formal logarithmic derivative by one degree.
  rw [← summable_nat_add_iff 1]
  refine (hlog.mul_left ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s))).congr fun e ↦ ?_
  rw [D.localLogDerivSeries_def, PowerSeries.coeff_succ_X_mul, pow_succ']
  ring

/-- The evaluation of a local formal logarithmic derivative inside a zero-free disk. This is
`logDeriv_eulerFactor_eq_neg_log_mul_tsum_coeff_localLogDerivSeries` with coefficient convergence
deduced from zero-freeness. -/
theorem logDeriv_eulerFactor_eq_neg_log_mul_tsum_coeff_localLogDerivSeries_of_zeroFree
    (D : EulerProductData K) (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ} {s : ℂ}
    (hσ : LSeries.abscissaOfAbsConv (D.localArithmeticFactor P) < σ)
    (hne : ∀ z : ℂ,
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    logDeriv (D.eulerFactor P) s =
      -Complex.log (Ideal.absNorm P.asIdeal : ℂ) *
        ∑' e : ℕ, PowerSeries.coeff e (D.localLogDerivSeries P) *
          ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e := by
  exact D.logDeriv_eulerFactor_eq_neg_log_mul_tsum_coeff_localLogDerivSeries P
    (hσ.trans (by exact_mod_cast hs))
    (by
      have hzero := hne ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s))
      have hlt := norm_absNorm_cpow_neg_lt_of_re_gt P hs
      rw [← D.ofScalarsSum_localPowerSeries_eq_eulerFactor P s]
      exact hzero hlt)
    (D.summable_coeff_localLogDerivSeries_of_zeroFree P hσ hne hs)

end TauCeti.EulerProductData
