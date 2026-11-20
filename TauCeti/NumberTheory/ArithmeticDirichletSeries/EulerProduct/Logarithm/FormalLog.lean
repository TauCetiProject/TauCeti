/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowerSeries.Log.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Analytic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Eval

/-!
# Evaluating the logarithm of a local Euler factor

The formal series `TauCeti.EulerProductData.localLogSeries` is the logarithm of a local Euler
factor before evaluation. This file supplies the analytic bridge. If the analytic sum of the
local power series at a height-one prime has no zero on the disk of radius `N(P) ^ (-σ)`, then its
formal logarithm converges absolutely at every smaller prime-norm parameter. No separate convergence
hypothesis is needed, since the analytic sum is `0` wherever the local power series diverges.
Exponentiating the resulting prime-power sum recovers the local Euler factor.

The zero-free hypothesis is essential: a zero of the local power series bounds the convergence
radius of its logarithm even when the local power series itself converges farther.

## Main results

* `TauCeti.EulerProductData.summable_norm_coeff_localLogSeries_of_zeroFree`: absolute convergence
  of the evaluated local formal logarithm.
* `TauCeti.EulerProductData.exp_tsum_coeff_localLogSeries_eq_eulerFactor_of_zeroFree`: the
  evaluated series is a logarithm of the local Euler factor.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti.EulerProductData

open Complex IsDedekindDomain
open scoped nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The evaluated formal logarithm of a local Euler factor converges absolutely at `N(P) ^ (-s)`
whenever `σ < Re(s)` and the local power series has no zero in the disk of radius `N(P) ^ (-σ)`. -/
theorem summable_norm_coeff_localLogSeries_of_zeroFree (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ} {s : ℂ}
    (hne : ∀ z : ℂ,
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    Summable fun e : ℕ ↦ ‖PowerSeries.coeff e (D.localLogSeries P) *
      ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e‖ := by
  rw [D.localLogSeries_def]
  exact PowerSeries.summable_norm_coeff_logOf_mul_pow_of_zeroFree
    (D.localPowerSeries P) (D.constantCoeff_localPowerSeries P)
    (r := ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ₑ)
    (fun z hz ↦ hne z ((lt_iff_lt_of_le_iff_le eNorm_le_iff_norm_le).1 hz))
    ((lt_iff_lt_of_le_iff_le eNorm_le_iff_norm_le).2
      (P.norm_absNorm_cpow_neg_lt (by simpa using hs)))

/-- **The local prime-power logarithm evaluates to a logarithm of the Euler factor.** Under the
same zero-free-disk hypothesis, exponentiating the sum of the formal logarithmic coefficients at
`N(P) ^ (-s)` recovers the analytic local Euler factor at `s`. Apply this theorem with a chosen
`σ`; the left-hand side does not determine it for simplification. -/
theorem exp_tsum_coeff_localLogSeries_eq_eulerFactor_of_zeroFree
    (D : EulerProductData K) (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ} {s : ℂ}
    (hne : ∀ z : ℂ,
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    Complex.exp (∑' e : ℕ, PowerSeries.coeff e (D.localLogSeries P) *
      ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) = D.eulerFactor P s := by
  rw [D.localLogSeries_def]
  calc
    Complex.exp (∑' e : ℕ, PowerSeries.coeff e (PowerSeries.logOf
        (D.localPowerSeries P)) * ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) =
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P))
            ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) := by
      exact PowerSeries.exp_tsum_coeff_logOf_mul_pow_of_zeroFree
        (D.localPowerSeries P) (D.constantCoeff_localPowerSeries P)
        (r := ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ₑ)
        (fun z hz ↦ hne z ((lt_iff_lt_of_le_iff_le eNorm_le_iff_norm_le).1 hz))
        ((lt_iff_lt_of_le_iff_le eNorm_le_iff_norm_le).2
          (P.norm_absNorm_cpow_neg_lt (by simpa using hs)))
    _ = D.eulerFactor P s := by
      simpa only [D.coeff_localPowerSeries] using D.localPowerSeries_eval_eq_eulerFactor P s

end TauCeti.EulerProductData
