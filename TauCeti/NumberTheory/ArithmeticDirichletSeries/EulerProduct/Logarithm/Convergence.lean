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
# Convergence of logarithmic-derivative series

The formal logarithmic derivative of a local Euler factor converges as far as the local power
series is zero-free. This removes the independent coefficient-summability hypothesis from the
evaluation theorem when zero-freeness is known on a disk. Combining the local result over all
height-one primes gives the prime-power expansion of the global logarithmic derivative.

For a height-one prime `P`, absolute convergence at a real parameter `σ` gives convergence of the
local power series on the disk of radius `N(P)⁻σ`. If that disk contains no zero, the formal
logarithmic derivative converges at `N(P) ^ (-s)` for every `s` with `σ < Re(s)`.

## Main results

* `TauCeti.EulerProductData.summable_coeff_localLogDerivSeries_of_zeroFree`: convergence of the
  formal local logarithmic derivative in a zero-free disk.
* `logDeriv_eulerFactor_eq_neg_log_mul_tsum_coeff_localLogDerivSeries_of_zeroFree`:
  evaluation of the formal series without a separate summability hypothesis.
* `TauCeti.EulerProductData.hasSum_tsum_coeff_localLogDerivSeries_of_zeroFree`: the global
  prime-power expansion under uniform local zero-free disks.
* `TauCeti.EulerProductData.exists_logarithm_hasSum_localLogDerivSeries`: a holomorphic logarithm
  whose derivative is given by the global prime-power expansion.

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
    exact D.norm_absNorm_cpow_neg_le_radius_localPowerSeries P
      (LSeriesSummable_of_abscissaOfAbsConv_lt_re (s := (σ : ℂ)) (by simpa using hσ))
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

/-- A local Euler factor is nonzero at `s` if the corresponding local power series is zero-free
on the disk bounded by the real parameter `σ`, and `σ < Re(s)`. -/
theorem eulerFactor_ne_zero_of_zeroFree (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) {σ : ℝ} {s : ℂ}
    (hne : ∀ z : ℂ,
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    D.eulerFactor P s ≠ 0 := by
  apply D.eulerFactor_ne_zero_of_localPowerSeries_ne_zero P
  apply hne
  simp only [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt
    (NumberField.HeightOneSpectrum.one_lt_absNorm P))]
  exact Real.rpow_lt_rpow_of_exponent_lt (by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P) (by simp; linarith)

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
    (hσ.trans (by exact_mod_cast hs)) (D.eulerFactor_ne_zero_of_zeroFree P hne hs)
    (D.summable_coeff_localLogDerivSeries_of_zeroFree P hσ hne hs)

/-- **The global logarithmic derivative expanded over prime powers.** Suppose `σ` lies strictly
to the right of the ideal-indexed abscissa of absolute convergence and every local power series
is zero-free on the disk of radius `N(P)⁻σ`. For `Re(s) > σ`, the local formal logarithmic
derivatives then converge, and their prime-indexed sum is the logarithmic derivative of the
global `L`-series. -/
theorem hasSum_tsum_coeff_localLogDerivSeries_of_zeroFree (D : EulerProductData K)
    {σ : ℝ} {s : ℂ}
    (hσ : idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < σ)
    (hne : ∀ (P : HeightOneSpectrum (𝓞 K)) (z : ℂ),
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    HasSum (fun P : HeightOneSpectrum (𝓞 K) ↦
        -Complex.log (Ideal.absNorm P.asIdeal : ℂ) *
          ∑' e : ℕ, PowerSeries.coeff e (D.localLogDerivSeries P) *
            ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e)
      (logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) s) := by
  refine D.hasSum_tsum_coeff_localLogDerivSeries
    (hσ.trans (by exact_mod_cast hs))
    (fun P ↦ D.eulerFactor_ne_zero_of_zeroFree P (hne P) hs)
    (fun P ↦ D.summable_coeff_localLogDerivSeries_of_zeroFree P
      ((D.abscissaOfAbsConv_localArithmeticFactor_le P).trans_lt hσ) (hne P) hs)

/-- The `tsum` form of
`TauCeti.EulerProductData.hasSum_tsum_coeff_localLogDerivSeries_of_zeroFree`. -/
theorem logDeriv_LSeries_eq_tsum_tsum_coeff_localLogDerivSeries_of_zeroFree
    (D : EulerProductData K) {σ : ℝ} {s : ℂ}
    (hσ : idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < σ)
    (hne : ∀ (P : HeightOneSpectrum (𝓞 K)) (z : ℂ),
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0)
    (hs : σ < s.re) :
    logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) s =
      ∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (Ideal.absNorm P.asIdeal : ℂ) *
          ∑' e : ℕ, PowerSeries.coeff e (D.localLogDerivSeries P) *
            ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e :=
  (D.hasSum_tsum_coeff_localLogDerivSeries_of_zeroFree hσ hne hs).tsum_eq.symm

/-- **A holomorphic logarithm with its derivative expanded over prime powers.** On a simply
connected open set contained in `Re(s) > σ`, the `L`-series has a holomorphic logarithm, and the
derivative of that branch is the global sum of the local formal logarithmic-derivative series.
The local zero-free disk hypothesis is what makes each formal series converge throughout the
region. -/
theorem exists_logarithm_hasSum_localLogDerivSeries (D : EulerProductData K)
    {U : Set ℂ} {σ : ℝ} (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    (hσ : idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < σ)
    (hU : ∀ s ∈ U, σ < s.re)
    (hne : ∀ (P : HeightOneSpectrum (𝓞 K)) (z : ℂ),
      ‖z‖ < ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ →
        FormalMultilinearSeries.ofScalarsSum (E := ℂ)
          (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P)) z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧
      Set.EqOn (Complex.exp ∘ L) (LSeries (normCoeff K D.toIdealArithmeticFunction)) U ∧
      ∀ s ∈ U, HasSum (fun P : HeightOneSpectrum (𝓞 K) ↦
          -Complex.log (Ideal.absNorm P.asIdeal : ℂ) *
            ∑' e : ℕ, PowerSeries.coeff e (D.localLogDerivSeries P) *
              ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) (deriv L s) := by
  have hconv : ∀ s ∈ U, Summable (idealTerm K D.toIdealArithmeticFunction s) := fun s hs ↦
    summable_idealTerm_of_idealAbscissaOfAbsConv_lt_re K
      (hσ.trans (by exact_mod_cast hU s hs))
  have hlocal : ∀ s ∈ U, ∀ P : HeightOneSpectrum (𝓞 K), D.eulerFactor P s ≠ 0 :=
    fun s hs P ↦ D.eulerFactor_ne_zero_of_zeroFree P (hne P) (hU s hs)
  obtain ⟨L, hLd, hLexp, hLderiv⟩ :=
    D.exists_differentiableOn_exp_eq_LSeries hUc hUo hconv hlocal
  refine ⟨L, hLd, hLexp, fun s hs ↦ ?_⟩
  rw [hLderiv s hs]
  exact D.hasSum_tsum_coeff_localLogDerivSeries_of_zeroFree hσ hne (hU s hs)

end TauCeti.EulerProductData
