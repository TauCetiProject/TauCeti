/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Coeff
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.LogDeriv

import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Evaluating logarithmic-derivative coefficients of ideal Euler factors

For a general ideal Euler product, the formal series
`TauCeti.EulerProductData.localLogDerivSeries` records the prime-power coefficients of the
logarithmic derivative of each local factor. This file evaluates those formal coefficients at
`N(P) ^ (-s)` and identifies their sum with the analytic logarithmic derivative at `s`.

Two hypotheses are visible in the result. The coefficient series must converge at the evaluation
point, and the local Euler factor must be nonzero there. These cannot be replaced by convergence of
the local factor itself: a convergent power series can have a zero closer to the origin than the
point being evaluated, in which case its formal logarithmic derivative does not converge at that
point.

The local identity is also combined with the prime-indexed logarithmic-derivative sum. Thus, once
coefficient convergence is known at every prime, the logarithmic derivative of the global
`L`-series is the sum of the evaluated local formal series.

## Main results

* `TauCeti.EulerProductData.localPowerSeries_eval_eq_eulerFactor`: evaluation of the local power
  series at `N(P) ^ (-s)`.
* `TauCeti.EulerProductData.logDeriv_eulerFactor_eq_neg_log_mul_tsum_coeff_localLogDerivSeries`:
  evaluation of one local formal logarithmic derivative.
* `TauCeti.EulerProductData.hasSum_tsum_coeff_localLogDerivSeries`: the corresponding expansion of
  the logarithmic derivative of the global `L`-series.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti

open Complex IsDedekindDomain

open scoped nonZeroDivisors NumberField

namespace EulerProductData

open IdealArithmeticFunction

variable {K : Type*} [Field K] [NumberField K]

/-- Evaluating the local power series at `N(P) ^ (-s)` gives the local Euler factor at `s`. -/
@[simp]
theorem localPowerSeries_eval_eq_eulerFactor (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    FormalMultilinearSeries.ofScalarsSum (E := ℂ)
        (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P))
          ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) =
      D.eulerFactor P s := by
  rw [FormalMultilinearSeries.ofScalars_sum_eq, D.eulerFactor_eq_tsum]
  exact tsum_congr fun e ↦ by
    rw [D.coeff_localPowerSeries]
    exact (IdealArithmeticFunction.idealTerm_primeIdealPow_eq_mul_cpow_neg
      D.toIdealArithmeticFunction P s e).symm

/-- A local Euler factor is nonzero at `s` if the corresponding local power series is nonzero at
`N(P) ^ (-s)`. -/
theorem eulerFactor_ne_zero_of_localPowerSeries_ne_zero (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hne : FormalMultilinearSeries.ofScalarsSum (E := ℂ)
      (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P))
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ≠ 0) :
    D.eulerFactor P s ≠ 0 := by
  simpa only [D.localPowerSeries_eval_eq_eulerFactor] using hne

/-- **Evaluation of a local formal logarithmic derivative.** If the coefficient series of
`X F_P'(X) / F_P(X)` converges at `X = N(P) ^ (-s)` and the local Euler factor does not vanish at
`s`, then the analytic logarithmic derivative is `-log N(P)` times that sum.

The explicit convergence hypothesis is necessary: convergence and nonvanishing of `F_P` at one
point do not imply convergence there of the Taylor series of `F_P'/F_P` about zero. -/
theorem logDeriv_eulerFactor_eq_neg_log_mul_tsum_coeff_localLogDerivSeries
    (D : EulerProductData K) (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : LSeries.abscissaOfAbsConv (D.localArithmeticFactor P) < s.re)
    (hne : D.eulerFactor P s ≠ 0)
    (hcoeff : Summable fun e : ℕ ↦
      PowerSeries.coeff e (D.localLogDerivSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) :
    logDeriv (D.eulerFactor P) s =
      -Complex.log (Ideal.absNorm P.asIdeal : ℂ) *
        ∑' e : ℕ, PowerSeries.coeff e (D.localLogDerivSeries P) *
          ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e := by
  let x : ℂ := (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)
  let b : ℕ → ℂ := fun e ↦ PowerSeries.coeff e (D.localLogDerivSeries P)
  let a : ℕ → ℂ := fun e ↦ D (P.primeIdealPow e)
  have hlocal : Summable fun e : ℕ ↦
      idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow e) := by
    have hsum := LSeriesSummable_of_abscissaOfAbsConv_lt_re hs
    rw [LSeriesSummable] at hsum
    have hsum' := hsum.comp_injective <|
      Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm P)
    refine hsum'.congr fun e ↦ ?_
    simp only [Function.comp_apply]
    rw [LSeries.term_of_ne_zero (pow_ne_zero e <| Nat.ne_of_gt <|
        (Nat.zero_lt_one.trans <| NumberField.HeightOneSpectrum.one_lt_absNorm P)),
      D.localArithmeticFactor_apply_pow, idealTerm_def, P.absNorm_primeIdealPow]
  have ha : Summable fun e : ℕ ↦ a e * x ^ e :=
    hlocal.congr fun e ↦
      idealTerm_primeIdealPow_eq_mul_cpow_neg D.toIdealArithmeticFunction P s e
  have hfactor : ∑' e : ℕ, a e * x ^ e = D.eulerFactor P s := by
    rw [D.eulerFactor_eq_tsum]
    exact tsum_congr fun e ↦
      (idealTerm_primeIdealPow_eq_mul_cpow_neg D.toIdealArithmeticFunction P s e).symm
  have hcauchy :
      (∑' e : ℕ, b e * x ^ e) * ∑' e : ℕ, a e * x ^ e =
        ∑' n : ℕ, ∑ ij ∈ Finset.antidiagonal n,
          (b ij.1 * x ^ ij.1) * (a ij.2 * x ^ ij.2) :=
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hcoeff.norm ha.norm
  have hinner (n : ℕ) :
      ∑ ij ∈ Finset.antidiagonal n, (b ij.1 * x ^ ij.1) * (a ij.2 * x ^ ij.2) =
        (n : ℂ) * a n * x ^ n := by
    calc
      _ = (∑ ij ∈ Finset.antidiagonal n, b ij.1 * a ij.2) * x ^ n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ij hij
        rw [Finset.mem_antidiagonal] at hij
        rw [← hij, pow_add]
        ring
      _ = (n : ℂ) * a n * x ^ n := by
        rw [D.sum_antidiagonal_coeff_localLogDerivSeries_eq P n]
  have hweighted : Summable fun n : ℕ ↦ (n : ℂ) * a n * x ^ n :=
    (summable_sum_mul_antidiagonal_of_summable_norm'
      hcoeff.norm hcoeff ha.norm ha).congr hinner
  have heval_mul :
      (∑' e : ℕ, b e * x ^ e) * D.eulerFactor P s =
        ∑' n : ℕ, (n : ℂ) * a n * x ^ n := by
    rw [← hfactor, hcauchy]
    exact tsum_congr hinner
  have hlog (n : ℕ) :
      Complex.log (Ideal.absNorm P.asIdeal : ℂ) * ((n : ℂ) * a n * x ^ n) =
        Complex.log (Ideal.absNorm (P.primeIdealPow n : Ideal (𝓞 K)) : ℂ) *
          idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow n) := by
    rw [idealTerm_primeIdealPow_eq_mul_cpow_neg]
    rw [P.absNorm_primeIdealPow, ← Complex.natCast_log, ← Complex.natCast_log]
    push_cast [Real.log_pow]
    ring
  have hlog_tsum :
      Complex.log (Ideal.absNorm P.asIdeal : ℂ) *
          (∑' n : ℕ, (n : ℂ) * a n * x ^ n) =
        ∑' n : ℕ,
          Complex.log (Ideal.absNorm (P.primeIdealPow n : Ideal (𝓞 K)) : ℂ) *
            idealTerm K D.toIdealArithmeticFunction s (P.primeIdealPow n) := by
    rw [← hweighted.tsum_mul_left]
    exact tsum_congr hlog
  rw [D.logDeriv_eulerFactor_eq P hs, ← hlog_tsum, ← heval_mul]
  field_simp
  ring

/-- **The logarithmic derivative of a general ideal Euler product, expanded in its local formal
coefficients.** If every local formal logarithmic-derivative series converges at
`N(P) ^ (-s)`, the global logarithmic derivative is the sum of their evaluations weighted by
`-log N(P)`. -/
theorem hasSum_tsum_coeff_localLogDerivSeries (D : EulerProductData K) {s : ℂ}
    (hs : idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < s.re)
    (hne : ∀ P : HeightOneSpectrum (𝓞 K), D.eulerFactor P s ≠ 0)
    (hcoeff : ∀ P : HeightOneSpectrum (𝓞 K), Summable fun e : ℕ ↦
      PowerSeries.coeff e (D.localLogDerivSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) :
    HasSum (fun P : HeightOneSpectrum (𝓞 K) ↦
        -Complex.log (Ideal.absNorm P.asIdeal : ℂ) *
          ∑' e : ℕ, PowerSeries.coeff e (D.localLogDerivSeries P) *
            ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e)
      (logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) s) := by
  refine HasSum.congr_fun (D.hasSum_logDeriv_eulerFactor hs hne) fun P ↦ ?_
  exact (D.logDeriv_eulerFactor_eq_neg_log_mul_tsum_coeff_localLogDerivSeries P
    ((D.abscissaOfAbsConv_localArithmeticFactor_le P).trans_lt hs) (hne P) (hcoeff P)).symm

/-- The `tsum` form of
`TauCeti.EulerProductData.hasSum_tsum_coeff_localLogDerivSeries`. -/
theorem logDeriv_LSeries_eq_tsum_tsum_coeff_localLogDerivSeries
    (D : EulerProductData K) {s : ℂ}
    (hs : idealAbscissaOfAbsConv K D.toIdealArithmeticFunction < s.re)
    (hne : ∀ P : HeightOneSpectrum (𝓞 K), D.eulerFactor P s ≠ 0)
    (hcoeff : ∀ P : HeightOneSpectrum (𝓞 K), Summable fun e : ℕ ↦
      PowerSeries.coeff e (D.localLogDerivSeries P) *
        ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e) :
    logDeriv (LSeries (normCoeff K D.toIdealArithmeticFunction)) s =
      ∑' P : HeightOneSpectrum (𝓞 K),
        -Complex.log (Ideal.absNorm P.asIdeal : ℂ) *
          ∑' e : ℕ, PowerSeries.coeff e (D.localLogDerivSeries P) *
            ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) ^ e :=
  (D.hasSum_tsum_coeff_localLogDerivSeries hs hne hcoeff).tsum_eq.symm

end EulerProductData

end TauCeti
