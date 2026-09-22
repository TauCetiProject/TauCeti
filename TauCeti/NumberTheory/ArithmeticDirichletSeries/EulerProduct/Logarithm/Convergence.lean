/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PowerSeries.LogDeriv
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Eval

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
  let q : ℂ := (Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))
  let r : NNReal := ‖q‖₊
  -- Absolute convergence of the local Dirichlet series supplies the analytic radius.
  have hlocal : Summable fun e : ℕ ↦
      D (P.primeIdealPow e) * q ^ e := by
    have hsum := LSeriesSummable_of_abscissaOfAbsConv_lt_re (s := (σ : ℂ)) (by simpa using hσ)
    rw [LSeriesSummable] at hsum
    have hsum' := hsum.comp_injective <|
      Nat.pow_right_injective (NumberField.HeightOneSpectrum.one_lt_absNorm P)
    refine hsum'.congr fun e ↦ ?_
    simp only [Function.comp_apply]
    rw [LSeries.term_of_ne_zero (pow_ne_zero e <| Nat.ne_of_gt <|
        (Nat.zero_lt_one.trans <| NumberField.HeightOneSpectrum.one_lt_absNorm P)),
      D.localArithmeticFactor_apply_pow]
    dsimp [q]
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul,
      Complex.cpow_neg]
    ring
  have hcoeff : Summable fun e : ℕ ↦
      ‖PowerSeries.coeff e (D.localPowerSeries P)‖ * (r : ℝ) ^ e := by
    refine hlocal.norm.congr fun e ↦ ?_
    rw [D.coeff_localPowerSeries, norm_mul, norm_pow]
    rfl
  have hr : (r : ENNReal) ≤
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦
        PowerSeries.coeff n (D.localPowerSeries P)).radius := by
    apply FormalMultilinearSeries.le_radius_of_summable
    simpa [FormalMultilinearSeries.ofScalars_norm] using hcoeff
  have hq0 : q ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl P.natCast_absNorm_ne_zero)
  have hr0 : 0 < (r : ENNReal) := by simp [r, hq0]
  have hz : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ₑ < (r : ENNReal) := by
    rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe]
    -- Unfold the named boundary point to compare the two complex powers by real part.
    change ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ < ‖q‖
    dsimp [q]
    rw [Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt
      (NumberField.HeightOneSpectrum.one_lt_absNorm P)),
      Complex.norm_natCast_cpow_of_pos (Nat.zero_lt_of_lt
        (NumberField.HeightOneSpectrum.one_lt_absNorm P))]
    exact Real.rpow_lt_rpow_of_exponent_lt (by
      exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P) (by simp; linarith)
  -- Zero-freeness lets the analytic logarithmic derivative inherit that radius.
  have hlog := PowerSeries.summable_coeff_logDeriv_mul_pow_of_zeroFree
    (D.localPowerSeries P) (D.constantCoeff_localPowerSeries P) hr0 hr
    (fun z hz' ↦ hne z (by
      rw [enorm_eq_nnnorm, ENNReal.coe_lt_coe] at hz'
      dsimp [r, q] at hz'
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
      have hP0 := Nat.zero_lt_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm P)
      have hlt : ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ <
          ‖(Ideal.absNorm P.asIdeal : ℂ) ^ (-(σ : ℂ))‖ := by
        simp only [Complex.norm_natCast_cpow_of_pos hP0]
        exact Real.rpow_lt_rpow_of_exponent_lt (by
          exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P) (by simp; linarith)
      have heval :
          FormalMultilinearSeries.ofScalarsSum (E := ℂ)
              (fun n ↦ PowerSeries.coeff n (D.localPowerSeries P))
              ((Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) = D.eulerFactor P s := by
        rw [FormalMultilinearSeries.ofScalars_sum_eq, D.eulerFactor_eq_tsum]
        exact tsum_congr fun e ↦ by
          rw [D.coeff_localPowerSeries]
          exact (IdealArithmeticFunction.idealTerm_primeIdealPow_eq_mul_cpow_neg
            D.toIdealArithmeticFunction P s e).symm
      rw [← heval]
      exact hzero hlt)
    (D.summable_coeff_localLogDerivSeries_of_zeroFree P hσ hne hs)

end TauCeti.EulerProductData
