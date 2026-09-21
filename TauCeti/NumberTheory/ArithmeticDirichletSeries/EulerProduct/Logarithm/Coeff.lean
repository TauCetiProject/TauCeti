/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Data
public import TauCeti.RingTheory.PowerSeries.Log

/-!
# Formal logarithmic-derivative coefficients of an ideal Euler product

An `EulerProductData K` has at every height-one prime `P` a canonical local power series

`F_P(X) = ∑ e, D(P ^ e) X ^ e`.

Its formal logarithm `log F_P` packages the general prime-power logarithmic expansion, including
coefficient systems whose values at higher prime powers are independent. The series

`X * F_P'(X) / F_P(X)`

then packages the local coefficients of the negative analytic logarithmic derivative: after
substituting `X = N(P) ^ (-s)`, its coefficient in degree `e` is multiplied by `log N(P)`.

The identity `(X F_P'/F_P) F_P = X F_P'` gives a finite recurrence for every coefficient. In
degrees one and two the coefficients are respectively
`D(P)` and `2 D(P ^ 2) - D(P) ^ 2`. For completely multiplicative degree-one data this reduces to
the familiar geometric family `χ(P) ^ e`, so the general construction agrees with the existing
prime-power logarithmic derivative rather than defining a parallel specialization.

These are formal identities: evaluating the logarithm series and differentiating it termwise are
separate analytic questions requiring convergence hypotheses.

## Main definitions

* `TauCeti.EulerProductData.localLogSeries`: the formal logarithm of a local Euler factor.
* `TauCeti.EulerProductData.localLogDerivSeries`: the series `X F_P'/F_P`.

## Main results

* `TauCeti.EulerProductData.sum_antidiagonal_coeff_localLogDerivSeries_eq`: the coefficient
  recurrence determining the local logarithmic derivative.
* `TauCeti.EulerProductData.coeff_localLogDerivSeries_ofMultiplicativeIdealWeight`: the
  specialization to completely multiplicative weights.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

public section

namespace TauCeti

open IsDedekindDomain
open scoped NumberField nonZeroDivisors

namespace EulerProductData

variable {K : Type*} [Field K] [NumberField K]

/-- The formal logarithm of the local power series of `D` at `P`. Its constant coefficient is
zero because coprime multiplicativity fixes the constant coefficient of the local series to be
one. -/
noncomputable def localLogSeries (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) : PowerSeries ℂ :=
  PowerSeries.logOf (D.localPowerSeries P)

/-- The local logarithm is the formal logarithm of the local power series. -/
theorem localLogSeries_def (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    D.localLogSeries P = PowerSeries.logOf (D.localPowerSeries P) := by
  rw [localLogSeries]

/-- The local **formal logarithmic-derivative series** `X F_P'(X) / F_P(X)`. The factor `X`
aligns degree `e` with the prime power `P ^ e`; after substituting `X = N(P) ^ (-s)`, these are
the coefficients of the negative analytic logarithmic derivative before multiplication by
`log N(P)`. -/
noncomputable def localLogDerivSeries (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) : PowerSeries ℂ :=
  PowerSeries.X * PowerSeries.logDeriv (D.localPowerSeries P)

/-- The local logarithmic-derivative series is `X` times the formal logarithmic derivative of
the local power series. -/
theorem localLogDerivSeries_def (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    D.localLogDerivSeries P =
      PowerSeries.X * PowerSeries.logDeriv (D.localPowerSeries P) := by
  rw [localLogDerivSeries]

/-- The formal local logarithm has zero constant coefficient. -/
@[simp]
theorem constantCoeff_localLogSeries (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    PowerSeries.constantCoeff (D.localLogSeries P) = 0 := by
  exact PowerSeries.constantCoeff_logOf (D.constantCoeff_localPowerSeries P)

/-- The degree-zero logarithmic-derivative coefficient vanishes. -/
@[simp]
theorem coeff_zero_localLogDerivSeries (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    PowerSeries.coeff 0 (D.localLogDerivSeries P) = 0 := by
  simp [localLogDerivSeries]

/-- The coefficient in positive degree of `X (log F_P)'` is the degree times the corresponding
coefficient of `log F_P`. -/
theorem coeff_succ_localLogDerivSeries (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    PowerSeries.coeff (n + 1) (D.localLogDerivSeries P) =
      (n + 1 : ℂ) * PowerSeries.coeff (n + 1) (D.localLogSeries P) := by
  rw [localLogDerivSeries, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_logDeriv,
    localLogSeries]
  ring

/-- The local logarithmic derivative is characterized by
`(X F_P'/F_P) * F_P = X F_P'`. -/
theorem localLogDerivSeries_mul_localPowerSeries (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    D.localLogDerivSeries P * D.localPowerSeries P =
      PowerSeries.X * PowerSeries.derivative ℂ (D.localPowerSeries P) := by
  rw [localLogDerivSeries, mul_assoc,
    PowerSeries.logDeriv_mul _ (D.constantCoeff_localPowerSeries P)]

/-- **The local logarithmic-derivative recurrence.** If `b e` is the coefficient of
`X F_P'/F_P` in degree `e`, then

`sum_(i+j=n) b i * D(P ^ j) = n * D(P ^ n)`.

Because `b 0 = 0` and `D(P ^ 0) = 1`, this determines `b n` from the preceding coefficients and
the prime-power data through degree `n`. -/
theorem sum_antidiagonal_coeff_localLogDerivSeries_eq (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ∑ ij ∈ Finset.antidiagonal n,
        PowerSeries.coeff ij.1 (D.localLogDerivSeries P) * D (P.primeIdealPow ij.2) =
      (n : ℂ) * D (P.primeIdealPow n) := by
  have h := congrArg (PowerSeries.coeff n)
    (D.localLogDerivSeries_mul_localPowerSeries P)
  rw [PowerSeries.coeff_mul] at h
  simp only [D.coeff_localPowerSeries] at h
  cases n with
  | zero => simpa only [PowerSeries.coeff_zero_X_mul, Nat.cast_zero, zero_mul] using h
  | succ n =>
      rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative] at h
      simpa [Nat.cast_add, Nat.cast_one, mul_comm] using h

/-- The first local logarithmic-derivative coefficient is the coefficient at `P`. -/
@[simp]
theorem coeff_one_localLogDerivSeries (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    PowerSeries.coeff 1 (D.localLogDerivSeries P) = D (P.primeIdealPow 1) := by
  have h := D.sum_antidiagonal_coeff_localLogDerivSeries_eq P 1
  norm_num [Finset.antidiagonal] at h
  simpa using h

/-- The second local logarithmic-derivative coefficient records the first genuinely independent
prime-power datum: it is `2 D(P ^ 2) - D(P) ^ 2`. -/
@[simp]
theorem coeff_two_localLogDerivSeries (D : EulerProductData K)
    (P : HeightOneSpectrum (𝓞 K)) :
    PowerSeries.coeff 2 (D.localLogDerivSeries P) =
      2 * D (P.primeIdealPow 2) - D (P.primeIdealPow 1) ^ 2 := by
  have h := D.sum_antidiagonal_coeff_localLogDerivSeries_eq P 2
  norm_num [Finset.antidiagonal] at h ⊢
  linear_combination h

/-- The local power series of completely multiplicative data is the geometric series with
degree-`n` coefficient `χ(P) ^ n`. -/
theorem localPowerSeries_ofMultiplicativeIdealWeight (χ : MultiplicativeIdealWeight K)
    (P : HeightOneSpectrum (𝓞 K)) :
    (ofMultiplicativeIdealWeight χ).localPowerSeries P =
      PowerSeries.mk fun n ↦ χ P.asIdeal ^ n := by
  ext n
  rw [coeff_localPowerSeries, PowerSeries.coeff_mk, ofMultiplicativeIdealWeight_apply]
  have hpow : P.primeIdealPow n =
      (⟨P.asIdeal, mem_nonZeroDivisors_of_ne_zero P.ne_bot⟩ : (Ideal (𝓞 K))⁰) ^ n := by
    apply Subtype.ext
    simp [HeightOneSpectrum.coe_primeIdealPow]
  rw [hpow]
  simp

/-- For completely multiplicative data, the local formal logarithmic derivative is the geometric
family `X * χ(P) * F_P(X)`. -/
theorem localLogDerivSeries_ofMultiplicativeIdealWeight
    (χ : MultiplicativeIdealWeight K) (P : HeightOneSpectrum (𝓞 K)) :
    (ofMultiplicativeIdealWeight χ).localLogDerivSeries P =
      PowerSeries.X * PowerSeries.C (χ P.asIdeal) *
        (ofMultiplicativeIdealWeight χ).localPowerSeries P := by
  let D := ofMultiplicativeIdealWeight χ
  let F := D.localPowerSeries P
  let a := χ P.asIdeal
  have hF : F = PowerSeries.mk fun n ↦ a ^ n := by
    simpa [D, F, a] using localPowerSeries_ofMultiplicativeIdealWeight χ P
  have hgeom : F * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
    have h := congrArg (PowerSeries.rescale a)
      (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
    simp only [map_mul, map_sub, map_one, PowerSeries.rescale_mk, Pi.one_apply, mul_one,
      PowerSeries.rescale_X] at h
    simpa [hF] using h
  have hderiv : PowerSeries.derivative ℂ F = PowerSeries.C a * F ^ 2 := by
    have h := congrArg (PowerSeries.derivative ℂ) hgeom
    simp only [PowerSeries.derivative_one, Derivation.leibniz, map_sub,
      PowerSeries.derivative_C, PowerSeries.derivative_X, smul_eq_mul] at h
    have h' : (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.derivative ℂ F =
        PowerSeries.C a * F := by
      linear_combination h
    calc
      PowerSeries.derivative ℂ F =
          (F * (1 - PowerSeries.C a * PowerSeries.X)) * PowerSeries.derivative ℂ F := by
            rw [hgeom, one_mul]
      _ = F * ((1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.derivative ℂ F) := by
        ring
      _ = PowerSeries.C a * F ^ 2 := by rw [h']; ring
  have hunit : IsUnit F := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hF]; simp)
  apply hunit.mul_right_cancel
  rw [D.localLogDerivSeries_mul_localPowerSeries P]
  simp only [F, D] at hderiv ⊢
  rw [hderiv]
  ring

/-- The degree-`n` local logarithmic-derivative coefficient of a completely multiplicative
weight is `χ(P) ^ n` for `n > 0`, and zero in degree zero. -/
@[simp]
theorem coeff_localLogDerivSeries_ofMultiplicativeIdealWeight
    (χ : MultiplicativeIdealWeight K) (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    PowerSeries.coeff n ((ofMultiplicativeIdealWeight χ).localLogDerivSeries P) =
      if n = 0 then 0 else χ P.asIdeal ^ n := by
  rw [localLogDerivSeries_ofMultiplicativeIdealWeight]
  cases n with
  | zero => simp
  | succ n =>
      rw [mul_assoc, PowerSeries.coeff_succ_X_mul]
      rw [PowerSeries.coeff_C_mul, coeff_localPowerSeries]
      simp only [ofMultiplicativeIdealWeight_apply, HeightOneSpectrum.coe_primeIdealPow, map_pow]
      exact (pow_succ' (χ P.asIdeal) n).symm

end EulerProductData

end TauCeti
