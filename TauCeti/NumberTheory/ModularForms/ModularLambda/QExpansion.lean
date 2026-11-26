/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ModularLambda.Basic
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
public import TauCeti.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.Analysis.Analytic.PowerSubstitution
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.SpecialFunctions.QPochhammer
import TauCeti.Combinatorics.Enumerative.Pentagonal.EulerFunction
import TauCeti.RingTheory.MvPowerSeries.Inverse

/-!
# The integral coordinate of the modular lambda function

The normalized modular function `λ / 16` has integral coefficients in the nome
`q = exp (π i τ)`. With `E(q) = ∏_{n ≥ 1} (1 - q^n)`, the normalized series is
`q (E(q) E(q⁴)² / E(q²)³)⁸`. Its linear coefficient is one, so this defines a strict
`FormalCoordinate ℤ`. The coordinate inverse represents `q` as a series in `λ / 16`,
and `FormalCoordinate.substAlgEquiv` gives the change of variables over any commutative
ring after base change.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), §1.1.3.
-/

public noncomputable section

open Complex Topology PowerSeries
open scoped UpperHalfPlane

namespace TauCeti.ModularForm

/-- The strict integral coordinate underlying the normalized modular lambda function. -/
def modularLambdaCoordinate : FormalCoordinate ℤ where
  toPowerSeries := X * (pentagonalSeries ℤ * ((pentagonalSeries ℤ).expand 4 (by decide)) ^ 2 *
    ((pentagonalSeries ℤ).expand 2 two_ne_zero).invOfUnit 1 ^ 3) ^ 8
  constantCoeff_toPowerSeries := by simp
  isUnit_coeff_one := by simp [constantCoeff_invOfUnit]

/-- The normalized series is the integral Euler quotient, expressed using the inverse of its
unit denominator. -/
theorem modularLambdaCoordinate_toPowerSeries :
    modularLambdaCoordinate.toPowerSeries = X *
      ((pentagonalSeries ℤ) * ((pentagonalSeries ℤ).expand 4 (by decide)) ^ 2 *
        ((pentagonalSeries ℤ).expand 2 two_ne_zero).invOfUnit 1 ^ 3) ^ 8 := by
  rw [modularLambdaCoordinate]

/-- The normalized modular lambda series has linear coefficient one. -/
@[simp]
theorem modularLambdaCoordinate_coeff_one :
    coeff 1 modularLambdaCoordinate.toPowerSeries = 1 := by
  simp [modularLambdaCoordinate_toPowerSeries, constantCoeff_invOfUnit]

/-- The quadratic coefficient of the normalized modular lambda series is `-8`. -/
@[simp]
theorem modularLambdaCoordinate_coeff_two :
    coeff 2 modularLambdaCoordinate.toPowerSeries = -8 := by
  let E := pentagonalSeries ℤ
  let E₂ := E.expand 2 two_ne_zero
  let E₄ := E.expand 4 (by decide)
  have h₀ : constantCoeff E = 1 := constantCoeff_pentagonalSeries ℤ
  have h₁ : coeff 1 E = -1 := by
    have hone : pentagonal 1 = 1 := by norm_num [pentagonal_def]
    simpa [hone, Int.coe_negOnePow] using coeff_pentagonalSeries_pentagonal ℤ 1
  have h₂ : coeff 1 E₂ = 0 := coeff_expand_of_not_dvd _ _ _ (by decide)
  have h₄ : coeff 1 E₄ = 0 := coeff_expand_of_not_dvd _ _ _ (by decide)
  have hi : coeff 1 (E₂.invOfUnit 1) = 0 := by
    have h := congrArg (coeff 1) (mul_invOfUnit (φ := E₂) (u := 1) (by simp [E₂, h₀]))
    rw [coeff_one_mul, h₂, zero_mul, zero_add] at h
    simpa [E₂, h₀] using h
  have hmain : modularLambdaCoordinate.toPowerSeries =
      X * (E * E₄ ^ 2 * (E₂.invOfUnit 1) ^ 3) ^ 8 :=
    modularLambdaCoordinate_toPowerSeries
  rw [hmain, coeff_succ_X_mul]
  norm_num [coeff_one_pow, coeff_one_mul, h₀, h₁, hi, h₄, E₄, constantCoeff_invOfUnit]

private theorem modularLambda_div_sixteen_eq_euler {τ : ℂ} (hτ : 0 < τ.im) :
    modularLambda τ / 16 = cexp (Real.pi * I * τ) *
      (eulerFunction (cexp (Real.pi * I * τ)) *
        eulerFunction (cexp (Real.pi * I * τ) ^ 4) ^ 2 *
        (eulerFunction (cexp (Real.pi * I * τ) ^ 2))⁻¹ ^ 3) ^ 8 := by
  rw [modularLambda_eq_mul_tprod hτ]
  set q := cexp (Real.pi * I * τ)
  have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_pi_I_lt_one hτ
  have hq₂ := norm_pow_lt_one hq two_ne_zero
  have hq₄ := norm_pow_lt_one hq₂ two_ne_zero
  have hne : eulerFunction (q ^ 2) ≠ 0 := by
    rw [eulerFunction_eq_tprod hq₂]
    exact tprod_one_sub_pow_ne_zero hq₂
  have hodd := tprod_one_sub_pow_eq_tprod_one_sub_pow_odd_mul hq
  rw [← eulerFunction_eq_tprod hq, ← eulerFunction_eq_tprod hq₂] at hodd
  have heven := tprod_one_add_pow_mul_tprod_one_sub_pow hq₂
  rw [← eulerFunction_eq_tprod hq₂, ← eulerFunction_eq_tprod hq₄] at heven
  have heven' : (∏' n : ℕ, (1 + q ^ (2 * n + 2))) =
      eulerFunction (q ^ 4) / eulerFunction (q ^ 2) := by
    simpa only [← pow_mul, mul_add, mul_one] using (eq_div_iff hne).2 heven
  rw [(eq_div_iff hne).2 hodd.symm, heven']
  ring

private def normalizedLambdaEuler : ℂ → ℂ :=
  (fun q ↦ q) * (eulerFunction * (fun q : ℂ ↦ eulerFunction (q ^ 4)) ^ 2 *
    (fun q : ℂ ↦ eulerFunction (q ^ 2))⁻¹ ^ 3) ^ 8

private theorem analyticAt_eulerFunction_comp_pow (k : ℕ) (hk : k ≠ 0) :
    AnalyticAt ℂ (fun q : ℂ ↦ eulerFunction (q ^ k)) 0 :=
  analyticAt_eulerFunction_zero.comp_of_eq (by fun_prop) (zero_pow hk)

private theorem analyticAt_normalizedLambdaEuler : AnalyticAt ℂ normalizedLambdaEuler 0 := by
  have h₂ := analyticAt_eulerFunction_comp_pow 2 two_ne_zero
  have h₄ := analyticAt_eulerFunction_comp_pow 4 (by decide)
  exact analyticAt_id.mul (((analyticAt_eulerFunction_zero.mul (h₄.pow 2)).mul
    ((h₂.inv (by simp)).pow 3)).pow 8)

private theorem cuspFunction_modularLambda_div_sixteen_eventuallyEq :
    UpperHalfPlane.cuspFunction 2 (fun τ : ℍ ↦ modularLambda τ / 16) =ᶠ[𝓝 0]
      normalizedLambdaEuler := by
  have hfun : (fun τ : ℍ ↦ modularLambda τ / 16) =
      fun τ : ℍ ↦ normalizedLambdaEuler (Function.Periodic.qParam 2 τ) := by
    funext τ
    rw [modularLambda_div_sixteen_eq_euler τ.im_pos]
    simp only [Periodic.exp_pi_I_mul_eq_qParam_two, normalizedLambdaEuler,
      Pi.mul_apply, Pi.pow_apply, Pi.inv_apply]
  rw [hfun]
  exact TauCeti.UpperHalfPlane.cuspFunction_comp_qParam_eventuallyEq (by norm_num)
    analyticAt_normalizedLambdaEuler.continuousAt

/-- The width-two cusp function of `λ / 16` is analytic at the origin. -/
theorem analyticAt_cuspFunction_modularLambda_div_sixteen :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 2 (fun τ : ℍ ↦ modularLambda τ / 16)) 0 :=
  analyticAt_normalizedLambdaEuler.congr cuspFunction_modularLambda_div_sixteen_eventuallyEq.symm

/-- The integral formal coordinate is the width-two `q`-expansion of `λ / 16`. -/
theorem modularLambdaCoordinate_map_eq_qExpansion :
    modularLambdaCoordinate.toPowerSeries.map (Int.castRingHom ℂ) =
      UpperHalfPlane.qExpansion 2 (fun τ : ℍ ↦ modularLambda τ / 16) := by
  have hE : AnalyticAt ℂ (eulerFunction : ℂ → ℂ) 0 := analyticAt_eulerFunction_zero
  have h₂ := analyticAt_eulerFunction_comp_pow 2 two_ne_zero
  have h₄ := analyticAt_eulerFunction_comp_pow 4 (by decide)
  have hne : eulerFunction ((0 : ℂ) ^ 2) ≠ 0 := by simp
  have hId : AnalyticAt ℂ (fun q : ℂ ↦ q) 0 := analyticAt_id
  have hInv := h₂.inv hne
  have hSquare := h₄.pow 2
  have hCube := hInv.pow 3
  have hNumerator := hE.mul hSquare
  have hProduct := hNumerator.mul hCube
  have hPower := hProduct.pow 8
  have hTaylor (k : ℕ) (hk : k ≠ 0) :
      taylorSeries (fun q : ℂ ↦ eulerFunction (q ^ k)) 0 = (pentagonalSeries ℂ).expand k hk := by
    rw [taylorSeries_comp_pow hE k hk, taylorSeries_eulerFunction]
  rw [TauCeti.UpperHalfPlane.qExpansion_eq_taylorSeries
    analyticAt_cuspFunction_modularLambda_div_sixteen,
    taylorSeries_congr cuspFunction_modularLambda_div_sixteen_eventuallyEq]
  simp (disch := assumption) only
    [normalizedLambdaEuler, taylorSeries_mul, taylorSeries_pow, taylorSeries_inv, taylorSeries_id,
      taylorSeries_eulerFunction, hTaylor 2 two_ne_zero, hTaylor 4 (by decide)]
  rw [modularLambdaCoordinate_toPowerSeries]
  simp only [map_mul, map_pow, map_X, map_invOfUnit_ringHom, map_one, map_expand,
    map_pentagonalSeries]
  rw [invOfUnit_eq' _ _ (by simp)]

end TauCeti.ModularForm
