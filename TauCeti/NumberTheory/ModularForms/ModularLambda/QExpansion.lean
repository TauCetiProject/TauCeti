/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import TauCeti.NumberTheory.ModularForms.ModularLambda.Basic
public import TauCeti.NumberTheory.ModularForms.ModularLambda.Coordinate
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Combinatorics.Enumerative.Pentagonal.EulerFunction
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
import TauCeti.RingTheory.MvPowerSeries.Inverse

/-!
# The integral `q`-expansion of the modular lambda function

In the nome `q = exp (π i τ)`, the normalized modular function `λ / 16` has expansion
`q (E(q) E(q⁴)² / E(q²)³)⁸`, where `E(q) = ∏_{n ≥ 1} (1 - q^n)`. This is the
complex image of the integral formal coordinate.

## Main results

* `TauCeti.ModularForm.analyticAt_cuspFunction_modularLambda_div_sixteen`: the cusp function
  of `λ / 16` is analytic at zero.
* `TauCeti.ModularForm.modularLambdaCoordinate_map_eq_qExpansion`: the width-two expansion
  is obtained by mapping the integral coordinate to `ℂ`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), §1.1.3.
-/

public noncomputable section

open Complex Topology PowerSeries
open scoped UpperHalfPlane

namespace TauCeti.ModularForm

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

-- Use the same analyticity rules for the product and the Taylor rewrites of its factors.
local macro "prove_lambda_euler_analytic" : tactic =>
  `(tactic| (
    have hE := analyticAt_eulerFunction_zero (𝕜 := ℂ)
    have h₂ := analyticAt_eulerFunction_comp_pow (𝕜 := ℂ) 2
    have h₄ := analyticAt_eulerFunction_comp_pow (𝕜 := ℂ) 4
    fun_prop (disch := simp)))

private theorem analyticAt_normalizedLambdaEuler : AnalyticAt ℂ normalizedLambdaEuler 0 := by
  unfold normalizedLambdaEuler
  prove_lambda_euler_analytic

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
  rw [TauCeti.UpperHalfPlane.qExpansion_eq_taylorSeries
    analyticAt_cuspFunction_modularLambda_div_sixteen,
    taylorSeries_congr cuspFunction_modularLambda_div_sixteen_eventuallyEq]
  have hId : AnalyticAt ℂ (fun q : ℂ ↦ q) 0 := analyticAt_id
  simp (disch := first | assumption | decide | prove_lambda_euler_analytic | (simp; done)) only
    [normalizedLambdaEuler, taylorSeries_mul, taylorSeries_pow, taylorSeries_inv, taylorSeries_id,
      taylorSeries_eulerFunction, taylorSeries_eulerFunction_comp_pow]
  rw [modularLambdaCoordinate_toPowerSeries]
  simp only [map_mul, map_pow, map_X, map_invOfUnit_ringHom, map_one, map_expand,
    map_pentagonalSeries]
  rw [invOfUnit_eq' _ _ (by simp)]

end TauCeti.ModularForm
