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
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
public import Mathlib.RingTheory.PowerSeries.Inverse
import TauCeti.RingTheory.PowerSeries.HasFPowerSeriesOnBall
import TauCeti.Analysis.Analytic.PowerSubstitution
import TauCeti.Analysis.Complex.UpperHalfPlane.Exp
import TauCeti.Analysis.SpecialFunctions.QPochhammer
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

open Complex Filter Topology PowerSeries
open scoped UpperHalfPlane

namespace TauCeti.ModularForm

private def eulerSeries (k : ℕ) (hk : k ≠ 0) : ℤ⟦X⟧ :=
  (pentagonalSeries ℤ).expand k hk

private theorem eulerSeries_constantCoeff (k : ℕ) (hk : k ≠ 0) :
    constantCoeff (eulerSeries k hk) = 1 := by
  rw [eulerSeries, constantCoeff_expand]
  rw [← coeff_zero_eq_constantCoeff_apply,
    ← show pentagonal 0 = 0 by norm_num [pentagonal_def], coeff_pentagonalSeries_pentagonal]
  norm_num

/-- The strict integral coordinate underlying the normalized modular lambda function. -/
def modularLambdaCoordinate : FormalCoordinate ℤ where
  toPowerSeries := X * (eulerSeries 1 one_ne_zero * eulerSeries 4 (by decide) ^ 2 *
    (eulerSeries 2 two_ne_zero).invOfUnit 1 ^ 3) ^ 8
  constantCoeff_toPowerSeries := by simp
  isUnit_coeff_one := by
    have h (k : ℕ) (hk : k ≠ 0) := eulerSeries_constantCoeff k hk
    simp [h, constantCoeff_invOfUnit]

/-- The normalized series is the integral Euler quotient, expressed using the inverse of its
unit denominator. -/
theorem modularLambdaCoordinate_toPowerSeries :
    modularLambdaCoordinate.toPowerSeries = X *
      ((pentagonalSeries ℤ) * ((pentagonalSeries ℤ).expand 4 (by decide)) ^ 2 *
        ((pentagonalSeries ℤ).expand 2 two_ne_zero).invOfUnit 1 ^ 3) ^ 8 := by
  simp [modularLambdaCoordinate, eulerSeries]

/-- The normalized modular lambda series has linear coefficient one. -/
@[simp]
theorem modularLambdaCoordinate_coeff_one :
    coeff 1 modularLambdaCoordinate.toPowerSeries = 1 := by
  have h (k : ℕ) (hk : k ≠ 0) := eulerSeries_constantCoeff k hk
  simp [modularLambdaCoordinate, h,
    constantCoeff_invOfUnit]

/-- The normalized modular lambda series begins `X - 8 X²`. -/
@[simp]
theorem modularLambdaCoordinate_coeff_two :
    coeff 2 modularLambdaCoordinate.toPowerSeries = -8 := by
  let E := pentagonalSeries ℤ
  let E₂ := E.expand 2 two_ne_zero
  let E₄ := E.expand 4 (by decide)
  have h₀ : constantCoeff E = 1 := by
    simpa [E, eulerSeries] using eulerSeries_constantCoeff 1 one_ne_zero
  have h₁ : coeff 1 E = -1 := by
    have h := coeff_pentagonalSeries_pentagonal ℤ 1
    rw [show pentagonal 1 = 1 by norm_num [pentagonal_def]] at h
    simpa [Int.coe_negOnePow] using h
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

private theorem eulerSeries_analyticAt_taylorSeries (k : ℕ) (hk : k ≠ 0) :
    AnalyticAt ℂ (fun q : ℂ ↦ eulerFunction (q ^ k)) 0 ∧
      taylorSeries (fun q : ℂ ↦ eulerFunction (q ^ k)) 0 =
        (eulerSeries k hk).map (Int.castRingHom ℂ) := by
  have hcoeff (n : ℕ) : ‖(pentagonalSeries ℂ).coeff n‖ ≤ 1 := by
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨j, rfl⟩ := hn
      simp [Int.coe_negOnePow]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]
  have hs : HasFPowerSeriesOnBall (eulerFunction : ℂ → ℂ)
      (.ofScalars ℂ fun n ↦ (pentagonalSeries ℂ).coeff n) 0 1 := by
    have hrad := PowerSeries.le_radius_of_bound (f := pentagonalSeries ℂ) 1 (r := 1)
      (fun n ↦ by simpa using hcoeff n)
    refine ⟨?_, by norm_num, ?_⟩
    · simpa [PowerSeries.radius_eq_radius_ofScalars ℂ] using hrad
    · intro q hq
      have hqn : ‖q‖ < 1 := by
        simpa only [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one,
          Metric.mem_ball, dist_zero_right] using hq
      simpa [smul_eq_mul, mul_comm] using hasSum_eulerFunction_pentagonalSeries hqn
  have he := hs.hasFPowerSeriesAt
  refine ⟨he.analyticAt.comp_of_eq (by fun_prop) (zero_pow hk), ?_⟩
  have ht : taylorSeries (eulerFunction : ℂ → ℂ) 0 = pentagonalSeries ℂ := by
    ext n
    simpa using he.coeff_taylorSeries n
  have hm : (pentagonalSeries ℤ).map (Int.castRingHom ℂ) = pentagonalSeries ℂ := by
    ext n
    by_cases hn : n ∈ Set.range pentagonal
    · obtain ⟨j, rfl⟩ := hn
      simp [Int.coe_negOnePow]
    · simp [coeff_pentagonalSeries_eq_zero _ hn]
  rw [taylorSeries_comp_pow he.analyticAt k hk, ht, eulerSeries, map_expand, hm]

private theorem eulerFunction_zero : eulerFunction (0 : ℂ) = 1 := by
  rw [eulerFunction_eq_tprod (by simp)]
  simp

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

private theorem map_eulerSeries_inv (k : ℕ) (hk : k ≠ 0) :
    ((eulerSeries k hk).invOfUnit 1).map (Int.castRingHom ℂ) =
      ((eulerSeries k hk).map (Int.castRingHom ℂ))⁻¹ := by
  rw [map_invOfUnit_ringHom, map_one]
  exact invOfUnit_eq' _ _ (by simp [eulerSeries_constantCoeff k hk])

private def normalizedLambdaEuler (q : ℂ) : ℂ :=
  q * (eulerFunction q * eulerFunction (q ^ 4) ^ 2 *
    (eulerFunction (q ^ 2))⁻¹ ^ 3) ^ 8

private theorem analyticAt_normalizedLambdaEuler : AnalyticAt ℂ normalizedLambdaEuler 0 := by
  have h₁ : AnalyticAt ℂ (eulerFunction : ℂ → ℂ) 0 := by
    simpa using (eulerSeries_analyticAt_taylorSeries 1 one_ne_zero).1
  have h₂ := (eulerSeries_analyticAt_taylorSeries 2 two_ne_zero).1
  have h₄ := (eulerSeries_analyticAt_taylorSeries 4 (by decide)).1
  exact analyticAt_id.mul (((h₁.mul (h₄.pow 2)).mul
    ((h₂.inv (by simp [eulerFunction_zero])).pow 3)).pow 8)

private theorem cuspFunction_modularLambda_div_sixteen_eventuallyEq :
    UpperHalfPlane.cuspFunction 2 (fun τ : ℍ ↦ modularLambda τ / 16) =ᶠ[𝓝 0]
      normalizedLambdaEuler := by
  have hfun : (fun τ : ℍ ↦ modularLambda τ / 16) =
      fun τ : ℍ ↦ normalizedLambdaEuler (Function.Periodic.qParam 2 τ) := by
    funext τ
    rw [modularLambda_div_sixteen_eq_euler τ.im_pos]
    have hq : cexp (Real.pi * I * τ) = Function.Periodic.qParam 2 τ := by
      simpa using Periodic.exp_pi_mul_I_mul_eq_qParam_pow
        (h := 2) (t := 1) (m := 1) (by norm_num) (by norm_num) τ
    simp [hq, normalizedLambdaEuler]
  rw [hfun]
  apply TauCeti.UpperHalfPlane.cuspFunction_eventuallyEq_nhds_of_continuousAt _
    analyticAt_normalizedLambdaEuler.continuousAt
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hqn
  have hq0 : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
  rw [TauCeti.UpperHalfPlane.cuspFunction_of_ne_zero hq0,
    UpperHalfPlane.ofComplex_apply_of_im_pos
      (Function.Periodic.im_invQParam_pos_of_norm_lt_one (by norm_num)
        (mem_ball_zero_iff.mp hqn) hq0),
    Function.Periodic.qParam_right_inv (by norm_num : (2 : ℝ) ≠ 0) hq0]

/-- The width-two cusp function of `λ / 16` is analytic at the origin. -/
theorem analyticAt_cuspFunction_modularLambda_div_sixteen :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 2 (fun τ : ℍ ↦ modularLambda τ / 16)) 0 :=
  analyticAt_normalizedLambdaEuler.congr cuspFunction_modularLambda_div_sixteen_eventuallyEq.symm

private theorem qExpansion_modularLambda_div_sixteen_eq_taylor :
    UpperHalfPlane.qExpansion 2 (fun τ : ℍ ↦ modularLambda τ / 16) =
      taylorSeries normalizedLambdaEuler 0 := by
  rw [← taylorSeries_congr cuspFunction_modularLambda_div_sixteen_eventuallyEq]
  ext n
  rw [(TauCeti.UpperHalfPlane.hasFPowerSeriesAt_cuspFunction
    analyticAt_cuspFunction_modularLambda_div_sixteen).coeff_taylorSeries]
  simp

private theorem taylorSeries_euler_inv_two :
    taylorSeries ((fun q : ℂ ↦ eulerFunction (q ^ 2))⁻¹) 0 =
      ((eulerSeries 2 two_ne_zero).map (Int.castRingHom ℂ))⁻¹ := by
  let f : ℂ → ℂ := fun q ↦ eulerFunction (q ^ 2)
  have hf : AnalyticAt ℂ f 0 := (eulerSeries_analyticAt_taylorSeries 2 two_ne_zero).1
  have hf0 : f 0 ≠ 0 := by simp [f, eulerFunction_zero]
  rw [← (eulerSeries_analyticAt_taylorSeries 2 two_ne_zero).2]
  -- Match both Taylor series with the same local function before applying the inverse criterion.
  change taylorSeries f⁻¹ 0 = (taylorSeries f 0)⁻¹
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simpa using hf0)).mpr
  rw [← taylorSeries_mul (hf.inv hf0) hf]
  rw [← map_one (C : ℂ →+* ℂ⟦X⟧), ← taylorSeries_const (a := (0 : ℂ)) (1 : ℂ)]
  apply taylorSeries_congr
  filter_upwards [hf.continuousAt.eventually_ne hf0] with q hq
  exact inv_mul_cancel₀ hq

/-- The integral formal coordinate is the width-two `q`-expansion of `λ / 16`. -/
theorem modularLambdaCoordinate_map_eq_qExpansion :
    modularLambdaCoordinate.toPowerSeries.map (Int.castRingHom ℂ) =
      UpperHalfPlane.qExpansion 2 (fun τ : ℍ ↦ modularLambda τ / 16) := by
  let E (k : ℕ) : ℂ → ℂ := fun q ↦ eulerFunction (q ^ k)
  have hE (k : ℕ) (hk : k ≠ 0) : AnalyticAt ℂ (E k) 0 :=
    (eulerSeries_analyticAt_taylorSeries k hk).1
  have hE0 : E 2 0 ≠ 0 := by simp [E, eulerFunction_zero]
  have hA := (hE 1 one_ne_zero).mul ((hE 4 (by decide)).pow 2)
  have hB := ((hE 2 two_ne_zero).inv hE0).pow 3
  have hF := hA.mul hB
  rw [qExpansion_modularLambda_div_sixteen_eq_taylor]
  have hform : normalizedLambdaEuler =
      (fun q : ℂ ↦ q) * (E 1 * E 4 ^ 2 * (E 2)⁻¹ ^ 3) ^ 8 := by
    funext q
    simp [normalizedLambdaEuler, E]
  rw [hform]
  have hId : AnalyticAt ℂ (fun q : ℂ ↦ q) 0 := by fun_prop
  rw [taylorSeries_mul hId (hF.pow 8), taylorSeries_pow hF, taylorSeries_mul hA hB,
    taylorSeries_mul (hE 1 one_ne_zero) ((hE 4 (by decide)).pow 2),
    taylorSeries_pow (hE 4 (by decide)), taylorSeries_pow ((hE 2 two_ne_zero).inv hE0)]
  have hid : taylorSeries (fun q : ℂ ↦ q) 0 = X := by
    simpa using (taylorSeries_sub_const (𝕜 := ℂ) (a := 0))
  rw [hid]
  simp only [E, modularLambdaCoordinate, map_mul, map_pow, map_X, map_eulerSeries_inv]
  rw [(eulerSeries_analyticAt_taylorSeries 1 one_ne_zero).2,
    (eulerSeries_analyticAt_taylorSeries 4 (by decide)).2, taylorSeries_euler_inv_two]

end TauCeti.ModularForm
