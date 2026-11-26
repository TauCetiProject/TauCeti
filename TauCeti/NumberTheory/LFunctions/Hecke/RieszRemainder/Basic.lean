/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.VonMangoldt
public import TauCeti.NumberTheory.LFunctions.DedekindZeta.EulerKronecker
public import TauCeti.NumberTheory.LFunctions.Hecke.Conjugate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.VonMangoldtCoeff

/-!
# First Riesz remainders for primitive ray class characters

Subtract the linear main term from the norm-regrouped Riesz sum of a primitive character's
von Mangoldt coefficients. For the trivial character, subtract instead the logarithmic and
linear main terms associated with the simple pole of the Dedekind zeta function.
The remainders are continuous, respect conjugation, and for `Re s > 1` their Mellin integrals
`∫_1^∞ R(y) y ^ (-s - 1) dy` converge absolutely.

The rational normalization is that of Levent Alpöge's `Deduction.Gchi`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex MeasureTheory Set
open scoped ComplexConjugate NumberField

namespace TauCeti.LFunctions.PrimitiveRayClassCharacter

variable {K : Type*} [Field K] [NumberField K]

/-- The coefficients of the Riesz sum for a primitive ray class character: the ideal von
Mangoldt function twisted by the character and grouped by absolute norm. -/
noncomputable def rieszCoeff (ψ : PrimitiveRayClassCharacter K) : ℕ → ℂ :=
  normCoeff K ψ.character.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform

/-- The norm-regrouping formula for the twisted von Mangoldt coefficients. -/
theorem rieszCoeff_def (ψ : PrimitiveRayClassCharacter K) : ψ.rieszCoeff =
    normCoeff K ψ.character.toUnitaryIdealWeight.toIdealArithmeticFunction.vonMangoldtTransform :=
  (rfl)

/-- The trivial primitive character gives the untwisted ideal von Mangoldt coefficients. -/
@[simp] theorem rieszCoeff_one : (1 : PrimitiveRayClassCharacter K).rieszCoeff =
    normCoeff K (IdealArithmeticFunction.vonMangoldt : IdealArithmeticFunction K) := by
  simp [rieszCoeff_def, character_one,
    GlobalNumberFields.RayClassCharacter.toUnitaryIdealWeight_one]

/-- Inverting the primitive character conjugates its twisted von Mangoldt coefficients. -/
@[simp] theorem rieszCoeff_inv (ψ : PrimitiveRayClassCharacter K) (n : ℕ) :
    ψ⁻¹.rieszCoeff n = conj (ψ.rieszCoeff n) := by
  simp only [rieszCoeff_def, character_inv,
    GlobalNumberFields.RayClassCharacter.toUnitaryIdealWeight_inv,
    UnitaryIdealWeight.toIdealArithmeticFunction_eq_val, UnitaryIdealWeight.val_conj,
    MultiplicativeIdealWeight.toIdealArithmeticFunction_conj,
    IdealArithmeticFunction.vonMangoldtTransform_star, normCoeff_star_apply, Complex.star_def]

/-- The twisted von Mangoldt coefficients have an absolutely convergent Dirichlet series on
`Re s > 1`: the case of `ψ`'s unitary weight in
`UnitaryIdealWeight.LSeriesSummable_normCoeff_vonMangoldtTransform`. -/
theorem LSeriesSummable_rieszCoeff (ψ : PrimitiveRayClassCharacter K) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ψ.rieszCoeff s := by
  rw [rieszCoeff_def]
  exact ψ.character.toUnitaryIdealWeight.LSeriesSummable_normCoeff_vonMangoldtTransform hs

/-- The first Riesz sum of the twisted von Mangoldt coefficients with its main term removed.
The trivial character uses the logarithmic term and the Euler–Kronecker constant of `K`; the
other characters use the logarithmic derivative at `1`. -/
noncomputable def rieszRemainder (ψ : PrimitiveRayClassCharacter K) (y : ℝ) : ℂ := by
  classical
  exact rieszSum ψ.rieszCoeff y +
    if ψ = 1 then ((y * (1 + NumberField.eulerKroneckerConstant K) - y * Real.log y : ℝ) : ℂ)
    else (y : ℂ) * logDeriv (heckeLFunctionC ψ.character) 1

/-- The primitive trivial character's Riesz remainder, with the Dedekind zeta main term
subtracted. -/
@[simp] theorem rieszRemainder_one (y : ℝ) : (1 : PrimitiveRayClassCharacter K).rieszRemainder y =
    rieszSum (normCoeff K IdealArithmeticFunction.vonMangoldt) y +
      ((y * (1 + NumberField.eulerKroneckerConstant K) - y * Real.log y : ℝ) : ℂ) := by
  simp [rieszRemainder]

/-- The Riesz remainder of a nontrivial primitive character subtracts the linear main term
with coefficient `-L′(1)/L(1)`. -/
theorem rieszRemainder_of_ne_one (ψ : PrimitiveRayClassCharacter K) (hψ : ψ ≠ 1) (y : ℝ) :
    ψ.rieszRemainder y =
      rieszSum ψ.rieszCoeff y + (y : ℂ) * logDeriv (heckeLFunctionC ψ.character) 1 := by
  simp [rieszRemainder, hψ]

/-- The first Riesz remainder is continuous, including at the integer cutoffs and at `0`. -/
@[fun_prop] theorem continuous_rieszRemainder (ψ : PrimitiveRayClassCharacter K) :
    Continuous ψ.rieszRemainder := by
  by_cases hψ : ψ = 1
  · subst ψ
    rw [funext (rieszRemainder_one (K := K))]
    exact (continuous_rieszSum _).add (continuous_ofReal.comp
      ((continuous_id.mul_const _).sub Real.continuous_mul_log))
  · rw [funext (rieszRemainder_of_ne_one ψ hψ)]
    exact (continuous_rieszSum _).add (continuous_ofReal.mul_const _)

/-- Inverse primitive characters have conjugate Riesz remainders. -/
@[simp] theorem rieszRemainder_inv (ψ : PrimitiveRayClassCharacter K) (y : ℝ) :
    ψ⁻¹.rieszRemainder y = conj (ψ.rieszRemainder y) := by
  by_cases hψ : ψ = 1
  · subst ψ
    have hcoeff : (fun n ↦ conj ((1 : PrimitiveRayClassCharacter K).rieszCoeff n)) =
        (1 : PrimitiveRayClassCharacter K).rieszCoeff := by
      funext n
      rw [← rieszCoeff_inv, inv_one]
    simp only [inv_one, rieszRemainder_one, map_add, conj_ofReal, ← rieszCoeff_one,
      ← rieszSum_conj, hcoeff]
  · have hinv : ψ⁻¹ ≠ 1 := (inv_injective.eq_iff' inv_one).not.mpr hψ
    have hcoeff : ψ⁻¹.rieszCoeff = fun n ↦ conj (ψ.rieszCoeff n) := funext (ψ.rieszCoeff_inv)
    have hlog : logDeriv (heckeLFunctionC ψ.character⁻¹) 1 =
        conj (logDeriv (heckeLFunctionC ψ.character) 1) := by
      simpa only [map_one] using logDeriv_heckeLFunctionC_inv_conj ψ.character 1
    simp only [rieszRemainder_of_ne_one _ hinv, rieszRemainder_of_ne_one _ hψ, hcoeff,
      character_inv, hlog, rieszSum_conj, map_add, map_mul, conj_ofReal]

/-- For each exponent `σ > 1`, the first Riesz remainder is bounded by a constant times
`y ^ σ` for every `y ≥ 1`. -/
theorem exists_norm_rieszRemainder_le_rpow (ψ : PrimitiveRayClassCharacter K) {σ : ℝ}
    (hσ : 1 < σ) : ∃ C : ℝ, ∀ y ≥ 1, ‖ψ.rieszRemainder y‖ ≤ C * y ^ σ := by
  let M := ∑' n : ℕ, ‖LSeries.term ψ.rieszCoeff (σ : ℂ) n‖
  have hsum (y : ℝ) (hy : 1 ≤ y) : ‖rieszSum ψ.rieszCoeff y‖ ≤ M * y ^ σ := by
    simpa only [M, mul_comm] using norm_rieszSum_le hσ.le (zero_le_one.trans hy)
      (ψ.LSeriesSummable_rieszCoeff (s := (σ : ℂ)) (by simpa using hσ))
  by_cases hψ : ψ = 1
  · refine ⟨M + |1 + NumberField.eulerKroneckerConstant K| + (σ - 1)⁻¹, fun y hy ↦ ?_⟩
    have hy₀ : 0 ≤ y := zero_le_one.trans hy
    have hlog : y * Real.log y ≤ (σ - 1)⁻¹ * y ^ σ := by
      calc y * Real.log y ≤ y * (y ^ (σ - 1) / (σ - 1)) := by
              gcongr
              exact Real.log_le_rpow_div hy₀ (sub_pos.mpr hσ)
        _ = (σ - 1)⁻¹ * (y ^ (1 : ℝ) * y ^ (σ - 1)) := by
              rw [Real.rpow_one]
              ring
        _ = (σ - 1)⁻¹ * y ^ σ := by
              rw [← Real.rpow_add (zero_lt_one.trans_le hy)]
              ring_nf
    have hcorr : ‖((y * (1 + NumberField.eulerKroneckerConstant K) - y * Real.log y : ℝ) : ℂ)‖ ≤
        |1 + NumberField.eulerKroneckerConstant K| * y ^ σ + (σ - 1)⁻¹ * y ^ σ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg hy₀, abs_of_nonneg (Real.log_nonneg hy)]
      rw [mul_comm y |1 + NumberField.eulerKroneckerConstant K|]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_one_le hy hσ.le) (abs_nonneg _)) hlog
    rw [hψ, rieszRemainder_one, ← rieszCoeff_one]
    have hsum' : ‖rieszSum (1 : PrimitiveRayClassCharacter K).rieszCoeff y‖ ≤ M * y ^ σ := by
      simpa only [← hψ] using hsum y hy
    simpa only [add_mul, add_assoc] using (norm_add_le _ _).trans (add_le_add hsum' hcorr)
  · let D := logDeriv (heckeLFunctionC ψ.character) 1
    refine ⟨M + ‖D‖, fun y hy ↦ ?_⟩
    rw [rieszRemainder_of_ne_one ψ hψ, add_mul]
    refine (norm_add_le _ _).trans (add_le_add (hsum y hy) ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hy),
      mul_comm y]
    exact mul_le_mul_of_nonneg_left (Real.self_le_rpow_of_one_le hy hσ.le) (norm_nonneg D)

/-- The Mellin integrand of the first Riesz remainder is absolutely integrable on the upper
ray for `Re s > 1`. -/
theorem integrableOn_rieszRemainder_mul_cpow (ψ : PrimitiveRayClassCharacter K) {s : ℂ}
    (hs : 1 < s.re) : IntegrableOn (fun y : ℝ ↦ ψ.rieszRemainder y * (y : ℂ) ^ (-s - 1))
      (Ioi 1) := by
  obtain ⟨σ, hσ, hσs⟩ := exists_between hs
  obtain ⟨C, hC⟩ := ψ.exists_norm_rieszRemainder_le_rpow hσ
  have hg : Asymptotics.IsBigO Filter.atTop ψ.rieszRemainder (fun y : ℝ ↦ y ^ (-(-σ))) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with y hy
    simpa only [neg_neg, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hy) _)] using hC y hy
  have hint := integrableOn_Ioi_cpow_smul_of_isBigO
    (ψ.continuous_rieszRemainder.continuousOn.locallyIntegrableOn measurableSet_Ioi) hg
    (z := -s) (by simpa only [neg_re, neg_lt_neg_iff] using hσs)
  simpa only [smul_eq_mul, mul_comm] using hint

end TauCeti.LFunctions.PrimitiveRayClassCharacter
