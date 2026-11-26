/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
public import TauCeti.NumberTheory.DirichletCharacter.LFunction.RieszMellin
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Bundle
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.NumberTheory.MulChar.Lemmas
import TauCeti.Analysis.LaplaceTransform.Elementary
import TauCeti.Analysis.LaplaceTransform.Mellin
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Mellin
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic
import TauCeti.NumberTheory.LSeries.RiemannZeta.RieszMellin

/-!
# First Riesz remainders for primitive Dirichlet characters

Subtract the main term from the first Riesz sum of the twisted von Mangoldt coefficients.
The resulting remainder is continuous, intertwines inversion and complex conjugation, and has
an absolutely convergent upper Mellin transform on `1 < s.re`. The transform equals the
meromorphic Riesz expression, so estimates for the prime sum can be related to poles of that
expression.

The normalization and transform identities are those of Levent Alpöge's `Deduction.Gchi`,
`Deduction.mellin_Gchi_modOne` and `Deduction.mellin_Gchi_of_ne_one` in the formalization of the
Riemann hypothesis for Dirichlet L-functions.
-/

public section

open MeasureTheory Set
open scoped ArithmeticFunction.vonMangoldt ComplexConjugate

namespace TauCeti.PrimitiveDirichletCharacter

/-- The first Riesz sum of `χ(n) Λ(n)` after subtracting its main term. For the character of
conductor one the main term includes `y log y`, and its linear coefficient uses Euler's
constant. -/
noncomputable def rieszRemainder (χ : PrimitiveDirichletCharacter) (y : ℝ) : ℂ := by
  classical
  exact rieszSum (fun n ↦ χ.character n * (Λ n : ℂ)) y +
    if χ = 1 then
      (y : ℂ) * (1 + (Real.eulerMascheroniConstant : ℂ)) - (y : ℂ) * Real.log y
    else (y : ℂ) * logDeriv χ.character.LFunction 1

/-- At conductor one the first Riesz remainder subtracts `y log y - (1 + γ) y` from the
untwisted sum. -/
@[simp] theorem rieszRemainder_one (y : ℝ) :
    (1 : PrimitiveDirichletCharacter).rieszRemainder y =
      rieszSum (fun n ↦ (Λ n : ℂ)) y +
        ((y : ℂ) * (1 + (Real.eulerMascheroniConstant : ℂ)) - (y : ℂ) * Real.log y) := by
  have h (n : ℕ) : (1 : PrimitiveDirichletCharacter).character n = 1 :=
    DirichletCharacter.modOne_eq_one' (χ := (1 : DirichletCharacter ℂ 1)) n
  rw [rieszRemainder, ite_eq_left rfl]
  simp only [h, one_mul]

/-- A nontrivial primitive character has only a linear main term, given by the logarithmic
derivative at `1`. -/
theorem rieszRemainder_of_ne_one {χ : PrimitiveDirichletCharacter} (hχ : χ ≠ 1) (y : ℝ) :
    χ.rieszRemainder y =
      rieszSum (fun n ↦ χ.character n * (Λ n : ℂ)) y +
        (y : ℂ) * logDeriv χ.character.LFunction 1 := by
  simp [rieszRemainder, hχ]

/-- The first Riesz remainder is continuous, including at the lower Mellin endpoint `1`. -/
theorem continuous_rieszRemainder (χ : PrimitiveDirichletCharacter) :
    Continuous χ.rieszRemainder := by
  by_cases hχ : χ = 1
  · subst χ
    refine ((continuous_rieszSum (fun n ↦ (Λ n : ℂ))).add
      ((Complex.continuous_ofReal.mul_const (1 + (Real.eulerMascheroniConstant : ℂ))).sub
        (Complex.continuous_ofReal.comp Real.continuous_mul_log))).congr fun y ↦ ?_
    simp only [rieszRemainder_one, Function.comp_apply, Complex.ofReal_mul, Pi.add_apply,
      Pi.sub_apply]
  · exact ((continuous_rieszSum (fun n ↦ χ.character n * (Λ n : ℂ))).add
      (Complex.continuous_ofReal.mul_const (logDeriv χ.character.LFunction 1))).congr
        fun y ↦ (rieszRemainder_of_ne_one hχ y).symm

/-- The inverse character's first Riesz remainder is the complex conjugate of the original. -/
@[simp] theorem rieszRemainder_inv (χ : PrimitiveDirichletCharacter) (y : ℝ) :
    χ⁻¹.rieszRemainder y = conj (χ.rieszRemainder y) := by
  by_cases hχ : χ = 1
  · subst χ
    simp [rieszSum_def]
  · have hc : χ.character ≠ 1 := fun hc ↦ hχ (by
      rw [← of_character χ, hc, of_one])
    have hi : χ⁻¹ ≠ 1 := fun hi ↦ hχ (by
      simpa only [inv_inv, inv_one] using congrArg Inv.inv hi)
    have hlog : logDeriv (χ.character⁻¹).LFunction 1 =
        conj (logDeriv χ.character.LFunction 1) := by
      simpa only [map_one, logDeriv_apply, map_div₀] using congrArg₂ (· / ·)
        (χ.character.deriv_LFunction_inv_conj 1)
        (χ.character.LFunction_inv_conj (.inr hc) (s := 1))
    simp [rieszRemainder_of_ne_one hi, rieszRemainder_of_ne_one hχ, character_inv,
      rieszSum_def, hlog, ← MulChar.star_apply']

/-- On the half-plane of absolute convergence the remainder in logarithmic coordinates has
one-sided Laplace transform given by the meromorphic Riesz expression. -/
private theorem hasLaplace_rieszRemainder (χ : PrimitiveDirichletCharacter) {s : ℂ}
    (hs : 1 < s.re) :
    HasLaplace (χ.rieszRemainder ∘ Real.exp) s (rieszRemainderMellin χ.character.LFunction s) := by
  have h₀ : s ≠ 0 := Complex.ne_zero_of_re_pos (zero_lt_one.trans hs)
  have h₁ : s - 1 ≠ 0 := Complex.ne_zero_of_re_pos (by simpa using sub_pos.mpr hs)
  -- The twisted prime sum contributes the same logarithmic derivative term in both cases.
  have hr : HasLaplace (rieszSum (fun n ↦ χ.character n * (Λ n : ℂ)) ∘ Real.exp) s
      (-logDeriv χ.character.LFunction s / (s * (s - 1))) := by
    have hsum : LSeriesSummable (fun n : ℕ ↦ χ.character n * (Λ n : ℂ)) s :=
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ.character hs
    have hlog : logDeriv χ.character.LFunction s =
        -LSeries (fun n : ℕ ↦ χ.character n * (Λ n : ℂ)) s :=
      χ.character.logDeriv_LFunction_eq_neg_LSeries hs
    rw [hlog, neg_neg, hasLaplace_comp_exp_iff]
    simpa only [Real.exp_zero, neg_add', smul_eq_mul, mul_comm] using
      And.intro (integrableOn_rieszSum_mul_cpow hs hsum) (integral_rieszSum_mul_cpow hs hsum)
  have hlin (c : ℂ) := (hasLaplace_exp_mul_pow 0 hs).const_smul c
  by_cases hχ : χ = 1
  · subst χ
    have hzeta : (1 : PrimitiveDirichletCharacter).character.LFunction = riemannZeta :=
      DirichletCharacter.LFunction_modOne_eq (χ := (1 : DirichletCharacter ℂ 1))
    rw [hzeta] at hr ⊢
    have h := hr.add ((hlin (1 + (Real.eulerMascheroniConstant : ℂ))).sub
      (hasLaplace_exp_mul_pow 1 hs))
    rw [rieszRemainderMellin_riemannZeta hs]
    convert h using 1
    · ext u
      rw [Function.comp_apply, rieszRemainder, ite_eq_left rfl]
      simp [Function.comp_apply, Real.log_exp, mul_comm]
    · simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, Nat.reduceAdd, pow_one,
        smul_eq_mul, Complex.ofReal_one]
      field_simp
      ring
  · have hc : χ.character ≠ 1 := fun hc ↦ hχ (by rw [← of_character χ, hc, of_one])
    have h := hr.add (hlin (logDeriv χ.character.LFunction 1))
    rw [χ.character.rieszRemainderMellin_LFunction_of_ne_one hc hs]
    convert h using 1
    · ext u
      simp [rieszRemainder_of_ne_one hχ, mul_comm]
    · simp only [Nat.factorial_zero, Nat.cast_one, Nat.zero_add, pow_one, smul_eq_mul,
        Complex.ofReal_one]
      field_simp
      ring

/-- The upper Mellin integrand of the first Riesz remainder is absolutely integrable on
`Re s > 1`. -/
theorem integrableOn_rieszRemainder_mul_cpow (χ : PrimitiveDirichletCharacter) {s : ℂ}
    (hs : 1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ χ.rieszRemainder y * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  simpa only [Real.exp_zero, neg_add', smul_eq_mul, mul_comm] using
    ((hasLaplace_comp_exp_iff χ.rieszRemainder s _ 0).mp (hasLaplace_rieszRemainder χ hs)).1

/-- The upper Mellin integral of the first Riesz remainder equals its meromorphic expression
on the half-plane of absolute convergence. -/
theorem integral_rieszRemainder_mul_cpow (χ : PrimitiveDirichletCharacter) {s : ℂ}
    (hs : 1 < s.re) :
    ∫ y in Ioi (1 : ℝ), χ.rieszRemainder y * (y : ℂ) ^ (-s - 1) =
      rieszRemainderMellin χ.character.LFunction s := by
  simpa only [Real.exp_zero, neg_add', smul_eq_mul, mul_comm] using
    ((hasLaplace_comp_exp_iff χ.rieszRemainder s _ 0).mp (hasLaplace_rieszRemainder χ hs)).2

end TauCeti.PrimitiveDirichletCharacter
