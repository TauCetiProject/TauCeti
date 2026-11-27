/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import TauCeti.Data.Nat.GCD
import Mathlib.NumberTheory.LSeries.Linearity
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.Basic

/-!
# Dirichlet series of twisted von Mangoldt weights in a residue class

Character orthogonality computes the Dirichlet series of the von Mangoldt weight in an
invertible residue class, multiplied by a Dirichlet character at a possibly different level.
Subtracting this series from the untwisted one gives the signed combination of logarithmic
derivatives for the weight with factor `1 - ξ(n)`. If the conductor of the twisting character
does not divide the progression modulus, the pole-subtracted expression is analytic at `1`.

The quadratic application is the character expansion
`New.LSeries_lambdaKResidueClass_eq_add_logDerivMean` in
`grh/src/New/Reduction/Zeros/PrimeError.lean` in lsernau/grh-lean (`72fead1`).
-/

public section

open DirichletCharacter
open scoped LSeries.notation

namespace ArithmeticFunction.vonMangoldt

/-- The series of the twisted von Mangoldt weight in an invertible residue class converges
absolutely to the negative weighted mean of the logarithmic derivatives of the product
characters at the least common multiple of the levels. -/
theorem LSeriesHasSum_residueClass_mul_char {q d : ℕ} [NeZero q] [NeZero d]
    {a : ZMod q} (ha : IsUnit a) (ξ : DirichletCharacter ℂ d) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (residueClass a n : ℂ) * ξ n) s
      (-(q.totient : ℂ)⁻¹ * ∑ ψ : DirichletCharacter ℂ q,
        ψ a⁻¹ * logDeriv (ψ.mul ξ).LFunction s) := by
  have hχ (ψ : DirichletCharacter ℂ q) : LSeriesHasSum (↗(ψ.mul ξ) * ↗vonMangoldt) s
      (-logDeriv (ψ.mul ξ).LFunction s) := by
    simpa only [DirichletCharacter.logDeriv_LFunction_eq_neg_LSeries _ hs, neg_neg] using
      (LSeriesSummable_twist_vonMangoldt (ψ.mul ξ) hs).LSeriesHasSum
  have hsum := (LSeriesHasSum.sum (S := Finset.univ) fun ψ _ ↦
    (hχ ψ).smul (ψ a⁻¹)).smul (q.totient : ℂ)⁻¹
  rw [neg_mul, ← mul_neg, ← Finset.sum_neg_distrib]
  simp_rw [← mul_neg]
  refine (LSeriesHasSum_congr s _ ?_).mp hsum
  intro n _
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.mul_apply,
    mul_natCast, residueClass_apply ha, mul_assoc, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun ψ _ ↦ by ring

/-- The weight with factor `1 - ξ(n)` has Dirichlet series equal to the untwisted expression
minus the twisted one. The term `s / (φ(q) * (s - 1))` isolates the untwisted pole at `1`
with the normalization used in the Mellin transform of the first smoothed sum. -/
theorem LSeriesHasSum_residueClass_mul_one_sub {q d : ℕ} [NeZero q] [NeZero d]
    {a : ZMod q} (ha : IsUnit a) (ξ : DirichletCharacter ℂ d) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ (residueClass a n : ℂ) * (1 - ξ n)) s
      (s / ((q.totient : ℂ) * (s - 1)) + (LFunctionResidueClassAux a s +
        (q.totient : ℂ)⁻¹ * (∑ ψ : DirichletCharacter ℂ q,
          ψ a⁻¹ * logDeriv (ψ.mul ξ).LFunction s) - (q.totient : ℂ)⁻¹)) := by
  have habs := (abscissaOfAbsConv_residueClass_le_one a).trans_lt (EReal.coe_lt_coe_iff.mpr hs)
  have h₀ := (LSeriesSummable_of_abscissaOfAbsConv_lt_re habs).LSeriesHasSum
  have h₁ := h₀.sub (LSeriesHasSum_residueClass_mul_char ha ξ hs)
  have hc : LSeriesHasSum (fun n : ℕ ↦ (residueClass a n : ℂ) * (1 - ξ n)) s _ :=
    (LSeriesHasSum_congr s _ (fun _ ↦ by simp [mul_sub])).mp h₁
  convert hc using 1
  have he := eqOn_LFunctionResidueClassAux ha hs
  have hs₁ : s - 1 ≠ 0 := sub_ne_zero.mpr (by rintro rfl; simp at hs)
  have hq : (q.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  rw [he]
  field_simp
  ring

/-- The auxiliary expression used to subtract the pole of the von Mangoldt series in an
invertible residue class is analytic at `1`. -/
theorem analyticAt_LFunctionResidueClassAux_one {q : ℕ} [NeZero q] (a : ZMod q) :
    AnalyticAt ℂ (LFunctionResidueClassAux a) 1 := by
  classical
  have h₀ : AnalyticAt ℂ (fun s ↦ -logDeriv (LFunctionTrivChar₁ q) s) 1 :=
    (((differentiable_LFunctionTrivChar₁ q).analyticAt 1).logDeriv
      (LFunctionTrivChar₁_apply_one_ne_zero q)).fun_neg
  have h₁ : AnalyticAt ℂ (fun s ↦ ∑ ψ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)),
      ψ a⁻¹ * logDeriv ψ.LFunction s) 1 := by
    refine Finset.analyticAt_fun_sum _ fun ψ hψ ↦ analyticAt_const.fun_mul ?_
    have hψ' : ψ ≠ 1 := by simpa using hψ
    exact (ψ.analyticAt_LFunction (.inr hψ')).logDeriv
      (LFunction_ne_zero_of_one_le_re ψ (.inl hψ') (by simp))
  have hc : AnalyticAt ℂ (fun _ : ℂ ↦ (q.totient : ℂ)⁻¹) 1 := analyticAt_const
  convert hc.fun_mul (h₀.fun_sub h₁) using 1
  ext s
  simp only [LFunctionResidueClassAux, logDeriv_apply, neg_div, mul_div_assoc]

/-- The pole-subtracted expression for the weight with factor `1 - ξ(n)` is analytic at `1`
when the conductor of `ξ` does not divide `q`: no product character in the twisted sum can
be principal. -/
theorem analyticAt_residueClass_mul_one_sub_logDeriv_one {q d : ℕ} [NeZero q] [NeZero d]
    (a : ZMod q) (ξ : DirichletCharacter ℂ d) (hξ : ¬ ξ.conductor ∣ q) :
    AnalyticAt ℂ (fun s ↦ LFunctionResidueClassAux a s +
      (q.totient : ℂ)⁻¹ * (∑ ψ : DirichletCharacter ℂ q,
        ψ a⁻¹ * logDeriv (ψ.mul ξ).LFunction s) - (q.totient : ℂ)⁻¹) 1 := by
  refine ((analyticAt_LFunctionResidueClassAux_one a).fun_add
    (analyticAt_const.fun_mul (Finset.analyticAt_fun_sum _ fun ψ _ ↦
      analyticAt_const.fun_mul ?_))).sub analyticAt_const
  have hψξ : ψ.mul ξ ≠ 1 := by
    intro h
    rw [DirichletCharacter.mul, mul_comm, mul_eq_one_iff_eq_inv] at h
    have hc := congrArg conductor h
    rw [conductor_inv, conductor_changeLevel, conductor_changeLevel] at hc
    exact hξ (hc ▸ ψ.conductor_dvd_level)
  exact ((ψ.mul ξ).analyticAt_LFunction (.inr hψξ)).logDeriv
    (LFunction_ne_zero_of_one_le_re _ (.inl hψξ) (by simp))

end ArithmeticFunction.vonMangoldt
