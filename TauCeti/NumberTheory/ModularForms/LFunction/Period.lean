/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.LFunction.Basic
public import TauCeti.NumberTheory.ModularForms.GeodesicIntegral.BetweenCusps

/-!
# Periods of cusp forms are values of their `L`-functions

Let `f` be a cusp form of weight `k > 0` on an arithmetic subgroup `Γ`. Its **periods** are the
integrals `rₙ(f) = ∫₀^{i∞} f(τ) τⁿ dτ`, `n ≥ 0`, along the positive imaginary axis, the integral
`TauCeti.cuspIntegral` between the cusps `0` and `∞`. Substituting `τ = i t` turns `rₙ(f)` into
`iⁿ⁺¹` times the Mellin transform of `t ↦ f(i t)` at `n + 1`, which is Mathlib's completed
`L`-function `ModularForm.Λ`:

`rₙ(f) = iⁿ⁺¹ Λ(f, n + 1) = n! / (-2πi)ⁿ⁺¹ · L(f, n + 1)`.

For `f` of weight `k = w + 2` and `0 ≤ n ≤ w` these are the values of `L(f, s)` at the critical
integers `s = 1, …, k - 1`, and they are, up to binomial coefficients and signs, the
coefficients of the period polynomial of `f`. This is how nonvanishing of `L`-values enters the
Eichler–Shimura theory of period polynomials.

## Main results

* `TauCeti.cuspIntegral_mul_pow_zero_infty`: `∫₀^{i∞} f(τ) τⁿ dτ = iⁿ⁺¹ Λ(f, n + 1)`.
* `TauCeti.cuspIntegral_mul_pow_zero_infty_eq_L`: `∫₀^{i∞} f(τ) τⁿ dτ = n! / (-2πi)ⁿ⁺¹ L(f, n + 1)`.

## References

* Y. I. Manin, *Periods of parabolic forms and p-adic Hecke series*, Mat. Sb. **92** (1973),
  378–401, §1.
* W. Kohnen and D. Zagier, *Modular forms with rational periods*, in *Modular Forms*
  (R. A. Rankin, ed.), Ellis Horwood, 1984, 197–249, §1.1.
-/

public section

open UpperHalfPlane hiding I
open Complex MeasureTheory Set OnePoint
open scoped ModularForm Nat Real

namespace TauCeti

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
  [CuspFormClass F Γ k]

/-- **Periods are completed `L`-values**: the period `∫₀^{i∞} f(τ) τⁿ dτ` of a cusp form `f` of
positive weight on an arithmetic subgroup is `iⁿ⁺¹ Λ(f, n + 1)`, for Mathlib's completed
`L`-function `ModularForm.Λ`. -/
theorem cuspIntegral_mul_pow_zero_infty (hk : 0 < k) (f : F) (n : ℕ) :
    cuspIntegral (fun τ ↦ f τ * (τ : ℂ) ^ n) ((0 : ℚ) : OnePoint ℚ) ∞ =
      I ^ (n + 1) * ModularForm.Λ hk f (n + 1) := by
  -- the geodesic from `0` to `∞` is the positive imaginary axis, cut out by the identity matrix
  have h := cuspIntegral_smul_zero_smul_infty (fun τ ↦ f τ * (τ : ℂ) ^ n) (g := 1) (by simp)
  rw [one_smul, one_smul] at h
  rw [h, Matrix.GeneralLinearGroup.geodesicIntegral_def, SlashAction.slash_one,
    CuspForm.Λ_eq_mellin, mellin, pow_succ', mul_assoc, ← integral_const_mul (I ^ n)]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  rw [resToImagAxis_of_pos _ ht, ofComplex_apply_of_im_pos (by simpa using ht),
    add_sub_cancel_right, smul_eq_mul, cpow_natCast]
  ring

/-- **Periods are `L`-values at positive integers**: the period `∫₀^{i∞} f(τ) τⁿ dτ` of a cusp
form `f` of positive weight `k` on an arithmetic subgroup is `n! / (-2πi)ⁿ⁺¹ · L(f, n + 1)`, for
Mathlib's `L`-function `ModularForm.L`. For `0 ≤ n ≤ k - 2` these are the critical values. -/
theorem cuspIntegral_mul_pow_zero_infty_eq_L (hk : 0 < k) (f : F) (n : ℕ) :
    cuspIntegral (fun τ ↦ f τ * (τ : ℂ) ^ n) ((0 : ℚ) : OnePoint ℚ) ∞ =
      n ! / (-2 * π * I) ^ (n + 1) * ModularForm.L hk f (n + 1) := by
  -- `iⁿ⁺¹ = 1 / (-i)ⁿ⁺¹`
  have hI : I ^ (n + 1) = ((-I) ^ (n + 1))⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_pow, mul_neg, I_mul_I, neg_neg, one_pow])
  rw [cuspIntegral_mul_pow_zero_infty hk, ModularForm.Λ_natCast_add_one, hI,
    show (-2 * π * I : ℂ) = 2 * π * -I by ring, mul_pow (2 * π : ℂ) (-I)]
  field_simp

end TauCeti
