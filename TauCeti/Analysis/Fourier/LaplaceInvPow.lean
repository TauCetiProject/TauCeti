/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform

import TauCeti.Analysis.LaplaceTransform.Elementary
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Laplace's inverse Fourier integral for `1 / Γ` and Gaussian powers

For an integer `k ≥ 1`, the function `z ↦ (1 + 2πiz) ^ (-(k + 1))` on `ℝ` is the Fourier
transform of the Gamma density `t ↦ t ^ k * exp (-t) / k!` supported on `(0, ∞)`. Fourier
inversion evaluates the oscillatory integral `∫ z : ℝ, 𝐞 (x * z) * ((1 + 2πiz) ^ (k + 1))⁻¹`
for every real `x`, yielding `x ^ k * exp (-x) / k!` for `x ≥ 0` and `0` for `x ≤ 0`.

Combining this with the complex Gaussian integral `∫ w : ℂ, exp (-(1 + 2πit) ‖w‖²) = π / (1 + 2πit)`
evaluates the `n`-th power Gaussian Fourier integral for `n ≥ 2` and `a ≥ 0`.

## Main statements

* `TauCeti.integral_fourierChar_mul_inv_pow_eq_ite`: piecewise evaluation of Laplace's inverse
  Fourier integral for all `x : ℝ`.
* `TauCeti.integral_fourierChar_mul_inv_pow`: evaluation for `x ≥ 0`.
* `TauCeti.integral_fourierChar_mul_inv_pow_of_nonpos`: vanishing for `x ≤ 0`.
* `TauCeti.integral_fourierChar_mul_gaussian_pow`: Fourier inversion for the `n`-th power of the
  complex Gaussian integral (`n ≥ 2`, `a ≥ 0`).

## Provenance

Adapted from `New.integral_fourierChar_mul_inv_pow` and `New.integral_fourierChar_mul_gaussian_pow`
in `grh/src/Lib/SiegelWeil/OneVector/SiegelClassSum.lean` of `grh-lean`
(<https://github.com/lsernau/grh-lean>, commit `72fead102f663d5c7a407964a13dc0cf9d977207`),
using `TauCeti.hasLaplace_pow` from `TauCeti.Analysis.LaplaceTransform.Elementary`.
-/

@[expose] public section

open Complex MeasureTheory Real
open scoped FourierTransform Nat Real

namespace TauCeti

/-- Laplace's inverse Fourier integral for `1 / Γ`: for an integer `k ≥ 1` and any `x : ℝ`,
`∫ z : ℝ, 𝐞 (x * z) * ((1 + 2πiz) ^ (k + 1))⁻¹` equals `x ^ k * exp (-x) / k!` if `0 ≤ x`
and `0` otherwise. -/
theorem integral_fourierChar_mul_inv_pow_eq_ite {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    ∫ z : ℝ, 𝐞 (x * z) * ((1 + 2 * π * Complex.I * z : ℂ) ^ (k + 1))⁻¹ =
      if 0 ≤ x then (x : ℂ) ^ k * Complex.exp (-x) / k ! else 0 := by
  let g (z : ℝ) : ℂ := ((1 + 2 * π * Complex.I * z) ^ (k + 1))⁻¹
  let p (t : ℝ) : ℂ := (t.toNNReal : ℂ) ^ k * Complex.exp (-t) / k.factorial
  have hg : g = 𝓕 p := by
    ext z
    have hlap : ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ k * Complex.exp (-(1 + 2 * π * Complex.I * z) * t) =
        (k.factorial : ℂ) / (1 + 2 * π * Complex.I * z) ^ (k + 1) := by
      simpa only [smul_eq_mul, mul_comm] using
        (TauCeti.hasLaplace_pow k (s := 1 + 2 * π * Complex.I * z) (by simp)).integral_eq
    calc g z = (∫ t : ℝ in Set.Ioi 0,
            (t : ℂ) ^ k * Complex.exp (-(1 + 2 * π * Complex.I * z) * t)) / k.factorial := by
          rw [hlap, div_div_cancel_left₀ (mod_cast k.factorial_ne_zero)]
      _ = 𝓕 p z := by
          rw [Real.fourier_eq', ← integral_div, ← integral_indicator measurableSet_Ioi]
          congr with t
          rcases lt_or_ge 0 t with ht | ht
          · simp [p, ht, ht.le, Complex.exp_add, add_mul, Complex.exp_neg]
            ring_nf
          · simp [p, ht, Nat.one_le_iff_ne_zero.mp hk]
  have h_ne : 𝓕 p 0 ≠ 0 := by simp [← hg, g]
  have p_int : Integrable p := .of_integral_ne_zero (by simpa [Real.fourier_eq] using h_ne)
  have h_norm (z : ℝ) : ‖g z‖ ≤ (1 + (2 * π * z) ^ 2)⁻¹ := calc
    ‖g z‖ = (√(1 + (2 * π * z) ^ 2) ^ (k + 1))⁻¹ := by
      simp [g, Complex.norm_eq_sqrt_sq_add_sq]
    _ ≤ (√(1 + (2 * π * z) ^ 2) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by simp [sq_nonneg]) (Nat.succ_le_succ hk))
    _ = (1 + (2 * π * z) ^ 2)⁻¹ := by rw [Real.sq_sqrt (by positivity)]
  have g_int : Integrable g := (integrable_inv_one_add_sq.comp_mul_left' two_pi_pos.ne').mono'
    (by fun_prop) (.of_forall h_norm)
  have h_inv : 𝓕⁻ g x = p x := by
    rw [hg, p_int.fourierInv_fourier_eq (by rwa [← hg]) (by fun_prop)]
  by_cases hx : 0 ≤ x
  · simpa [Real.fourierInv_eq, hx, g, p, Circle.smul_def] using h_inv
  · simp only [hx, ↓reduceIte]
    have hx' : x ≤ 0 := le_of_not_ge hx
    simpa [Real.fourierInv_eq, hx', Nat.one_le_iff_ne_zero.mp hk, g, p, Circle.smul_def] using h_inv

/-- Laplace's inverse Fourier integral for `1 / Γ` at `x ≥ 0`: for `k ≥ 1` and `0 ≤ x`,
`∫ z : ℝ, 𝐞 (x * z) * ((1 + 2πiz) ^ (k + 1))⁻¹ = x ^ k * exp (-x) / k!`. -/
theorem integral_fourierChar_mul_inv_pow {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 ≤ x) :
    ∫ z : ℝ, 𝐞 (x * z) * ((1 + 2 * π * Complex.I * z : ℂ) ^ (k + 1))⁻¹ =
      (x : ℂ) ^ k * Complex.exp (-x) / k ! := by
  simpa [hx] using integral_fourierChar_mul_inv_pow_eq_ite hk x

/-- Vanishing of Laplace's inverse Fourier integral for `x ≤ 0` and `k ≥ 1`. -/
theorem integral_fourierChar_mul_inv_pow_of_nonpos {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ≤ 0) :
    ∫ z : ℝ, 𝐞 (x * z) * ((1 + 2 * π * Complex.I * z : ℂ) ^ (k + 1))⁻¹ = 0 := by
  rw [integral_fourierChar_mul_inv_pow_eq_ite hk x]
  split_ifs with h
  · obtain rfl : x = 0 := le_antisymm hx h
    simp [Nat.one_le_iff_ne_zero.mp hk]
  · rfl

/-- For `n ≥ 2` and `a ≥ 0`, the inverse Fourier integral of the `n`-th power of the complex
Gaussian integral `∫ w : ℂ, exp (-(1 + 2πit) ‖w‖²)` equals
`π ^ n / (n - 1)! * a ^ (n - 1) * exp (-a)`. -/
theorem integral_fourierChar_mul_gaussian_pow {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 0 ≤ a) :
    ∫ t : ℝ, 𝐞 (a * t) * (∫ w : ℂ, Complex.exp (-(1 + 2 * π * Complex.I * t) * ‖w‖ ^ 2)) ^ n =
      (π : ℂ) ^ n / (n - 1)! * (a : ℂ) ^ (n - 1) * Complex.exp (-a) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 1 := ⟨n - 1, by omega⟩
  have h_gauss (t : ℝ) : ∫ w : ℂ, Complex.exp (-(1 + 2 * π * Complex.I * t) * ‖w‖ ^ 2) =
      π * (1 + 2 * π * Complex.I * t)⁻¹ := by
    rw [GaussianFourier.integral_cexp_neg_mul_sq_norm (by simp)]
    simp [Complex.finrank_real_complex, division_def]
  simp_rw [h_gauss, mul_pow, inv_pow, mul_left_comm _ ((π : ℂ) ^ (k + 1)), integral_const_mul,
    integral_fourierChar_mul_inv_pow (show 1 ≤ k by omega) ha, Nat.add_sub_cancel]
  ring

end TauCeti
