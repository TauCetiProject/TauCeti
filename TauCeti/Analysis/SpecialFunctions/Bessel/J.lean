/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Power series and circle integrals of the Bessel function `J_ν`

Mathlib defines the Bessel function of the first kind `Complex.besselJ ν z` as
`(z / 2) ^ ν * ₀F₁(; ν + 1; -(z / 2) ^ 2)`, where `₀F₁` is the regularized hypergeometric function
`Complex.regularizedHGFun 0 {ν + 1}`. This file proves its everywhere-convergent power series for
arbitrary complex order and argument and derives the Hansen–Bessel circle integrals for integer
orders together with the order-zero Bessel integral on `[0, 2π]`, which evaluates the angular
integral in polar-coordinate representations of squared Airy integrals.

Because Mathlib's `Complex.Gamma` vanishes at nonpositive integers, the power series
`∑ⱼ (-1) ^ j * (z / 2) ^ (2 j + ν) / (j! Γ(j + ν + 1))` converges absolutely to
`Complex.besselJ ν z` for every `ν, z : ℂ` without exception, including at `z = 0`. Combining the
factorial series for natural orders with the Fourier-series expansion
`Complex.hasSum_integral_exp_mul_cos_mul_exp` of `θ ↦ e^{w cos θ}` on `[-π, π]` from
`TauCeti.Analysis.SpecialFunctions.Integrals.Basic` yields
`∫_{-π}^π e^{i z cos θ} e^{i n θ} dθ = 2π i^n J_n(z)` for all `n : ℤ`, its period-shift form on
`[a, a + 2π]`, and the order-zero Bessel integral `J_0(z) = (2π)⁻¹ ∫_0^{2π} e^{i z cos θ} dθ`. The
power-series and circle-integral arguments adapt the real modified-Bessel proofs
(`Real.hasSum_besselI`, `Real.hasSum_besselI_natCast`, and `Real.integral_exp_mul_cos_mul_cexp`) in
`TauCeti.Analysis.SpecialFunctions.Bessel.I`.

## Main declarations

* `Complex.besselJ_zero_zero`, `Complex.analyticAt_besselJ_natCast`,
  `Complex.analyticAt_besselJ_zero_left` — value at `(0, 0)` and `@[fun_prop]` analyticity bridges
  for natural orders `n : ℕ` and order `0`.
* `Complex.hasSum_besselJ`, `Complex.summable_norm_besselJ`, `Complex.besselJ_eq_tsum` — the power
  series `∑ⱼ (-1) ^ j * (z / 2) ^ (2 j + ν) / (j! Γ(j + ν + 1))` converges absolutely to
  `besselJ ν z` for every `ν, z : ℂ` (DLMF 10.2.2).
* `Complex.hasSum_besselJ_natCast`, `Complex.hasSum_besselJ_zero_left` — the factorial power series
  for natural orders `n : ℕ` and order `0`.
* `Complex.I_zpow_mul_besselJ_int_eq_natAbs` — integer-order reflection symmetry
  `i^n J_n(z) = i^{|n|} J_{|n|}(z)` for `n : ℤ` and `z : ℂ`.
* `Complex.integral_exp_I_mul_cos_mul_exp`, `Complex.integral_exp_I_mul_cos_mul_exp_add_two_pi` —
  the Hansen–Bessel circle integrals `∫_{-π}^π e^{i z cos θ} e^{i n θ} dθ = 2π i^n J_n(z)` and
  `∫_a^{a + 2π} e^{i z cos θ} e^{i n θ} dθ = 2π i^n J_n(z)` for `n : ℤ` and `z : ℂ`.
* `Complex.integral_exp_I_mul_cos_zero_two_pi`,
  `Complex.besselJ_zero_left_eq_integral_exp_I_mul_cos` — the order-zero Bessel integral
  `J_0(z) = (2π)⁻¹ ∫_0^{2π} e^{i z cos θ} dθ` for every `z : ℂ` (DLMF 10.9.1).

## References

* *NIST Digital Library of Mathematical Functions*, [§10.2(ii)](https://dlmf.nist.gov/10.2.ii) and
  [§10.9(i)](https://dlmf.nist.gov/10.9.i).
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §§2.1–2.2.
* `TauCeti.Analysis.SpecialFunctions.Bessel.I` and
  `TauCeti.Analysis.SpecialFunctions.Integrals.Basic`, whose real modified-Bessel series and
  termwise circle-integral arguments this file adapts to `Complex.besselJ`.
-/

public section

noncomputable section

open scoped Nat Real

namespace Complex

/-! ### Power series -/

/-- `J_0(0) = 1`. -/
@[simp]
theorem besselJ_zero_zero : besselJ 0 0 = 1 := by
  simp [besselJ_zero]

/-- `J_n` is analytic on `ℂ` for every natural order `n : ℕ`. -/
@[fun_prop]
theorem analyticAt_besselJ_natCast (n : ℕ) (z : ℂ) : AnalyticAt ℂ (besselJ n) z := by
  simpa using analyticAt_besselJ_int (n : ℤ) z

/-- `J_0` is analytic on `ℂ`. -/
@[fun_prop]
theorem analyticAt_besselJ_zero_left (z : ℂ) : AnalyticAt ℂ (besselJ 0) z := by
  simpa using analyticAt_besselJ_int 0 z

private theorem besselJ_series_term_zero (ν : ℂ) {j : ℕ} (hj : j ≠ 0) :
    (-1 : ℂ) ^ j * (0 : ℂ) ^ (2 * j + ν) / (j ! * Gamma (j + ν + 1)) = 0 := by
  -- If the exponent `2 j + ν` vanishes with `j ≥ 1`, then `j + ν + 1 = 1 - j ≤ 0`, where
  -- `Complex.Gamma` vanishes.
  by_cases h : (2 : ℂ) * j + ν = 0
  · have harg : (j : ℂ) + ν + 1 = -((j - 1 : ℕ) : ℂ) := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hj), Nat.cast_one]
      linear_combination h
    rw [harg, Gamma_neg_nat_eq_zero, mul_zero, div_zero]
  · rw [zero_cpow h, mul_zero, zero_div]

private theorem besselJ_series_term_eq_mul_regularizedHGFunCoeff (ν : ℂ) {z : ℂ} (hz : z ≠ 0)
    (j : ℕ) :
    (-1 : ℂ) ^ j * (z / 2) ^ (2 * j + ν) / (j ! * Gamma (j + ν + 1)) =
      (z / 2) ^ ν * (regularizedHGFunCoeff 0 {ν + 1} j * (-(z / 2) ^ 2) ^ j) := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hexp : (2 : ℂ) * j + ν = ν + ((2 * j : ℕ) : ℂ) := by push_cast; ring
  have hadd : (j : ℂ) + ν + 1 = ν + 1 + j := by ring
  rw [hexp, cpow_add _ _ hz2, cpow_natCast, pow_mul, regularizedHGFunCoeff_zero_singleton, hadd,
    neg_pow ((z / 2) ^ 2) j]
  ring

/-- **Power series of `J_ν(z)`** (DLMF 10.2.2): for every complex order `ν` and argument `z`,
`besselJ ν z = ∑ⱼ (-1) ^ j * (z / 2) ^ (2 j + ν) / (j! Γ(j + ν + 1))`, including at `z = 0`
(since `Complex.Gamma` is totalized to `0` at nonpositive integers). -/
theorem hasSum_besselJ (ν z : ℂ) :
    HasSum (fun j : ℕ => (-1 : ℂ) ^ j * (z / 2) ^ (2 * j + ν) / (j ! * Gamma (j + ν + 1)))
      (besselJ ν z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · refine (hasSum_ite_eq 0 (besselJ ν 0)).congr_fun fun j => ?_
    rcases eq_or_ne j 0 with rfl | hj
    · by_cases hν : ν = 0 <;> simp [besselJ_zero, hν]
    · simp [hj, besselJ_series_term_zero ν hj]
  · simp_rw [besselJ_series_term_eq_mul_regularizedHGFunCoeff ν hz, besselJ]
    exact (hasSum_regularizedHGFun (a := 0) (b := {ν + 1}) (by simp) (-(z / 2) ^ 2)).mul_left
      ((z / 2) ^ ν)

/-- The power series of `besselJ ν z` converges absolutely at every `ν, z : ℂ`. -/
theorem summable_norm_besselJ (ν z : ℂ) :
    Summable fun j : ℕ =>
      ‖(-1 : ℂ) ^ j * (z / 2) ^ (2 * j + ν) / (j ! * Gamma (j + ν + 1))‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · refine summable_of_ne_finset_zero (s := {0}) fun j hj => ?_
    simp [besselJ_series_term_zero ν (Finset.notMem_singleton.mp hj)]
  · simp_rw [besselJ_series_term_eq_mul_regularizedHGFunCoeff ν hz]
    simp only [norm_mul ((z / 2) ^ ν)]
    exact (summable_norm_regularizedHGFun (a := 0) (b := {ν + 1}) (by simp)
      (-(z / 2) ^ 2)).mul_left ‖(z / 2) ^ ν‖

/-- `besselJ ν z` as a `tsum` over `ℕ`, valid for every `ν, z : ℂ`. -/
theorem besselJ_eq_tsum (ν z : ℂ) :
    besselJ ν z =
      ∑' j : ℕ, (-1 : ℂ) ^ j * (z / 2) ^ (2 * j + ν) / (j ! * Gamma (j + ν + 1)) :=
  (hasSum_besselJ ν z).tsum_eq.symm

/-- For a natural order `n`, `J_n(z) = ∑ⱼ (-1) ^ j * (z / 2) ^ (2 j + n) / (j! (j + n)!)` at every
`z : ℂ`. -/
theorem hasSum_besselJ_natCast (n : ℕ) (z : ℂ) :
    HasSum (fun j : ℕ => (-1 : ℂ) ^ j * (z / 2) ^ (2 * j + n) / (j ! * (j + n)!))
      (besselJ n z) := by
  simpa only [← Nat.cast_ofNat (R := ℂ) (n := 2), ← Nat.cast_mul, ← Nat.cast_add, cpow_natCast,
    Gamma_nat_eq_factorial] using hasSum_besselJ (n : ℂ) z

/-- Power series of `J_0(z)`: `J_0(z) = ∑ⱼ (-1) ^ j * (z / 2) ^ (2 j) / (j!)²` at every `z : ℂ`. -/
theorem hasSum_besselJ_zero_left (z : ℂ) :
    HasSum (fun j : ℕ => (-1 : ℂ) ^ j * (z / 2) ^ (2 * j) / (j ! : ℂ) ^ 2) (besselJ 0 z) := by
  simpa only [Nat.cast_zero, add_zero, sq] using hasSum_besselJ_natCast 0 z

/-! ### Hansen–Bessel circle integrals and the order-zero Bessel integral -/

/-- For every integer `n` and `z : ℂ`, `i^n J_n(z) = i^{|n|} J_{|n|}(z)`. -/
theorem I_zpow_mul_besselJ_int_eq_natAbs (n : ℤ) (z : ℂ) :
    I ^ n * besselJ n z = I ^ n.natAbs * besselJ n.natAbs z := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp
  · rw [Int.cast_neg, besselJ_neg_int]
    simp [← mul_assoc, ← inv_pow, ← mul_pow]

/-- **Hansen–Bessel circle integral**: for every `z : ℂ` and `n : ℤ`,
`∫_{-π}^π e^{i z cos θ} e^{i n θ} dθ = 2π i^n J_n(z)`. -/
theorem integral_exp_I_mul_cos_mul_exp (z : ℂ) (n : ℤ) :
    ∫ θ in -π..π, exp (I * z * Real.cos θ) * exp (n * θ * I) =
      2 * π * I ^ n * besselJ n z := by
  rw [mul_assoc (2 * (π : ℂ)), I_zpow_mul_besselJ_int_eq_natAbs, ← mul_assoc]
  refine (hasSum_integral_exp_mul_cos_mul_exp (I * z) n).unique ?_
  refine ((hasSum_besselJ_natCast n.natAbs z).mul_left
    (2 * (π : ℂ) * I ^ n.natAbs)).congr_fun fun j => ?_
  have hIpow : I ^ (2 * j + n.natAbs) = (-1 : ℂ) ^ j * I ^ n.natAbs := by
    rw [pow_add, pow_mul, I_sq]
  rw [mul_div_assoc, mul_pow, hIpow]
  ring

/-- **Hansen–Bessel circle integral over any period `[a, a + 2π]`**:
`∫_a^{a + 2π} e^{i z cos θ} e^{i n θ} dθ = 2π i^n J_n(z)`. -/
theorem integral_exp_I_mul_cos_mul_exp_add_two_pi (z : ℂ) (n : ℤ) (a : ℝ) :
    ∫ θ in a..a + 2 * π, exp (I * z * Real.cos θ) * exp (n * θ * I) =
      2 * π * I ^ n * besselJ n z := by
  have hper : Function.Periodic (fun θ : ℝ => exp (I * z * Real.cos θ) * exp (n * θ * I))
      (2 * π) := fun θ => by
    have hexp : exp ((n : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I) = exp (n * θ * I) := by
      have hsplit : (n : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I =
          n * θ * I + n * (2 * π * I) := by push_cast; ring
      rw [hsplit, exp_add, exp_int_mul, exp_two_pi_mul_I, one_zpow, mul_one]
    simp only [Real.cos_add_two_pi, hexp]
  rw [hper.intervalIntegral_add_eq a (-π)]
  have hpi : -π + 2 * π = π := by ring
  rw [hpi, integral_exp_I_mul_cos_mul_exp]

/-- For every `z : ℂ`, `∫_0^{2π} e^{i z cos θ} dθ = 2π J_0(z)`. -/
theorem integral_exp_I_mul_cos_zero_two_pi (z : ℂ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (I * z * Real.cos θ) = 2 * π * besselJ 0 z := by
  simpa using integral_exp_I_mul_cos_mul_exp_add_two_pi z 0 0

/-- **The Bessel integral for `J_0`** (DLMF 10.9.1): for every `z : ℂ`,
`J_0(z) = (2π)⁻¹ ∫_0^{2π} e^{i z cos θ} dθ`. -/
theorem besselJ_zero_left_eq_integral_exp_I_mul_cos (z : ℂ) :
    besselJ 0 z = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, exp (I * z * Real.cos θ) := by
  have h2pi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [integral_exp_I_mul_cos_zero_two_pi, inv_mul_cancel_left₀ h2pi]

end Complex
