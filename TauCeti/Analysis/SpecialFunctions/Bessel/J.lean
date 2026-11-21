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
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Power series and circle integrals for `Complex.besselJ`

Mathlib defines the Bessel function of the first kind `Complex.besselJ ν z` through the regularized
hypergeometric function `₀F₁`, establishes its parity and `J_{-n}(z) = (-1)^n J_n(z)` for integer
orders, and proves analyticity on `Complex.slitPlane` (and on all of `ℂ` for integer orders).

This file develops the power series and full-period circle integrals of `Complex.besselJ`,
paralleling the real modified-Bessel development in
`TauCeti/Analysis/SpecialFunctions/Bessel/I.lean`:

* Power series: `Complex.hasSum_besselJ` expresses `J_ν(z)` as its alternating power series
  `∑ⱼ (-1)^j (z / 2)^(2 j + ν) / (j! Γ(j + ν + 1))` at every `(ν, z)` without restriction,
  specializing to natural orders (`Complex.hasSum_besselJ_natCast`) and to order zero
  (`Complex.hasSum_besselJ_zero_left`).
* Circle integrals: the full-period Hansen–Bessel representation
  `∫_{-π}^{π} e^{i z cos θ} e^{i n θ} dθ = 2 π i^n J_n(z)` for every `z ∈ ℂ` and `n ∈ ℤ`
  (`Complex.integral_exp_I_mul_cos_mul_exp`) and its `[0, 2π]` form
  (`Complex.integral_zero_two_pi_exp_I_mul_cos_mul_exp`), proved via the shared Fourier-series
  evaluation `Complex.hasSum_pow_div_factorial_integral_exp_mul_cos_mul_cexp`. At order zero these
  give Bessel's integral for `J₀`: `∫_{-π}^{π} e^{i a cos θ} dθ = 2 π J_0(a)`
  (`Complex.integral_exp_mul_cos_mul_I`) and `J_0(a) = (2π)⁻¹ ∫_0^{2π} e^{i a cos θ} dθ`
  (`Complex.besselJ_zero_left_eq_integral`), DLMF 10.9.1 at `n = 0`. The right side is the
  average of the plane wave `e^{i a cos φ}` over all directions, so in polar coordinates it
  reduces a plane integral of `e^{i r cos φ}` times a radial weight to a one-dimensional integral
  against `J₀(r)`; this is how the representation DLMF 9.11.3 of the square of the Airy function
  is derived.

## Main results

* `Complex.hasSum_besselJ`, `Complex.hasSum_besselJ_natCast`, `Complex.hasSum_besselJ_zero_left`
* `Complex.integral_exp_I_mul_cos_mul_exp`, `Complex.integral_zero_two_pi_exp_I_mul_cos_mul_exp`
* `Complex.integral_exp_mul_cos_mul_I`, `Complex.besselJ_zero_left_eq_integral`

## References

* NIST *Digital Library of Mathematical Functions*, §§10.2, 10.9,
  <https://dlmf.nist.gov/10.2>, <https://dlmf.nist.gov/10.9>.
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §2.2.
-/

public section

noncomputable section

open scoped Nat Real

namespace Complex

/-! ### Power series -/

/-- `J_ν(z)` is the sum of its alternating power series
`∑ⱼ (-1)^j (z / 2)^(2 j + ν) / (j! Γ(j + ν + 1))` at every complex order `ν` and argument `z`,
including `z = 0` and the nonpositive integer poles of `Γ(j + ν + 1)` (DLMF 10.2.2). -/
theorem hasSum_besselJ (ν z : ℂ) :
    HasSum (fun j : ℕ => (-1) ^ j * (z / 2) ^ (2 * j + ν) / (j ! * Gamma (j + ν + 1)))
      (besselJ ν z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [besselJ_zero]
    split_ifs with hν
    · subst hν
      convert hasSum_ite_eq 0 (1 : ℂ) using 1
      ext j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · have hj0 : 2 * (j : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hj.ne')
        simp [hj.ne', zero_cpow hj0]
    · convert hasSum_zero with j
      rw [zero_div]
      by_cases h : 2 * (j : ℂ) + ν = 0
      · have hj0 : j ≠ 0 := by
          rintro rfl
          exact hν (by simpa using h)
        have hj : (j : ℂ) + ν + 1 = -((j - 1 : ℕ) : ℂ) := by
          have h1 : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
          have h2 : ((j - 1 : ℕ) : ℂ) = (j : ℂ) - 1 := by simp [Nat.cast_sub h1]
          rw [h2]
          linear_combination h
        simp [hj, Gamma_neg_nat_eq_zero]
      · simp [zero_cpow h]
  · have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
    have hcast (j : ℕ) : 2 * (j : ℂ) + ν = ν + ((2 * j : ℕ) : ℂ) := by
      push_cast
      ring
    have hadd (j : ℕ) : (j : ℂ) + ν + 1 = ν + 1 + j := by ring
    rw [besselJ_def]
    convert (hasSum_regularizedHGFun (a := 0) (b := {ν + 1}) (by simp) (-(z / 2) ^ 2)).mul_left
      ((z / 2) ^ ν) using 2 with j
    have hneg : (-(z / 2) ^ 2) ^ j = (-1) ^ j * (z / 2) ^ (2 * j) := by
      rw [neg_eq_neg_one_mul, mul_pow, ← pow_mul]
    rw [regularizedHGFunCoeff_zero_singleton, hcast, cpow_add _ _ hz2, cpow_natCast, hneg, hadd]
    ring

/-- For a natural order `n`, `J_n(z)` is the sum of its power series
`∑ⱼ (-1)^j (z / 2)^(2 j + n) / (j! (j + n)!)` at every `z ∈ ℂ`. -/
theorem hasSum_besselJ_natCast (n : ℕ) (z : ℂ) :
    HasSum (fun j : ℕ => (-1) ^ j * (z / 2) ^ (2 * j + n) / (j ! * (j + n)!))
      (besselJ n z) := by
  simpa only [← Nat.cast_ofNat (R := ℂ) (n := 2), ← Nat.cast_mul, ← Nat.cast_add, cpow_natCast,
    Gamma_nat_eq_factorial] using hasSum_besselJ (n : ℂ) z

/-- `J_0(z)` is the sum of its power series `∑ⱼ (-1)^j (z / 2)^(2 j) / (j!)^2` at every `z ∈ ℂ`. -/
theorem hasSum_besselJ_zero_left (z : ℂ) :
    HasSum (fun j : ℕ => (-1) ^ j * (z / 2) ^ (2 * j) / (j ! : ℂ) ^ 2)
      (besselJ 0 z) := by
  simpa only [Nat.cast_zero, add_zero, sq] using hasSum_besselJ_natCast 0 z

/-! ### Circle-integral representations -/

/-- **Full-period Hansen–Bessel integral.** For every complex argument `z` and integer order `n`,
`∫_{-π}^{π} e^{i z cos θ} e^{i n θ} dθ = 2 π i^n J_n(z)`. -/
theorem integral_exp_I_mul_cos_mul_exp (z : ℂ) (n : ℤ) :
    ∫ θ in -π..π, exp (I * z * Real.cos θ) * exp (n * θ * I) =
      2 * π * I ^ n * besselJ n z := by
  have hsym : I ^ n * besselJ n z = I ^ n.natAbs * besselJ n.natAbs z := by
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simp
    · rw [Int.cast_neg, besselJ_neg_int, Int.cast_natCast, Int.natAbs_neg, Int.natAbs_natCast]
      have hI : I ^ (-(m : ℤ)) * (-1 : ℂ) ^ (m : ℤ) = I ^ m := by
        simp [← inv_pow, ← mul_pow]
      linear_combination besselJ m z * hI
  rw [mul_assoc, hsym, ← mul_assoc]
  refine (hasSum_pow_div_factorial_integral_exp_mul_cos_mul_cexp (I * z) n).unique ?_
  convert (hasSum_besselJ_natCast n.natAbs z).mul_left (2 * (π : ℂ) * I ^ n.natAbs) using 2 with l
  have hdiv : I * z / 2 = I * (z / 2) := mul_div_assoc I z 2
  have hI : I ^ (2 * l + n.natAbs) = (-1) ^ l * I ^ n.natAbs := by
    rw [pow_add, pow_mul, I_sq]
  rw [hdiv, mul_pow, hI]
  ring

/-- Over `[0, 2π]`, `∫_0^{2π} e^{i z cos θ} e^{i n θ} dθ = 2 π i^n J_n(z)`. -/
theorem integral_zero_two_pi_exp_I_mul_cos_mul_exp (z : ℂ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (I * z * Real.cos θ) * exp (n * θ * I) =
      2 * π * I ^ n * besselJ n z := by
  have hper : Function.Periodic (fun θ : ℝ => exp (I * z * Real.cos θ) * exp (n * θ * I))
      (2 * π) := by
    intro θ
    have hexp : exp (n * ((θ + 2 * π : ℝ) : ℂ) * I) = exp (n * θ * I) := by
      have hsplit : (n : ℂ) * ((θ + 2 * π : ℝ) : ℂ) * I = n * θ * I + n * (2 * π * I) := by
        push_cast
        ring
      rw [hsplit, exp_add, exp_int_mul_two_pi_mul_I, mul_one]
    simp only [Real.cos_periodic θ, hexp]
  have hpi : -π + 2 * π = π := by ring
  have hshift := hper.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, hpi, integral_exp_I_mul_cos_mul_exp] at hshift
  exact hshift

/-- **Bessel's integral for `J₀`, symmetric form.** For every complex `a`,
`∫_{-π}^{π} e^{i a cos θ} dθ = 2π J₀(a)`. -/
theorem integral_exp_mul_cos_mul_I (a : ℂ) :
    ∫ θ in -π..π, exp (a * Real.cos θ * I) = 2 * π * besselJ 0 a := by
  simpa only [Int.cast_zero, zero_mul, exp_zero, mul_one, zpow_zero, mul_comm I a,
    mul_right_comm a I] using integral_exp_I_mul_cos_mul_exp a 0

/-- **Bessel's integral for `J₀`.** For every complex `a`,
`J₀(a) = (2π)⁻¹ ∫₀^{2π} e^{i a cos θ} dθ` (DLMF 10.9.1). -/
theorem besselJ_zero_left_eq_integral (a : ℂ) :
    besselJ 0 a = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, exp (a * Real.cos θ * I) := by
  have h2pi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have h := integral_zero_two_pi_exp_I_mul_cos_mul_exp a 0
  simp only [Int.cast_zero, zero_mul, exp_zero, mul_one, zpow_zero, mul_comm I a,
    mul_right_comm a I] at h
  rw [h, inv_mul_cancel_left₀ h2pi]

end Complex
