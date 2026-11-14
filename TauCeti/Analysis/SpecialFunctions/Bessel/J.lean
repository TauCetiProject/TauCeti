/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Power series, derivatives, and Bessel's integrals for `Complex.besselJ`

Mathlib defines the Bessel function of the first kind `Complex.besselJ ν z` through the regularized
hypergeometric function `₀F₁`, establishes its parity and `J_{-n}(z) = (-1)^n J_n(z)` for integer
orders, proves analyticity on `Complex.slitPlane` (and on all of `ℂ` for integer orders), and
proves the three-term recurrence `2 ν J_ν(z) = z J_{ν-1}(z) + z J_{ν+1}(z)`.

This file develops the power series, complex derivatives, and circle and half-period integral
representations of `Complex.besselJ`, together with the resulting magnitude bounds for integer
orders:

* Power series and Schwarz reflection: `Complex.hasSum_besselJ` expresses `J_ν(z)` as its
  alternating power series `∑ⱼ (-1)^j (z / 2)^(2 j + ν) / (j! Γ(j + ν + 1))` at every `(ν, z)`
  without restriction, specializing to natural orders (`Complex.hasSum_besselJ_natCast`) and to
  order zero (`Complex.hasSum_besselJ_zero_left`). For integer orders, `J_n` commutes with complex
  conjugation (`Complex.conj_besselJ_int`) and takes real values on `ℝ`
  (`Complex.besselJ_int_ofReal_im`).
* Bessel's integrals: the full-period Hansen–Bessel representation
  `∫_{-π}^{π} e^{i z cos θ} e^{i n θ} dθ = 2 π i^n J_n(z)` for every `z ∈ ℂ` and `n ∈ ℤ`
  (`Complex.integral_exp_I_mul_cos_mul_exp`), its shift to any period `[c, c + 2π]`, the
  half-period Hansen–Bessel cosine form (`Complex.besselJ_int_eq_integral_exp_I_mul_cos_mul_cos`),
  and Bessel's first integral `J_n(z) = π⁻¹ ∫_0^π cos(z sin θ - n θ) dθ`
  (`Complex.besselJ_int_eq_integral_cos_sin_sub`). At `n = 0`, these specialize to
  `J_0(z) = (2π)⁻¹ ∫_0^{2π} e^{i z cos θ} dθ`
  (`Complex.besselJ_zero_left_eq_integral_exp_I_mul_cos`) and the half- and quarter-period cosine
  integrals of `J_0`.
* Magnitude bounds: `‖J_n(z)‖ ≤ exp |Im z|` (`Complex.norm_besselJ_int_le_exp_abs_im`) and
  `‖J_n(x)‖ ≤ 1` for real `x` (`Complex.norm_besselJ_int_ofReal_le_one`).
* Complex derivatives and antiderivatives:
  `J_ν'(z) = (J_{ν-1}(z) - J_{ν+1}(z)) / 2 = (ν / z) J_ν(z) - J_{ν+1}(z)` on `Complex.slitPlane`
  (`Complex.hasDerivAt_besselJ`, `Complex.hasDerivAt_besselJ_eq_div_sub`), extending across the
  entire complex plane for integer orders (`Complex.hasDerivAt_besselJ_int`), with
  `J_0'(z) = -J_1(z)` (`Complex.hasDerivAt_besselJ_zero_left`),
  `(z^(n+1) J_{n+1}(z))' = z^(n+1) J_n(z)` (`Complex.hasDerivAt_pow_mul_besselJ_natCast`,
  `Complex.hasDerivAt_mul_besselJ_one_left`), and the corresponding definite integrals
  (`Complex.integral_pow_mul_besselJ_natCast`, `Complex.integral_mul_besselJ_zero_left`).

## Main results

* `Complex.hasSum_besselJ`, `Complex.hasSum_besselJ_natCast`, `Complex.hasSum_besselJ_zero_left`
* `Complex.conj_besselJ_int`, `Complex.besselJ_int_ofReal_im`
* `Complex.integral_exp_I_mul_cos_mul_exp`, `Complex.integral_exp_mul_cos_mul_exp`,
  `Complex.integral_add_two_pi_exp_I_mul_cos_mul_exp`,
  `Complex.integral_zero_two_pi_exp_I_mul_cos_mul_exp`
* `Complex.integral_zero_pi_exp_I_mul_cos_mul_cos`,
  `Complex.besselJ_int_eq_integral_exp_I_mul_cos_mul_cos`
* `Complex.integral_add_two_pi_exp_I_mul_sin_sub`, `Complex.integral_zero_two_pi_exp_I_mul_sin_sub`,
  `Complex.integral_zero_pi_cos_sin_sub`, `Complex.besselJ_int_eq_integral_cos_sin_sub`
* `Complex.besselJ_zero_left_eq_integral_exp_I_mul_cos`,
  `Complex.integral_zero_two_pi_exp_I_mul_cos`, `Complex.integral_neg_pi_pi_exp_I_mul_cos`,
  `Complex.besselJ_zero_left_eq_integral_cos_cos`, `Complex.besselJ_zero_left_eq_integral_cos_sin`,
  `Complex.besselJ_zero_left_eq_integral_zero_pi_div_two_cos_sin`,
  `Complex.besselJ_zero_left_eq_integral_zero_pi_div_two_cos_cos`
* `Complex.norm_besselJ_int_le_exp_abs_im`, `Complex.norm_besselJ_int_ofReal_le_one`
* `Complex.hasDerivAt_besselJ_eq_div_sub`, `Complex.hasDerivAt_besselJ`, `Complex.deriv_besselJ`,
  `Complex.hasDerivAt_besselJ_int`, `Complex.deriv_besselJ_int`,
  `Complex.hasDerivAt_besselJ_zero_left`, `Complex.deriv_besselJ_zero_left`,
  `Complex.hasDerivAt_pow_mul_besselJ_natCast`, `Complex.hasDerivAt_mul_besselJ_one_left`,
  `Complex.integral_pow_mul_besselJ_natCast`, `Complex.integral_mul_besselJ_zero_left`

## References

* *NIST Digital Library of Mathematical Functions*, §10.2 (definition and power series),
  §10.6 (recurrence relations and derivatives), §10.9 (integral representations),
  §10.14 (inequalities), and §10.22 (integrals).
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Nat Real Topology

namespace Complex

/-! ### Power series and Schwarz reflection -/

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
        rw [hj, Gamma_neg_nat_eq_zero, mul_zero, div_zero]
      · rw [zero_cpow h, mul_zero, zero_div]
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

/-- Schwarz reflection for integer-order Bessel functions: `conj (J_n(z)) = J_n(conj z)`. -/
theorem conj_besselJ_int (n : ℤ) (z : ℂ) :
    starRingEnd ℂ (besselJ n z) = besselJ n (starRingEnd ℂ z) := by
  have hnat (m : ℕ) : starRingEnd ℂ (besselJ m z) = besselJ m (starRingEnd ℂ z) := by
    refine ((hasSum_besselJ_natCast m z).star).unique ?_
    convert hasSum_besselJ_natCast m (starRingEnd ℂ z) using 1
    ext j
    simp [RCLike.star_def]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using hnat m
  · rw [Int.cast_neg, besselJ_neg_int, besselJ_neg_int, Int.cast_natCast, map_mul, hnat m]
    simp

/-- At real arguments, integer-order Bessel functions `J_n(x)` are real-valued. -/
@[simp]
theorem besselJ_int_ofReal_im (n : ℤ) (x : ℝ) : (besselJ n x).im = 0 :=
  conj_eq_iff_im.mp (by simpa using conj_besselJ_int n x)

/-! ### Bessel's integral representations -/

private theorem integral_exp_I_mul_cos_mul_exp_natCast (z : ℂ) (n : ℕ) :
    ∫ θ in -π..π, exp (I * z * Real.cos θ) * exp (n * θ * I) =
      2 * π * I ^ n * besselJ n z := by
  refine (hasSum_pow_div_factorial_integral_exp_mul_cos_mul_exp (I * z) n).unique ?_
  convert (hasSum_besselJ_natCast n z).mul_left (2 * (π : ℂ) * I ^ n) using 2 with l
  have hdiv : I * z / 2 = I * (z / 2) := mul_div_assoc I z 2
  have hI : I ^ (2 * l + n) = (-1) ^ l * I ^ n := by
    rw [pow_add, pow_mul, I_sq]
  rw [hdiv, mul_pow, hI]
  ring

/-- **Full-period Hansen–Bessel integral.** For every complex argument `z` and integer order `n`,
`∫_{-π}^{π} e^{i z cos θ} e^{i n θ} dθ = 2 π i^n J_n(z)`. -/
theorem integral_exp_I_mul_cos_mul_exp (z : ℂ) (n : ℤ) :
    ∫ θ in -π..π, exp (I * z * Real.cos θ) * exp (n * θ * I) =
      2 * π * I ^ n * besselJ n z := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using integral_exp_I_mul_cos_mul_exp_natCast z m
  · have h := intervalIntegral.integral_comp_neg (a := -π) (b := π)
      (fun θ : ℝ => exp (I * z * Real.cos θ) * exp (m * θ * I))
    rw [neg_neg, integral_exp_I_mul_cos_mul_exp_natCast] at h
    have hI : I ^ (-(m : ℤ)) * (-1 : ℂ) ^ (m : ℤ) = I ^ m := by
      rw [zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, inv_I, ← mul_pow]
      simp
    have hrhs : 2 * (π : ℂ) * I ^ (-(m : ℤ)) * besselJ ((-(m : ℤ) : ℤ) : ℂ) z =
        2 * π * I ^ m * besselJ m z := by
      rw [Int.cast_neg, besselJ_neg_int, Int.cast_natCast]
      linear_combination 2 * (π : ℂ) * besselJ m z * hI
    rw [hrhs, ← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [Real.cos_neg, ofReal_neg, Int.cast_neg, Int.cast_natCast]
    ring_nf

/-- For any complex `z` and integer `n`, the `n`-th Fourier integral of `θ ↦ e^{z cos θ}` over
`[-π, π]` is `2 π i^n J_n(-i z)`. -/
theorem integral_exp_mul_cos_mul_exp (z : ℂ) (n : ℤ) :
    ∫ θ in -π..π, exp (z * Real.cos θ) * exp (n * θ * I) =
      2 * π * I ^ n * besselJ n (-I * z) := by
  have hz : I * (-I * z) = z := by
    rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  simpa only [hz] using integral_exp_I_mul_cos_mul_exp (-I * z) n

/-- Over any period `[c, c + 2π]`, `∫_c^{c + 2π} e^{i z cos θ} e^{i n θ} dθ = 2 π i^n J_n(z)`. -/
theorem integral_add_two_pi_exp_I_mul_cos_mul_exp (z : ℂ) (n : ℤ) (c : ℝ) :
    ∫ θ in c..c + 2 * π, exp (I * z * Real.cos θ) * exp (n * θ * I) =
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
  rw [hper.intervalIntegral_add_eq c (-π),
    (by ring : -π + 2 * π = π), integral_exp_I_mul_cos_mul_exp]

/-- Over `[0, 2π]`, `∫_0^{2π} e^{i z cos θ} e^{i n θ} dθ = 2 π i^n J_n(z)`. -/
theorem integral_zero_two_pi_exp_I_mul_cos_mul_exp (z : ℂ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (I * z * Real.cos θ) * exp (n * θ * I) =
      2 * π * I ^ n * besselJ n z := by
  simpa using integral_add_two_pi_exp_I_mul_cos_mul_exp z n 0

/-- **Hansen–Bessel cosine integral.** For every `z ∈ ℂ` and `n ∈ ℤ`,
`∫_0^π e^{i z cos θ} cos(n θ) dθ = π i^n J_n(z)` (DLMF 10.9.2). -/
theorem integral_zero_pi_exp_I_mul_cos_mul_cos (z : ℂ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..π, exp (I * z * Real.cos θ) * Real.cos (n * θ) =
      π * I ^ n * besselJ n z := by
  let f : ℝ → ℂ := fun θ => exp (I * z * Real.cos θ) * exp (n * θ * I)
  have hint (a b : ℝ) : IntervalIntegrable f volume a b :=
    (by fun_prop : Continuous f).intervalIntegrable a b
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals (hint (-π) 0) (hint 0 π)).symm
  rw [integral_exp_I_mul_cos_mul_exp] at hsplit
  have hneg : ∫ θ in -π..0, f θ =
      ∫ θ in (0 : ℝ)..π, exp (I * z * Real.cos θ) * exp (-(n * θ * I)) := by
    have hc := intervalIntegral.integral_comp_neg f (a := 0) (b := π)
    rw [neg_zero] at hc
    rw [← hc]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [f, Real.cos_neg, ofReal_neg]
    ring_nf
  rw [hneg, ← intervalIntegral.integral_add
    ((by fun_prop : Continuous fun θ : ℝ =>
      exp (I * z * Real.cos θ) * exp (-(n * θ * I))).intervalIntegrable _ _)
    (hint 0 π)] at hsplit
  have hsum : ∫ θ in (0 : ℝ)..π,
      (exp (I * z * Real.cos θ) * exp (-(n * θ * I)) + f θ) =
      2 * ∫ θ in (0 : ℝ)..π, exp (I * z * Real.cos θ) * Real.cos (n * θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hcos : exp (n * (θ : ℂ) * I) + exp (-(n * (θ : ℂ) * I)) = 2 * Real.cos (n * θ) := by
      have harg : (n : ℂ) * θ = ((n * θ : ℝ) : ℂ) := by push_cast; ring
      rw [harg, ← neg_mul, ofReal_cos, ← two_cos]
    dsimp only [f]
    linear_combination exp (I * z * Real.cos θ) * hcos
  rw [hsum] at hsplit
  exact mul_left_cancel₀ (two_ne_zero' ℂ) (by linear_combination hsplit.symm)

/-- **Hansen–Bessel representation of `J_n`.** For every `n ∈ ℤ` and `z ∈ ℂ`,
`J_n(z) = (i^{-n} / π) ∫_0^π e^{i z cos θ} cos(n θ) dθ` (DLMF 10.9.2). -/
theorem besselJ_int_eq_integral_exp_I_mul_cos_mul_cos (n : ℤ) (z : ℂ) :
    besselJ n z = I ^ (-n) / π *
      ∫ θ in (0 : ℝ)..π, exp (I * z * Real.cos θ) * Real.cos (n * θ) := by
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : I ^ (-n) * I ^ n = 1 := zpow_neg_mul_zpow_self n I_ne_zero
  rw [integral_zero_pi_exp_I_mul_cos_mul_cos]
  have hmul : I ^ (-n) / (π : ℂ) * (π * I ^ n * besselJ n z) =
      (I ^ (-n) * I ^ n) * ((π : ℂ) / π) * besselJ n z := by ring
  rw [hmul, hI, div_self hpi, one_mul, one_mul]

/-- Over any period `[c, c + 2π]`, `∫_c^{c + 2π} e^{i (z sin θ - n θ)} dθ = 2 π J_n(z)`. -/
theorem integral_add_two_pi_exp_I_mul_sin_sub (z : ℂ) (n : ℤ) (c : ℝ) :
    ∫ θ in c..c + 2 * π, exp (I * (z * Real.sin θ - n * θ)) = 2 * π * besselJ n z := by
  set a : ℝ := π / 2 - c - 2 * π
  have hcomp := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => exp (I * (z * Real.sin θ - n * θ))) (π / 2) (a := a) (b := a + 2 * π)
  have hb : π / 2 - (a + 2 * π) = c := by simp [a]
  have ha : π / 2 - a = c + 2 * π := by dsimp only [a]; ring
  rw [hb, ha] at hcomp
  rw [← hcomp]
  have hcongr : ∫ θ in a..a + 2 * π, exp (I * (z * Real.sin (π / 2 - θ) - n * (π / 2 - θ : ℝ))) =
      I ^ (-n) * ∫ θ in a..a + 2 * π, exp (I * z * Real.cos θ) * exp (n * θ * I) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hexp : exp ((-n : ℤ) * (π / 2 * I)) = I ^ (-n) := by
      rw [exp_int_mul, exp_pi_div_two_mul_I]
    rw [Real.sin_pi_div_two_sub, ← hexp, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  rw [hcongr, integral_add_two_pi_exp_I_mul_cos_mul_exp]
  have hI : I ^ (-n) * I ^ n = 1 := zpow_neg_mul_zpow_self n I_ne_zero
  linear_combination 2 * (π : ℂ) * besselJ n z * hI

/-- Over `[0, 2π]`, `∫_0^{2π} e^{i (z sin θ - n θ)} dθ = 2 π J_n(z)`. -/
theorem integral_zero_two_pi_exp_I_mul_sin_sub (z : ℂ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (I * (z * Real.sin θ - n * θ)) = 2 * π * besselJ n z := by
  simpa using integral_add_two_pi_exp_I_mul_sin_sub z n 0

/-- **Bessel's first integral, unnormalized.** For every `z ∈ ℂ` and `n ∈ ℤ`,
`∫_0^π cos(z sin θ - n θ) dθ = π J_n(z)` (DLMF 10.9.2). -/
theorem integral_zero_pi_cos_sin_sub (z : ℂ) (n : ℤ) :
    ∫ θ in (0 : ℝ)..π, cos (z * Real.sin θ - n * θ) = π * besselJ n z := by
  let g : ℝ → ℂ := fun θ => exp (I * (z * Real.sin θ - n * θ))
  have hint (a b : ℝ) : IntervalIntegrable g volume a b :=
    (by fun_prop : Continuous g).intervalIntegrable a b
  have hfull := integral_add_two_pi_exp_I_mul_sin_sub z n (-π)
  have hpi_eq : -π + 2 * π = π := by ring
  rw [hpi_eq, ← intervalIntegral.integral_add_adjacent_intervals (hint (-π) 0) (hint 0 π)] at hfull
  have hneg : ∫ θ in -π..0, g θ =
      ∫ θ in (0 : ℝ)..π, exp (-(I * (z * Real.sin θ - n * θ))) := by
    have hc := intervalIntegral.integral_comp_neg g (a := 0) (b := π)
    rw [neg_zero] at hc
    rw [← hc]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [g, Real.sin_neg, ofReal_neg]
    ring_nf
  rw [hneg, ← intervalIntegral.integral_add
    ((by fun_prop : Continuous fun θ : ℝ =>
      exp (-(I * (z * Real.sin θ - n * θ)))).intervalIntegrable _ _)
    (hint 0 π)] at hfull
  have hsum : ∫ θ in (0 : ℝ)..π, (exp (-(I * (z * Real.sin θ - n * θ))) + g θ) =
      2 * ∫ θ in (0 : ℝ)..π, cos (z * Real.sin θ - n * θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    dsimp only [g]
    rw [mul_comm I, ← neg_mul, add_comm, ← two_cos]
  rw [hsum] at hfull
  exact mul_left_cancel₀ (two_ne_zero' ℂ) (by linear_combination hfull)

/-- **Bessel's first integral.** For every `n ∈ ℤ` and `z ∈ ℂ`,
`J_n(z) = π⁻¹ ∫_0^π cos(z sin θ - n θ) dθ` (DLMF 10.9.2). -/
theorem besselJ_int_eq_integral_cos_sin_sub (n : ℤ) (z : ℂ) :
    besselJ n z = (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, cos (z * Real.sin θ - n * θ) := by
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [integral_zero_pi_cos_sin_sub, inv_mul_cancel_left₀ hpi]

/-- Over `[0, 2π]`, `∫_0^{2π} e^{i z cos θ} dθ = 2 π J_0(z)` for every `z ∈ ℂ` (DLMF 10.9.1). -/
theorem integral_zero_two_pi_exp_I_mul_cos (z : ℂ) :
    ∫ θ in (0 : ℝ)..2 * π, exp (I * z * Real.cos θ) = 2 * π * besselJ 0 z := by
  simpa using integral_zero_two_pi_exp_I_mul_cos_mul_exp z 0

/-- Over `[-π, π]`, `∫_{-π}^{π} e^{i z cos θ} dθ = 2 π J_0(z)` for every `z ∈ ℂ`. -/
theorem integral_neg_pi_pi_exp_I_mul_cos (z : ℂ) :
    ∫ θ in -π..π, exp (I * z * Real.cos θ) = 2 * π * besselJ 0 z := by
  simpa using integral_exp_I_mul_cos_mul_exp z 0

/-- **The Bessel integral for `J_0` over `[0, 2π]`.** For every `z ∈ ℂ`,
`J_0(z) = (2π)⁻¹ ∫_0^{2π} e^{i z cos θ} dθ` (DLMF 10.9.1). -/
theorem besselJ_zero_left_eq_integral_exp_I_mul_cos (z : ℂ) :
    besselJ 0 z = (2 * (π : ℂ))⁻¹ * ∫ θ in (0 : ℝ)..2 * π, exp (I * z * Real.cos θ) := by
  have h2pi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [integral_zero_two_pi_exp_I_mul_cos, inv_mul_cancel_left₀ h2pi]

/-- For every `z ∈ ℂ`, `J_0(z) = π⁻¹ ∫_0^π cos(z sin θ) dθ` (DLMF 10.9.1). -/
theorem besselJ_zero_left_eq_integral_cos_sin (z : ℂ) :
    besselJ 0 z = (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, cos (z * Real.sin θ) := by
  simpa using besselJ_int_eq_integral_cos_sin_sub 0 z

/-- Quarter-period Bessel integral for `J_0`: for every `z ∈ ℂ`,
`J_0(z) = (2 / π) ∫_0^{π/2} cos(z sin θ) dθ` (DLMF 10.9.1). -/
theorem besselJ_zero_left_eq_integral_zero_pi_div_two_cos_sin (z : ℂ) :
    besselJ 0 z = 2 / π * ∫ θ in (0 : ℝ)..π / 2, cos (z * Real.sin θ) := by
  have hint (a b : ℝ) : IntervalIntegrable (fun θ : ℝ => cos (z * Real.sin θ)) volume a b :=
    (by fun_prop : Continuous fun θ : ℝ => cos (z * Real.sin θ)).intervalIntegrable a b
  have hsymm : ∫ θ in π / 2..π, cos (z * Real.sin θ) =
      ∫ θ in (0 : ℝ)..π / 2, cos (z * Real.sin θ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => cos (z * Real.sin θ)) π (a := 0) (b := π / 2)
    have hpi : π - π / 2 = π / 2 := by ring
    simp only [Real.sin_pi_sub, sub_zero, hpi] at h
    exact h.symm
  rw [besselJ_zero_left_eq_integral_cos_sin,
    ← intervalIntegral.integral_add_adjacent_intervals (hint 0 (π / 2)) (hint (π / 2) π), hsymm]
  ring

/-- Quarter-period Bessel integral for `J_0` with cosine: for every `z ∈ ℂ`,
`J_0(z) = (2 / π) ∫_0^{π/2} cos(z cos θ) dθ` (DLMF 10.9.1). -/
theorem besselJ_zero_left_eq_integral_zero_pi_div_two_cos_cos (z : ℂ) :
    besselJ 0 z = 2 / π * ∫ θ in (0 : ℝ)..π / 2, cos (z * Real.cos θ) := by
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ : ℝ => cos (z * Real.cos θ)) (π / 2) (a := 0) (b := π / 2)
  simp only [Real.cos_pi_div_two_sub, sub_self, sub_zero] at h
  rw [besselJ_zero_left_eq_integral_zero_pi_div_two_cos_sin, ← h]

/-- For every `z ∈ ℂ`, `J_0(z) = π⁻¹ ∫_0^π cos(z cos θ) dθ` (DLMF 10.9.1). -/
theorem besselJ_zero_left_eq_integral_cos_cos (z : ℂ) :
    besselJ 0 z = (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, cos (z * Real.cos θ) := by
  have hint (a b : ℝ) : IntervalIntegrable (fun θ : ℝ => cos (z * Real.cos θ)) volume a b :=
    (by fun_prop : Continuous fun θ : ℝ => cos (z * Real.cos θ)).intervalIntegrable a b
  have hsymm : ∫ θ in π / 2..π, cos (z * Real.cos θ) =
      ∫ θ in (0 : ℝ)..π / 2, cos (z * Real.cos θ) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => cos (z * Real.cos θ)) π (a := 0) (b := π / 2)
    have hpi : π - π / 2 = π / 2 := by ring
    simp only [Real.cos_pi_sub, ofReal_neg, mul_neg, cos_neg, sub_zero, hpi] at h
    exact h.symm
  rw [besselJ_zero_left_eq_integral_zero_pi_div_two_cos_cos,
    ← intervalIntegral.integral_add_adjacent_intervals (hint 0 (π / 2)) (hint (π / 2) π), hsymm]
  ring

/-! ### Magnitude bounds for integer orders -/

/-- For every integer `n` and complex `z`, `‖J_n(z)‖ ≤ exp |Im z|` (DLMF 10.14.4). -/
theorem norm_besselJ_int_le_exp_abs_im (n : ℤ) (z : ℂ) :
    ‖besselJ n z‖ ≤ Real.exp |z.im| := by
  have h2pi : (0 : ℝ) < 2 * π := Real.two_pi_pos
  have heq := congrArg norm (integral_zero_two_pi_exp_I_mul_sin_sub z n).symm
  rw [norm_mul, norm_mul, norm_ofNat, norm_real, Real.norm_of_nonneg Real.pi_nonneg] at heq
  have hbound : ‖∫ θ in (0 : ℝ)..2 * π, exp (I * (z * Real.sin θ - n * θ))‖ ≤
      Real.exp |z.im| * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have hre : (I * (z * (Real.sin θ : ℂ) - (n : ℂ) * (θ : ℂ))).re = -(z.im * Real.sin θ) := by
      have hnθ : (n : ℂ) * (θ : ℂ) = ((n * θ : ℝ) : ℂ) := by push_cast; ring
      rw [hnθ]
      simp only [mul_re, I_re, I_im, zero_mul, one_mul, zero_sub, sub_im, mul_im, ofReal_re,
        ofReal_im]
      ring
    rw [hre]
    calc -(z.im * Real.sin θ)
        ≤ |z.im * Real.sin θ| := neg_le_abs _
      _ = |z.im| * |Real.sin θ| := abs_mul _ _
      _ ≤ |z.im| * 1 := by gcongr; exact Real.abs_sin_le_one θ
      _ = |z.im| := mul_one _
  rw [sub_zero, abs_of_pos h2pi, ← heq] at hbound
  nlinarith

/-- For every integer `n` and real `x`, `‖J_n(x)‖ ≤ 1` (DLMF 10.14.1). -/
theorem norm_besselJ_int_ofReal_le_one (n : ℤ) (x : ℝ) : ‖besselJ n x‖ ≤ 1 := by
  simpa using norm_besselJ_int_le_exp_abs_im n x

/-! ### Complex derivatives and differential recurrences -/

/-- On `Complex.slitPlane`, `J_ν'(z) = (ν / z) J_ν(z) - J_{ν+1}(z)` (DLMF 10.6.2). -/
theorem hasDerivAt_besselJ_eq_div_sub (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselJ ν) (ν / z * besselJ ν z - besselJ (ν + 1) z) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  have hz2_slit : z / 2 ∈ slitPlane := by
    rw [mem_slitPlane_iff] at hz ⊢
    rcases hz with hre | him
    · left; simpa [div_ofNat_re] using half_pos hre
    · right; simpa [div_ofNat_im] using div_ne_zero him two_ne_zero
  have hpow := HasDerivAt.cpow_const (c := ν) ((hasDerivAt_id' z).div_const (2 : ℂ)) hz2_slit
  have hF := (hasDerivAt_regularizedHGFun_zero_singleton (ν + 1) (-(z / 2) ^ 2)).comp z
    (((hasDerivAt_id' z).div_const (2 : ℂ)).pow 2).neg
  refine ((hpow.mul hF).congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)).congr_deriv ?_
  · simp only [Pi.mul_apply, Function.comp_apply, Pi.neg_apply, Pi.pow_apply, besselJ_def]
  · simp only [Function.comp_apply, Pi.neg_apply, Pi.pow_apply, besselJ_def]
    have h1 : (z / 2) ^ (ν - 1) = (z / 2) ^ ν / (z / 2) := by
      rw [cpow_sub _ _ hz2, cpow_one]
    have h2 : (z / 2) ^ (ν + 1) = (z / 2) ^ ν * (z / 2) := by
      rw [cpow_add _ _ hz2, cpow_one]
    have hadd : ν + 1 + 1 = ν + 2 := by ring
    rw [h1, h2, hadd]
    field_simp [hz0, hz2]
    ring

/-- On `Complex.slitPlane`, `J_ν'(z) = (J_{ν-1}(z) - J_{ν+1}(z)) / 2` (DLMF 10.6.1). -/
theorem hasDerivAt_besselJ (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (besselJ ν) ((besselJ (ν - 1) z - besselJ (ν + 1) z) / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  refine (hasDerivAt_besselJ_eq_div_sub ν hz).congr_deriv ?_
  have hrec := two_mul_self_mul_besselJ ν z
  field_simp [hz0]
  linear_combination hrec

/-- On `Complex.slitPlane`, `deriv (besselJ ν) z = (J_{ν-1}(z) - J_{ν+1}(z)) / 2` (DLMF 10.6.1). -/
theorem deriv_besselJ (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (besselJ ν) z = (besselJ (ν - 1) z - besselJ (ν + 1) z) / 2 :=
  (hasDerivAt_besselJ ν hz).deriv

/-- For an integer order `n`, `deriv (besselJ n) z = (J_{n-1}(z) - J_{n+1}(z)) / 2` across the
entire complex plane, including `z = 0` and the negative real axis (DLMF 10.6.1). -/
theorem deriv_besselJ_int (n : ℤ) (z : ℂ) :
    deriv (besselJ n) z = (besselJ (n - 1 : ℤ) z - besselJ (n + 1 : ℤ) z) / 2 := by
  let g : ℂ → ℂ := fun w => (besselJ (n - 1 : ℤ) w - besselJ (n + 1 : ℤ) w) / 2
  have hslit (w : ℂ) (hw : w ∈ slitPlane) : deriv (besselJ n) w = g w := by
    simpa [g] using deriv_besselJ (n : ℂ) hw
  by_cases hz : z ∈ slitPlane
  · exact hslit z hz
  · have him : z.im = 0 := by
      rw [mem_slitPlane_iff] at hz
      push Not at hz
      exact hz.2
    have hcont_f : ContinuousAt (deriv (besselJ n)) z :=
      (analyticAt_besselJ_int n z).deriv.continuousAt
    have hcont_g : ContinuousAt g z :=
      (((analyticAt_besselJ_int (n - 1) z).continuousAt.sub
        (analyticAt_besselJ_int (n + 1) z).continuousAt).div_const 2)
    have h0 : Tendsto (fun k : ℕ => (((k : ℝ) + 1)⁻¹ : ℂ)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using
        (continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    have hseq : Tendsto (fun k : ℕ => z + (((k : ℝ) + 1)⁻¹ : ℝ) * I) atTop (𝓝 z) := by
      simpa using tendsto_const_nhds.add (h0.mul_const I)
    have hmem (k : ℕ) : z + (((k : ℝ) + 1)⁻¹ : ℝ) * I ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      right
      simp only [add_im, him, zero_add, mul_im, I_re, mul_zero, I_im, mul_one, ofReal_re,
        ofReal_im, ne_eq]
      positivity
    exact tendsto_nhds_unique (hcont_f.tendsto.comp hseq)
      ((hcont_g.tendsto.comp hseq).congr fun k => (hslit _ (hmem k)).symm)

/-- For an integer order `n`, `J_n` has complex derivative `(J_{n-1}(z) - J_{n+1}(z)) / 2` at
every `z ∈ ℂ` (DLMF 10.6.1). -/
theorem hasDerivAt_besselJ_int (n : ℤ) (z : ℂ) :
    HasDerivAt (besselJ n) ((besselJ (n - 1 : ℤ) z - besselJ (n + 1 : ℤ) z) / 2) z := by
  simpa only [deriv_besselJ_int] using (analyticAt_besselJ_int n z).differentiableAt.hasDerivAt

/-- `J_0` has complex derivative `-J_1(z)` at every `z ∈ ℂ` (DLMF 10.6.3). -/
theorem hasDerivAt_besselJ_zero_left (z : ℂ) :
    HasDerivAt (besselJ 0) (-besselJ 1 z) z := by
  have hd : HasDerivAt (besselJ 0)
      ((besselJ (-1 : ℤ) z - besselJ (1 : ℤ) z) / 2) z := by
    simpa using hasDerivAt_besselJ_int 0 z
  refine hd.congr_deriv ?_
  have h := besselJ_neg_int 1 z
  simp only [Int.cast_neg, Int.cast_one, zpow_one] at h ⊢
  rw [h]
  ring

/-- `deriv (besselJ 0) z = -J_1(z)` for every `z ∈ ℂ` (DLMF 10.6.3). -/
@[simp]
theorem deriv_besselJ_zero_left (z : ℂ) : deriv (besselJ 0) z = -besselJ 1 z :=
  (hasDerivAt_besselJ_zero_left z).deriv

/-- For every natural `n` and `z ∈ ℂ`, `w ↦ w^(n+1) J_{n+1}(w)` has complex derivative
`z^(n+1) J_n(z)` at `z` (DLMF 10.6.6). -/
theorem hasDerivAt_pow_mul_besselJ_natCast (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => w ^ (n + 1) * besselJ (n + 1) w)
      (z ^ (n + 1) * besselJ n z) z := by
  have hb : HasDerivAt (besselJ (n + 1))
      ((besselJ n z - besselJ (n + 2) z) / 2) z := by
    convert hasDerivAt_besselJ_int (n + 1) z using 2
    · push_cast; ring
    · congr 2 <;> (push_cast; ring)
  refine ((hasDerivAt_pow (n + 1) z).mul hb).congr_deriv ?_
  have hrec := two_mul_self_mul_besselJ ((n : ℂ) + 1) z
  have hsub : (n : ℂ) + 1 - 1 = n := by ring
  have hadd : (n : ℂ) + 1 + 1 = n + 2 := by ring
  rw [hsub, hadd] at hrec
  push_cast
  linear_combination (z ^ n / 2) * hrec

/-- `w ↦ w J_1(w)` has complex derivative `z J_0(z)` at every `z ∈ ℂ` (DLMF 10.6.6). -/
theorem hasDerivAt_mul_besselJ_one_left (z : ℂ) :
    HasDerivAt (fun w : ℂ => w * besselJ 1 w) (z * besselJ 0 z) z := by
  simpa using hasDerivAt_pow_mul_besselJ_natCast 0 z

/-- On any real interval `[a, b]`,
`∫_a^b t^(n+1) J_n(t) dt = b^(n+1) J_{n+1}(b) - a^(n+1) J_{n+1}(a)` (DLMF 10.22.1). -/
theorem integral_pow_mul_besselJ_natCast (n : ℕ) (a b : ℝ) :
    ∫ t in a..b, (t : ℂ) ^ (n + 1) * besselJ n t =
      b ^ (n + 1) * besselJ (n + 1) b - a ^ (n + 1) * besselJ (n + 1) a := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => (t : ℂ) ^ (n + 1) * besselJ (n + 1) t) (fun t _ => ?_) ?_
  · simpa using (hasDerivAt_pow_mul_besselJ_natCast n (t : ℂ)).comp_ofReal
  · have hcont : Continuous fun t : ℝ => besselJ n (t : ℂ) := by
      simpa only [Int.cast_natCast, Function.comp_def] using
        (analyticOnNhd_besselJ_int n).continuous.comp continuous_ofReal
    exact ((continuous_ofReal.pow (n + 1)).mul hcont).intervalIntegrable a b

/-- On any real interval `[a, b]`, `∫_a^b t J_0(t) dt = b J_1(b) - a J_1(a)` (DLMF 10.22.1). -/
theorem integral_mul_besselJ_zero_left (a b : ℝ) :
    ∫ t in a..b, (t : ℂ) * besselJ 0 t = b * besselJ 1 b - a * besselJ 1 a := by
  simpa using integral_pow_mul_besselJ_natCast 0 a b

end Complex
