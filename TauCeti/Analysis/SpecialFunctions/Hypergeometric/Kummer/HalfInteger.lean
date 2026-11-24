/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Contiguous

/-!
# The Kummer function at half-integer lower parameters

Write `𝐌(a, b, z) = Complex.regularizedHGFun {a} {b} z = ∑ (a)ₖ zᵏ / (k! Γ(b + k))` for Olver's
regularized Kummer function. At the half-integer lower parameters `b = m + ½`, `m ∈ ℕ`, the
half-integer values `Γ(n + ½) = (2n)! √π / (4ⁿ n!)` make the coefficients of `Γ(b) 𝐌(a, b, z)`
rational:

`Γ(m + ½) 𝐌(a, m + ½, z) = ∑ (a)ₖ (4z)ᵏ (2m)! (m + k)! / (m! k! (2(m + k))!)`,

for all complex `a` and `z`. At `m = 0` and `m = 1` the coefficients are `4ᵏ (a)ₖ / (2k)!` and
`4ᵏ (a)ₖ / (2k + 1)!`, so the unregularized Kummer functions `Γ(½) 𝐌(a, ½, z)` and
`Γ(3/2) 𝐌(a, 3/2, z)` have the series

`Γ(½) 𝐌(a, ½, z) = ∑ (a)ₖ (4z)ᵏ / (2k)!`, `Γ(3/2) 𝐌(a, 3/2, z) = ∑ (a)ₖ (4z)ᵏ / (2k + 1)!`.

These are the series behind the power series of the parabolic cylinder functions
(DLMF 12.4.3–12.4.6), whose Kummer forms (DLMF 12.7.12–12.7.13) have the lower parameters `½` and
`3/2`.

## Main results

* `Complex.Gamma_natCast_add_half_mul_regularizedHGFunCoeff`: the coefficients
  `Γ(b) (a)ₖ / (k! Γ(b + k))` at `b = m + ½`.
* `Complex.Gamma_one_half_mul_regularizedHGFunCoeff`,
  `Complex.Gamma_three_halves_mul_regularizedHGFunCoeff`: the cases `m = 0` and `m = 1`,
  `4ᵏ (a)ₖ / (2k)!` and `4ᵏ (a)ₖ / (2k + 1)!`.
* `Complex.hasSum_Gamma_natCast_add_half_mul_regularizedHGFun`: the series of
  `Γ(m + ½) 𝐌(a, m + ½, z)`.
* `Complex.hasSum_Gamma_one_half_mul_regularizedHGFun`,
  `Complex.hasSum_Gamma_three_halves_mul_regularizedHGFun`: the series of `Γ(½) 𝐌(a, ½, z)` and
  `Γ(3/2) 𝐌(a, 3/2, z)`.

## References

* *NIST Digital Library of Mathematical Functions*, [§13.2](https://dlmf.nist.gov/13.2) and
  [§12.4](https://dlmf.nist.gov/12.4).
-/

public section

open scoped Nat Real

namespace Complex

/-- The coefficients of the unregularized Kummer series at the half-integer lower parameter
`m + ½`: `Γ(m + ½) (a)ₖ / (k! Γ(m + ½ + k)) = 4ᵏ (a)ₖ (2m)! (m + k)! / (m! k! (2(m + k))!)`, from
the half-integer values `Complex.Gamma_natCast_add_half_eq_factorial`. -/
theorem Gamma_natCast_add_half_mul_regularizedHGFunCoeff (a : ℂ) (m k : ℕ) :
    Gamma (m + 1 / 2) * regularizedHGFunCoeff {a} {(m : ℂ) + 1 / 2} k =
      (ascPochhammer ℂ k).eval a * 4 ^ k * ((2 * m)! * (m + k)!) /
        (m ! * k ! * (2 * (m + k))!) := by
  -- the lower parameter shifted by `k` is again a half-integer
  have hk : (m : ℂ) + 1 / 2 + k = ((m + k : ℕ) : ℂ) + 1 / 2 := by push_cast; ring
  have hπ : (√π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  rw [regularizedHGFunCoeff_singleton, hk, Gamma_natCast_add_half_eq_factorial,
    Gamma_natCast_add_half_eq_factorial]
  field_simp
  ring

/-- The coefficients of the unregularized Kummer series at the lower parameter `½`:
`Γ(½) (a)ₖ / (k! Γ(½ + k)) = 4ᵏ (a)ₖ / (2k)!`. -/
theorem Gamma_one_half_mul_regularizedHGFunCoeff (a : ℂ) (k : ℕ) :
    Gamma (1 / 2) * regularizedHGFunCoeff {a} {1 / 2} k =
      (ascPochhammer ℂ k).eval a * 4 ^ k / (2 * k)! := by
  have h := Gamma_natCast_add_half_mul_regularizedHGFunCoeff a 0 k
  rw [Nat.cast_zero, zero_add] at h
  have hkf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  rw [h]
  simp only [mul_zero, zero_add, Nat.factorial_zero, Nat.cast_one, one_mul]
  field_simp

/-- The coefficients of the unregularized Kummer series at the lower parameter `3/2`:
`Γ(3/2) (a)ₖ / (k! Γ(3/2 + k)) = 4ᵏ (a)ₖ / (2k + 1)!`. -/
theorem Gamma_three_halves_mul_regularizedHGFunCoeff (a : ℂ) (k : ℕ) :
    Gamma (3 / 2) * regularizedHGFunCoeff {a} {3 / 2} k =
      (ascPochhammer ℂ k).eval a * 4 ^ k / (2 * k + 1)! := by
  have h := Gamma_natCast_add_half_mul_regularizedHGFunCoeff a 1 k
  -- the lower parameter `1 + ½` and the factorial `(2(1 + k))! = (2k + 2)!`
  have h32 : ((1 : ℕ) : ℂ) + 1 / 2 = 3 / 2 := by norm_num
  have hk : 2 * (1 + k) = 2 * k + 1 + 1 := by ring
  have hkf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2kf : ((2 * k + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h2k : (2 * k + 1 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k + 1)
  rw [h32] at h
  rw [h, hk, Nat.factorial_succ (2 * k + 1), add_comm 1 k, Nat.factorial_succ k, mul_one,
    Nat.factorial_two, Nat.factorial_one]
  push_cast
  field_simp
  ring

/-- **The Kummer series at the half-integer lower parameter `m + ½`**: the unregularized Kummer
function `Γ(m + ½) 𝐌(a, m + ½, z) = M(a, m + ½, z)` is
`∑ₖ (a)ₖ (4z)ᵏ (2m)! (m + k)! / (m! k! (2(m + k))!)`, for all complex `a` and `z`. -/
theorem hasSum_Gamma_natCast_add_half_mul_regularizedHGFun (a z : ℂ) (m : ℕ) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval a * (4 * z) ^ k * ((2 * m)! * (m + k)!) /
        (m ! * k ! * (2 * (m + k))!))
      (Gamma (m + 1 / 2) * regularizedHGFun {a} {(m : ℂ) + 1 / 2} z) := by
  convert (hasSum_regularizedHGFun (a := {a}) (b := {(m : ℂ) + 1 / 2}) (by simp) z).mul_left
    (Gamma (m + 1 / 2)) using 1
  funext k
  rw [← mul_assoc (Gamma _), Gamma_natCast_add_half_mul_regularizedHGFunCoeff, mul_pow]
  ring

/-- **The Kummer series at the lower parameter `½`**: the unregularized Kummer function
`Γ(½) 𝐌(a, ½, z) = M(a, ½, z)` is `∑ₖ (a)ₖ (4z)ᵏ / (2k)!`, for all complex `a` and `z`. -/
theorem hasSum_Gamma_one_half_mul_regularizedHGFun (a z : ℂ) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval a * (4 * z) ^ k / (2 * k)!)
      (Gamma (1 / 2) * regularizedHGFun {a} {1 / 2} z) := by
  have h := hasSum_Gamma_natCast_add_half_mul_regularizedHGFun a z 0
  rw [Nat.cast_zero, zero_add] at h
  refine h.congr_fun fun k => ?_
  -- the two coefficient formulas at `m = 0`
  have e := Gamma_natCast_add_half_mul_regularizedHGFunCoeff a 0 k
  rw [Nat.cast_zero, zero_add, Gamma_one_half_mul_regularizedHGFunCoeff] at e
  rw [mul_pow]
  linear_combination z ^ k * e

/-- **The Kummer series at the lower parameter `3/2`**: the unregularized Kummer function
`Γ(3/2) 𝐌(a, 3/2, z) = M(a, 3/2, z)` is `∑ₖ (a)ₖ (4z)ᵏ / (2k + 1)!`, for all complex `a`
and `z`. -/
theorem hasSum_Gamma_three_halves_mul_regularizedHGFun (a z : ℂ) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval a * (4 * z) ^ k / (2 * k + 1)!)
      (Gamma (3 / 2) * regularizedHGFun {a} {3 / 2} z) := by
  -- the lower parameter `1 + ½`
  have h32 : ((1 : ℕ) : ℂ) + 1 / 2 = 3 / 2 := by norm_num
  have h := hasSum_Gamma_natCast_add_half_mul_regularizedHGFun a z 1
  rw [h32] at h
  refine h.congr_fun fun k => ?_
  -- the two coefficient formulas at `m = 1`
  have e := Gamma_natCast_add_half_mul_regularizedHGFunCoeff a 1 k
  rw [h32, Gamma_three_halves_mul_regularizedHGFunCoeff] at e
  rw [mul_pow]
  linear_combination z ^ k * e

end Complex
