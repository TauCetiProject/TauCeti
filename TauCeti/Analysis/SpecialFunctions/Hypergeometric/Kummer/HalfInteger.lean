/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Contiguous

/-!
# The Kummer function at the lower parameters `½` and `3/2`

Write `𝐌(a, b, z) = Complex.regularizedHGFun {a} {b} z = ∑ (a)ₖ zᵏ / (k! Γ(b + k))` for Olver's
regularized Kummer function. At the half-integer lower parameters `b = ½` and `b = 3/2` the
factors `k! Γ(b + k) / Γ(b)` are the factorials `(2k)! / 4ᵏ` and `(2k + 1)! / 4ᵏ`, so the
unregularized Kummer functions `Γ(½) 𝐌(a, ½, z)` and `Γ(3/2) 𝐌(a, 3/2, z)` have the series

`Γ(½) 𝐌(a, ½, z) = ∑ (a)ₖ (4z)ᵏ / (2k)!`, `Γ(3/2) 𝐌(a, 3/2, z) = ∑ (a)ₖ (4z)ᵏ / (2k + 1)!`,

for all complex `a` and `z`. These are the series behind the power series of the parabolic
cylinder functions (DLMF 12.4.3–12.4.6), whose Kummer forms (DLMF 12.7.12–12.7.13) have the lower
parameters `½` and `3/2`.

## Main results

* `Complex.Gamma_one_half_mul_regularizedHGFunCoeff`,
  `Complex.Gamma_three_halves_mul_regularizedHGFunCoeff`: the coefficients
  `Γ(b) (a)ₖ / (k! Γ(b + k))` at `b = ½` and `b = 3/2` are `4ᵏ (a)ₖ / (2k)!` and
  `4ᵏ (a)ₖ / (2k + 1)!`.
* `Complex.hasSum_Gamma_one_half_mul_regularizedHGFun`: the series of `Γ(½) 𝐌(a, ½, z)`.
* `Complex.hasSum_Gamma_three_halves_mul_regularizedHGFun`: the series of `Γ(3/2) 𝐌(a, 3/2, z)`.

## References

* *NIST Digital Library of Mathematical Functions*, [§13.2](https://dlmf.nist.gov/13.2) and
  [§12.4](https://dlmf.nist.gov/12.4).
-/

public section

open scoped Nat Real

namespace Complex

/-- The coefficients of the unregularized Kummer series at the lower parameter `½`:
`Γ(½) (a)ₖ / (k! Γ(½ + k)) = 4ᵏ (a)ₖ / (2k)!`, from the half-integer values
`Γ(k + ½) = (2k)! √π / (4ᵏ k!)` of `Real.Gamma_nat_add_half_eq_factorial`. -/
theorem Gamma_one_half_mul_regularizedHGFunCoeff (a : ℂ) (k : ℕ) :
    Gamma (1 / 2) * regularizedHGFunCoeff {a} {1 / 2} k =
      (ascPochhammer ℂ k).eval a * 4 ^ k / (2 * k)! := by
  have h0 : Gamma (1 / 2) = ((Real.Gamma (0 + 1 / 2) : ℝ) : ℂ) := by
    rw [← Gamma_ofReal]
    push_cast
    ring_nf
  have hk : Gamma (1 / 2 + k) = ((Real.Gamma (k + 1 / 2) : ℝ) : ℂ) := by
    rw [← Gamma_ofReal]
    push_cast
    ring_nf
  have hπ : (√π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hkf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  rw [regularizedHGFunCoeff_singleton, h0, hk, ← Nat.cast_zero,
    Real.Gamma_nat_add_half_eq_factorial, Real.Gamma_nat_add_half_eq_factorial]
  push_cast
  field_simp

/-- The coefficients of the unregularized Kummer series at the lower parameter `3/2`:
`Γ(3/2) (a)ₖ / (k! Γ(3/2 + k)) = 4ᵏ (a)ₖ / (2k + 1)!`, from the half-integer values
`Γ(k + ½) = (2k)! √π / (4ᵏ k!)` of `Real.Gamma_nat_add_half_eq_factorial`. -/
theorem Gamma_three_halves_mul_regularizedHGFunCoeff (a : ℂ) (k : ℕ) :
    Gamma (3 / 2) * regularizedHGFunCoeff {a} {3 / 2} k =
      (ascPochhammer ℂ k).eval a * 4 ^ k / (2 * k + 1)! := by
  have h0 : Gamma (3 / 2) = ((Real.Gamma ((1 : ℕ) + 1 / 2) : ℝ) : ℂ) := by
    rw [← Gamma_ofReal]
    push_cast
    ring_nf
  have hk : Gamma (3 / 2 + k) = ((Real.Gamma ((k + 1 : ℕ) + 1 / 2) : ℝ) : ℂ) := by
    rw [← Gamma_ofReal]
    push_cast
    ring_nf
  have hπ : (√π : ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 Real.pi_pos).ne'
  have hkf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2kf : ((2 * k + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have h2k : (2 * k + 1 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * k + 1)
  rw [regularizedHGFunCoeff_singleton, h0, hk, Real.Gamma_nat_add_half_eq_factorial,
    Real.Gamma_nat_add_half_eq_factorial, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
    Nat.factorial_succ (2 * k + 1), Nat.factorial_succ k]
  push_cast
  field_simp
  ring

/-- **The Kummer series at the lower parameter `½`**: the unregularized Kummer function
`Γ(½) 𝐌(a, ½, z) = M(a, ½, z)` is `∑ₖ (a)ₖ (4z)ᵏ / (2k)!`, for all complex `a` and `z`. -/
theorem hasSum_Gamma_one_half_mul_regularizedHGFun (a z : ℂ) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval a * (4 * z) ^ k / (2 * k)!)
      (Gamma (1 / 2) * regularizedHGFun {a} {1 / 2} z) := by
  convert (hasSum_regularizedHGFun (a := {a}) (b := {1 / 2}) (by simp) z).mul_left
    (Gamma (1 / 2)) using 1
  funext k
  rw [← mul_assoc, Gamma_one_half_mul_regularizedHGFunCoeff, mul_pow]
  ring

/-- **The Kummer series at the lower parameter `3/2`**: the unregularized Kummer function
`Γ(3/2) 𝐌(a, 3/2, z) = M(a, 3/2, z)` is `∑ₖ (a)ₖ (4z)ᵏ / (2k + 1)!`, for all complex `a`
and `z`. -/
theorem hasSum_Gamma_three_halves_mul_regularizedHGFun (a z : ℂ) :
    HasSum (fun k : ℕ => (ascPochhammer ℂ k).eval a * (4 * z) ^ k / (2 * k + 1)!)
      (Gamma (3 / 2) * regularizedHGFun {a} {3 / 2} z) := by
  convert (hasSum_regularizedHGFun (a := {a}) (b := {3 / 2}) (by simp) z).mul_left
    (Gamma (3 / 2)) using 1
  funext k
  rw [← mul_assoc, Gamma_three_halves_mul_regularizedHGFunCoeff, mul_pow]
  ring

end Complex
