/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Closed forms of `exp (π i / 3)`, `exp (π i / 6)` and `exp (2 π i / 3)`

The values of the complex exponential at `±π i / 6`, `±π i / 3` and `±2 π i / 3` in Cartesian
form, through `√3`, and the fact that `ω = exp (2 π i / 3)` and `ω⁻¹` are cube roots of unity.
The squares of `√x` in `ℂ` are recorded alongside, since every use of the closed forms needs
`(√3 : ℂ) ^ 2 = 3`.

## Main results

* `Complex.ofReal_sqrt_sq`, `Complex.ofReal_sqrt_ofNat_sq`: `(√x : ℂ) ^ 2 = x` for `0 ≤ x`;
* `Complex.exp_two_pi_mul_I_div_three`, `Complex.exp_neg_two_pi_mul_I_div_three`:
  `exp (±2 π i / 3) = -1/2 ± (√3/2) i`;
* `Complex.exp_pi_mul_I_div_three`, `Complex.exp_neg_pi_mul_I_div_three`:
  `exp (±π i / 3) = 1/2 ± (√3/2) i`;
* `Complex.exp_pi_mul_I_div_six`, `Complex.exp_neg_pi_mul_I_div_six`:
  `exp (±π i / 6) = √3/2 ± i/2`;
* `Complex.exp_two_pi_mul_I_div_three_pow_three`,
  `Complex.exp_neg_two_pi_mul_I_div_three_pow_three`: `exp (±2 π i / 3) ^ 3 = 1`.
-/

public section

open scoped Real

namespace Complex

/-- `(√x)² = x` in `ℂ` for `0 ≤ x`. -/
theorem ofReal_sqrt_sq {x : ℝ} (hx : 0 ≤ x) : (√x : ℂ) ^ 2 = x := by
  rw [← ofReal_pow, Real.sq_sqrt hx]

/-- `(√n)² = n` in `ℂ` for a numeral `n`, for instance `(√3 : ℂ) ^ 2 = 3`. -/
@[simp]
theorem ofReal_sqrt_ofNat_sq (n : ℕ) [n.AtLeastTwo] :
    (√(ofNat(n) : ℝ) : ℂ) ^ 2 = ofNat(n) := by
  rw [ofReal_sqrt_sq (Nat.ofNat_nonneg _), ofReal_ofNat]

/-- `ω = e^{2πi/3} = −1/2 + (√3/2) i`. -/
theorem exp_two_pi_mul_I_div_three : cexp (2 * π * I / 3) = -1 / 2 + √3 / 2 * I := by
  have h := exp_ofReal_mul_I (π - π / 3)
  rw [Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three] at h
  convert h using 2 <;> push_cast <;> ring

/-- `ω⁻¹ = e^{−2πi/3} = −1/2 − (√3/2) i`. -/
theorem exp_neg_two_pi_mul_I_div_three : cexp (-(2 * π * I / 3)) = -1 / 2 - √3 / 2 * I := by
  have h := exp_ofReal_mul_I (-(π - π / 3))
  rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three,
    Real.sin_pi_div_three] at h
  convert h using 2 <;> push_cast <;> ring

/-- `e^{πi/3} = 1/2 + (√3/2) i`. -/
theorem exp_pi_mul_I_div_three : cexp (π * I / 3) = 1 / 2 + √3 / 2 * I := by
  have h := exp_ofReal_mul_I (π / 3)
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three] at h
  convert h using 2 <;> push_cast <;> ring

/-- `e^{−πi/3} = 1/2 − (√3/2) i`. -/
theorem exp_neg_pi_mul_I_div_three : cexp (-(π * I / 3)) = 1 / 2 - √3 / 2 * I := by
  have h := exp_ofReal_mul_I (-(π / 3))
  rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_three, Real.sin_pi_div_three] at h
  convert h using 2 <;> push_cast <;> ring

/-- `e^{πi/6} = √3/2 + i/2`. -/
theorem exp_pi_mul_I_div_six : cexp (π * I / 6) = √3 / 2 + 1 / 2 * I := by
  have h := exp_ofReal_mul_I (π / 6)
  rw [Real.cos_pi_div_six, Real.sin_pi_div_six] at h
  convert h using 2 <;> push_cast <;> ring

/-- `e^{−πi/6} = √3/2 − i/2`. -/
theorem exp_neg_pi_mul_I_div_six : cexp (-(π * I / 6)) = √3 / 2 - 1 / 2 * I := by
  have h := exp_ofReal_mul_I (-(π / 6))
  rw [Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six, Real.sin_pi_div_six] at h
  convert h using 2 <;> push_cast <;> ring

/-- `ω³ = 1` for `ω = e^{2πi/3}`. -/
theorem exp_two_pi_mul_I_div_three_pow_three : cexp (2 * π * I / 3) ^ 3 = 1 := by
  rw [← exp_natCast_mul]
  convert exp_two_pi_mul_I using 2
  push_cast
  ring

/-- `ω⁻³ = 1` for `ω = e^{2πi/3}`. -/
theorem exp_neg_two_pi_mul_I_div_three_pow_three : cexp (-(2 * π * I / 3)) ^ 3 = 1 := by
  rw [exp_neg, inv_pow, exp_two_pi_mul_I_div_three_pow_three, inv_one]

end Complex
