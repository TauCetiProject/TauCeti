/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp

/-!
# The exponential `e^{2π i τ}` on the upper half-plane

Elementary facts about `q = e^{2π i τ}` and `e^{2π i (x τ + y)}` for `τ` in the upper half-plane,
complementing `Mathlib.Analysis.Complex.UpperHalfPlane.Exp`.

## Main results

* `TauCeti.UpperHalfPlane.one_sub_exp_two_pi_I_ne_zero`: `1 - e^{2π i (x τ + y)}` has no zero in
  the upper half-plane unless `x = 0` and `y ∈ ℤ`.
* `TauCeti.UpperHalfPlane.exp_two_pi_I_zpow_mul_exp`:
  `qᵏ e^{2π i (x τ + y)} = e^{2π i ((k + x) τ + y)}` for `k ∈ ℤ`.
-/

public section

open Complex
open UpperHalfPlane hiding I
open scoped Real

namespace TauCeti.UpperHalfPlane

/-- `1 - e^{2π i (x τ + y)}` vanishes at a point `τ` of the upper half-plane only when `x = 0` and
`y` is an integer. -/
theorem one_sub_exp_two_pi_I_ne_zero {x y : ℝ} {τ : ℂ} (hτ : 0 < τ.im)
    (h : ∀ k : ℤ, x = 0 → y ≠ k) : 1 - cexp (2 * π * I * (x * τ + y)) ≠ 0 := by
  rw [sub_ne_zero, ne_comm, Ne, Complex.exp_eq_one_iff]
  rintro ⟨k, hk⟩
  have hk' : (x : ℂ) * τ + y = k := by
    have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    exact mul_left_cancel₀ h2 (by rw [hk]; ring)
  have him := congrArg Complex.im hk'
  have hre := congrArg Complex.re hk'
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, intCast_im] at him
  have hx : x = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h (ne_of_gt hτ)
  exact h k hx (by simpa [hx] using hre)

/-- `qᵏ e^{2π i (x τ + y)} = e^{2π i ((k + x) τ + y)}` for `q = e^{2π i τ}` and `k ∈ ℤ`. -/
theorem exp_two_pi_I_zpow_mul_exp (k : ℤ) (x y : ℝ) (τ : ℂ) :
    cexp (2 * π * I * τ) ^ k * cexp (2 * π * I * (x * τ + y)) =
      cexp (2 * π * I * (((k + x : ℝ) : ℂ) * τ + y)) := by
  rw [← Complex.exp_int_mul, ← Complex.exp_add]
  push_cast
  ring_nf

end TauCeti.UpperHalfPlane
