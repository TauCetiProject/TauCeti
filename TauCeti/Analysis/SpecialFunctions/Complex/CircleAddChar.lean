/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Data.ZMod.ValMinAbs

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Values of the standard circle character of `ZMod N`

Mathlib's `ZMod.toCircle` sends `j : ZMod N` to `exp (2πij/N)`. At level `2n` it sends `n`
to `exp (πi) = -1`. The distance from `1` to a character value is bounded below using the distance
of the corresponding residue to zero around the circle.

## Main results

* `ZMod.coe_toCircle_natCast_self`: `ZMod.toCircle (n : ZMod (2n)) = -1`.
* `ZMod.le_norm_stdAddChar_sub_one`: a lower bound for the distance to `1`.
-/

public section

namespace ZMod

open scoped Real

/-- The standard circle character of `ZMod (2n)` sends `n` to `exp (πi) = -1`. -/
theorem coe_toCircle_natCast_self (n : ℕ) [NeZero n] :
    ((toCircle ((n : ℕ) : ZMod (2 * n)) : Circle) : ℂ) = -1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [toCircle_natCast, Nat.cast_mul, Nat.cast_two]
  have : 2 * π * Complex.I * n / (2 * n) = π * Complex.I := by
    field_simp
  rw [this, Complex.exp_pi_mul_I]

/-- The chord from `1` to the standard character at `k` has length at least four times
the absolute value of the centered residue divided by the modulus. -/
theorem le_norm_stdAddChar_sub_one {N : ℕ} [NeZero N] (k : ZMod N) :
    4 * (k.valMinAbs.natAbs : ℝ) / N ≤ ‖stdAddChar k - 1‖ := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hk : (k.valMinAbs.natAbs : ℝ) * 2 ≤ N := by
    exact_mod_cast Nat.le_div_two_iff_mul_two_le.mp k.natAbs_valMinAbs_le
  have habs : |(k.valMinAbs : ℝ)| = k.valMinAbs.natAbs := by
    simp only [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hchar : stdAddChar k = Complex.exp (Complex.I * (↑(2 * (π *
      ((k.valMinAbs : ℝ) / N))) : ℂ)) := by
    calc
      stdAddChar k = stdAddChar (k.valMinAbs : ZMod N) := by rw [coe_valMinAbs]
      _ = _ := by
        rw [stdAddChar_coe]
        push_cast
        congr 1
        ring
  have harg : |π * ((k.valMinAbs : ℝ) / N)| = π * ((k.valMinAbs.natAbs : ℝ) / N) := by
    rw [abs_mul, abs_of_pos Real.pi_pos, abs_div, habs, abs_of_pos hN]
  have hhalf : |π * ((k.valMinAbs : ℝ) / N)| ≤ π / 2 := by
    rw [harg, div_eq_mul_inv π 2]
    exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hN).mpr (by linarith)) Real.pi_pos.le
  rw [hchar, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs,
    mul_div_cancel_left₀ _ two_ne_zero, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ = 2 * (2 / π * |π * ((k.valMinAbs : ℝ) / N)|) := by
      rw [harg]
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.mul_abs_le_abs_sin hhalf) (by norm_num)

end ZMod
