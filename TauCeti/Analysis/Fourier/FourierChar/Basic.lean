/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The real additive character and distance to the integers

The additive character `Real.fourierChar` is the lift of `AddCircle.toCircle` from
`UnitAddCircle`. The quotient norm is the distance to the nearest integer, by
`UnitAddCircle.norm_eq`. Its comparison with the chord from `1` controls the denominator
in geometric exponential sums. Integration over an interval of length one extracts the
zero Fourier mode.
-/

public section

open scoped FourierTransform

namespace AddCircle

/-- The standard character on `ℝ / ℤ`, pulled back to `ℝ`, is the real Fourier character. -/
@[simp]
theorem toCircle_unit_coe (x : ℝ) : toCircle (x : UnitAddCircle) = 𝐞 x := by
  rw [AddCircle.toCircle_apply_mk, div_one, Real.fourierChar_apply']

end AddCircle

namespace Real

/-- The real Fourier character is periodic with period one. -/
theorem periodic_fourierChar : Function.Periodic (𝐞 : ℝ → Circle) 1 := by
  intro x
  rw [← AddCircle.toCircle_unit_coe, AddCircle.coe_add_period, AddCircle.toCircle_unit_coe]

/-- The real Fourier character is one precisely at phases that vanish in `ℝ / ℤ`. -/
theorem fourierChar_eq_one_iff {x : ℝ} : 𝐞 x = 1 ↔ (x : UnitAddCircle) = 0 := by
  rw [← AddCircle.toCircle_unit_coe, ← AddCircle.toCircle_zero (T := 1)]
  exact (AddCircle.injective_toCircle one_ne_zero).eq_iff

/-- The real Fourier character is one at every integer. -/
@[simp]
theorem fourierChar_intCast (m : ℤ) : 𝐞 (m : ℝ) = 1 := by
  rw [fourierChar_eq_one_iff, AddCircle.coe_eq_zero_iff]
  exact ⟨m, by simp [zsmul_eq_mul]⟩

/-- The length of the chord from the Fourier character to `1`. -/
theorem norm_fourierChar_sub_one (x : ℝ) : ‖(𝐞 x : ℂ) - 1‖ = 2 * |sin (π * x)| := by
  rw [fourierChar_apply, mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one,
    Real.norm_eq_abs, abs_mul, abs_two]
  rw [show 2 * π * x / 2 = π * x by ring]

/-- Twice the distance to the nearest integer is at most `|sin (π x)|`. -/
theorem two_mul_norm_unitAddCircle_le_abs_sin (x : ℝ) :
    2 * ‖(x : UnitAddCircle)‖ ≤ |sin (π * x)| := by
  rw [UnitAddCircle.norm_eq]
  let y := x - (round x : ℝ)
  have hy : |y| ≤ 1 / 2 := abs_sub_round x
  have hπy : |π * y| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos pi_pos]
    linarith [mul_le_mul_of_nonneg_left hy pi_pos.le]
  have hsin := mul_abs_le_abs_sin hπy
  rw [abs_mul, abs_of_pos pi_pos, ← mul_assoc, div_mul_cancel₀ _ pi_ne_zero] at hsin
  have hshift : π * y = π * x - (round x : ℝ) * π := by dsimp [y]; ring
  rwa [hshift, sin_sub_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul] at hsin

/-- A full unit interval integrates an integer-frequency character to zero, except at
frequency zero, where the integral is one. -/
theorem integral_fourierChar_intCast_mul (m : ℤ) (a : ℝ) :
    (∫ x in a..a + 1, (𝐞 ((m : ℝ) * x) : ℂ)) = if m = 0 then 1 else 0 := by
  have : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
  have h := congrFun (fourierCoeff_fourier (T := 1) m) 0
  rw [fourierCoeff_eq_intervalIntegral _ _ a] at h
  have hmode (x : ℝ) : fourier (T := 1) m (x : UnitAddCircle) = (𝐞 ((m : ℝ) * x) : ℂ) := by
    rw [fourier_apply, ← AddCircle.coe_zsmul, AddCircle.toCircle_unit_coe, zsmul_eq_mul]
  simpa [hmode, Pi.single_apply, eq_comm (a := (0 : ℤ))] using h

end Real

open Real

-- The quarter-turn and half-turn fix the choice of sign of the character.
example : (𝐞 (1 / 2) : ℂ) = -1 := by
  rw [fourierChar_apply, show 2 * π * (1 / 2) = π by ring]
  exact Complex.exp_pi_mul_I

example : (𝐞 (1 / 4) : ℂ) = Complex.I := by
  rw [fourierChar_apply, show 2 * π * (1 / 4) = π / 2 by ring, Complex.ofReal_div]
  exact Complex.exp_pi_div_two_mul_I

example : ‖((1 / 2 : ℝ) : UnitAddCircle)‖ = 1 / 2 := by
  simpa using (AddCircle.norm_half_period_eq (p := (1 : ℝ)))

example : ‖((-3 / 10 : ℝ) : UnitAddCircle)‖ = 3 / 10 := by
  rw [(AddCircle.norm_coe_eq_abs_iff (p := 1) (by norm_num)).2 (by norm_num)]
  norm_num

example : ‖((7 : ℝ) : UnitAddCircle)‖ = 0 := by
  rw [norm_eq_zero, ← fourierChar_eq_one_iff]
  exact_mod_cast fourierChar_intCast 7
