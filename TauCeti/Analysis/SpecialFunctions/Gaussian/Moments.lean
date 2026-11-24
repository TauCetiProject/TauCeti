/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

import Mathlib.MeasureTheory.Integral.Gamma
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Gaussian moments

For a Gaussian kernel `exp (-b * x ^ 2)` on `(0, ∞)`, this file records the exact integrability
criterion and closed-form evaluations of the monomial moments
`∫ x in Ioi 0, x ^ k * exp (-b * x ^ 2)` for `k : ℕ`, specializing Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow` to natural powers and simplifying even and odd orders to
elementary factorial expressions. Folding the real line onto `(0, ∞)` doubles the even moments,
which gives the even moments over the whole line.

## Main results

* `TauCeti.integrableOn_Ioi_pow_mul_exp_neg_mul_sq_iff`: `x ↦ x ^ k * exp (-b * x ^ 2)` is
  integrable on `(0, ∞)` if and only if `0 < b`.
* `TauCeti.integral_Ioi_pow_mul_exp_neg_mul_sq`: general evaluation
  `∫ x in Ioi 0, x ^ k * exp (-b * x ^ 2) = Γ((k + 1) / 2) / (2 * b ^ ((k + 1) / 2))` for `0 < b`.
* `TauCeti.integral_Ioi_pow_two_mul_mul_exp_neg_mul_sq`: even-order half-line Gaussian moment
  `∫ x in Ioi 0, x ^ (2 * m) * exp (-b * x ^ 2)` equals
  `(2 * m)! * √(π / b) / (2 ^ (2 * m + 1) * m! * b ^ m)`, valid for all `b : ℝ`.
* `TauCeti.integral_Ioi_pow_two_mul_add_one_mul_exp_neg_mul_sq`: odd-order half-line Gaussian
  moment `∫ x in Ioi 0, x ^ (2 * m + 1) * exp (-b * x ^ 2) = m! / (2 * b ^ (m + 1))` for `0 < b`.
* `TauCeti.integral_pow_two_mul_mul_exp_neg_mul_sq`: even-order Gaussian moment over the whole
  line, `∫ x ^ (2 * m) * exp (-b * x ^ 2) dx = (2 * m)! * √(π / b) / (2 ^ (2 * m) * m! * b ^ m)`,
  valid for all `b : ℝ`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Nat

namespace TauCeti

/-- The monomial Gaussian weight `x ↦ x ^ k * exp (-b * x ^ 2)` is integrable on `(0, ∞)` if and
only if `0 < b`. -/
theorem integrableOn_Ioi_pow_mul_exp_neg_mul_sq_iff {b : ℝ} (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) (Ioi 0) ↔ 0 < b := by
  refine ⟨fun h => ?_, fun hb => ?_⟩
  · by_contra! hb
    have hmono : IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-b * x ^ 2)) (Ioi 1) :=
      h.mono_set (Ioi_subset_Ioi zero_le_one)
    have hle : ∫⁻ _ : ℝ in Ioi (1 : ℝ), 1 ≤
        ∫⁻ x : ℝ in Ioi (1 : ℝ), ‖x ^ k * Real.exp (-b * x ^ 2)‖₊ := by
      refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
      have hx1 : (1 : ℝ) ≤ x := (mem_Ioi.mp hx).le
      have hpow : (1 : ℝ) ≤ x ^ k := one_le_pow₀ hx1
      have hexp : (1 : ℝ) ≤ Real.exp (-b * x ^ 2) :=
        Real.one_le_exp (mul_nonneg (neg_nonneg.mpr hb) (sq_nonneg x))
      have hprod : (1 : ℝ) ≤ x ^ k * Real.exp (-b * x ^ 2) :=
        one_le_mul_of_one_le_of_one_le hpow hexp
      exact_mod_cast (by
        rw [Real.norm_of_nonneg (by linarith)]
        exact hprod : (1 : ℝ) ≤ ‖x ^ k * Real.exp (-b * x ^ 2)‖)
    have hinf : ∫⁻ _ : ℝ in Ioi (1 : ℝ), (1 : ℝ≥0∞) = ⊤ := by
      simp [Real.volume_Ioi]
    exact (hinf ▸ hle.trans_lt hmono.2).ne rfl
  · exact (integrableOn_rpow_mul_exp_neg_mul_sq hb
      (by linarith [Nat.cast_nonneg (α := ℝ) k] : (-1 : ℝ) < k)).congr_fun
      (fun x _ => by dsimp only; rw [Real.rpow_natCast]) measurableSet_Ioi

/-- Half-line monomial Gaussian moment in terms of `Real.Gamma`: for `0 < b` and `k : ℕ`,
`∫ x in Ioi 0, x ^ k * exp (-b * x ^ 2) = Γ((k + 1) / 2) / (2 * b ^ ((k + 1) / 2))`.
For `b < 0` and odd `k`, equality fails because the Bochner integral vanishes by
`MeasureTheory.integral_undef` while the right-hand side is nonzero (at `b = 0`, equality holds
only by `div_zero`). -/
theorem integral_Ioi_pow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (k : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-b * x ^ 2) =
      Real.Gamma (((k : ℝ) + 1) / 2) / (2 * b ^ (((k : ℝ) + 1) / 2)) := by
  have heq : ∫ x in Ioi (0 : ℝ), x ^ k * Real.exp (-b * x ^ 2) =
      ∫ x in Ioi (0 : ℝ), x ^ (k : ℝ) * Real.exp (-b * x ^ (2 : ℝ)) :=
    setIntegral_congr_fun measurableSet_Ioi fun x _ => by rw [Real.rpow_natCast, Real.rpow_two]
  rw [heq, integral_rpow_mul_exp_neg_mul_rpow two_pos
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) hb,
    neg_div, Real.rpow_neg hb.le]
  ring

/-- Even-order half-line Gaussian moment in closed factorial form: for every `b : ℝ` and `m : ℕ`,
`∫ x in Ioi 0, x ^ (2 * m) * exp (-b * x ^ 2)` equals
`(2 * m)! * √(π / b) / (2 ^ (2 * m + 1) * m! * b ^ m)`.
For `b ≤ 0`, both sides vanish by `MeasureTheory.integral_undef` and
`Real.sqrt_eq_zero_of_nonpos`. -/
theorem integral_Ioi_pow_two_mul_mul_exp_neg_mul_sq (b : ℝ) (m : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * m) * Real.exp (-b * x ^ 2) =
      ((2 * m)! : ℝ) * Real.sqrt (Real.pi / b) / (2 ^ (2 * m + 1) * (m ! : ℝ) * b ^ m) := by
  rcases le_or_gt b 0 with hb | hb
  · rw [integral_undef (mt (integrableOn_Ioi_pow_mul_exp_neg_mul_sq_iff (2 * m)).mp
      (not_lt.mpr hb)),
      Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonneg_of_nonpos Real.pi_pos.le hb),
      mul_zero, zero_div]
  · rw [integral_Ioi_pow_mul_exp_neg_mul_sq hb (2 * m)]
    have harg : (((2 * m : ℕ) : ℝ) + 1) / 2 = (m : ℝ) + 1 / 2 := by push_cast; ring
    have h4 : (4 : ℝ) ^ m = 2 ^ (2 * m) := by rw [pow_mul]; norm_num
    rw [harg, Real.Gamma_nat_add_half_eq_factorial, Real.rpow_add hb, Real.rpow_natCast,
      ← Real.sqrt_eq_rpow, Real.sqrt_div Real.pi_pos.le, h4, pow_succ]
    have hfact : (m ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hsqrt : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
    field_simp [hfact, hsqrt, pow_ne_zero m hb.ne']

/-- Odd-order half-line Gaussian moment in closed factorial form: for `0 < b` and `m : ℕ`,
`∫ x in Ioi 0, x ^ (2 * m + 1) * exp (-b * x ^ 2) = m! / (2 * b ^ (m + 1))`.
For `b < 0`, equality fails because the Bochner integral vanishes by
`MeasureTheory.integral_undef` while the right-hand side is nonzero (at `b = 0`, equality holds
only by `div_zero`). -/
theorem integral_Ioi_pow_two_mul_add_one_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) (m : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * m + 1) * Real.exp (-b * x ^ 2) =
      (m ! : ℝ) / (2 * b ^ (m + 1)) := by
  rw [integral_Ioi_pow_mul_exp_neg_mul_sq hb (2 * m + 1)]
  have harg : (((2 * m + 1 : ℕ) : ℝ) + 1) / 2 = (m : ℝ) + 1 := by push_cast; ring
  rw [harg, Real.Gamma_nat_eq_factorial, ← Nat.cast_add_one, Real.rpow_natCast]

/-- Even-order Gaussian moment over the whole real line: for every `b : ℝ` and `m : ℕ`,
`∫ x ^ (2 * m) * exp (-b * x ^ 2) dx = (2 * m)! * √(π / b) / (2 ^ (2 * m) * m! * b ^ m)`, twice
the half-line moment `TauCeti.integral_Ioi_pow_two_mul_mul_exp_neg_mul_sq`.
For `b ≤ 0`, both sides vanish by `MeasureTheory.integral_undef` and
`Real.sqrt_eq_zero_of_nonpos`. -/
theorem integral_pow_two_mul_mul_exp_neg_mul_sq (b : ℝ) (m : ℕ) :
    ∫ x : ℝ, x ^ (2 * m) * Real.exp (-b * x ^ 2) =
      ((2 * m)! : ℝ) * Real.sqrt (Real.pi / b) / (2 ^ (2 * m) * (m ! : ℝ) * b ^ m) := by
  have h := integral_comp_abs (f := fun x : ℝ => x ^ (2 * m) * Real.exp (-b * x ^ 2))
  simp only [(even_two_mul m).pow_abs, sq_abs] at h
  rw [h, integral_Ioi_pow_two_mul_mul_exp_neg_mul_sq, pow_succ]
  ring

end TauCeti

end
