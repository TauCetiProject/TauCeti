/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Elementary Gaussian bounds

A polynomial weight times a real Gaussian is bounded above. This file records an explicit
upper bound for `(1 + r) ^ m * exp (-a r²)`, the scalar estimate behind the decay of Gaussian
Schwartz functions, together with the cocompact decay of `t ↦ exp (c - δ * t ^ 2)`.

## Main results

* `TauCeti.one_add_pow_mul_exp_neg_mul_sq_le`: an explicit upper bound for
  `(1 + r) ^ m * exp (-a r²)`.
* `TauCeti.norm_exp_ofReal_mul_sub_sq`, `TauCeti.norm_exp_ofReal_mul_sub_sq_le`: modulus and closed
  unit-strip bound for `z ↦ exp (δ * (z - θ) ^ 2)`.
* `TauCeti.tendsto_exp_sub_mul_sq_cocompact`,
  `TauCeti.tendsto_norm_exp_ofReal_mul_add_mul_I_sub_sq_cocompact`: cocompact decay of
  `t ↦ exp (c - δ * t ^ 2)` and `t ↦ ‖exp (δ * (a + t * I - θ) ^ 2)‖`.
-/

public section

open Filter
open scoped Nat Topology

namespace TauCeti

/-- For `0 < a`, the function `r ↦ (1 + r) ^ m * exp (-a r²)` is bounded above by the explicit
constant `m! / (a / 2) ^ m * exp a`. -/
theorem one_add_pow_mul_exp_neg_mul_sq_le {a : ℝ} (ha : 0 < a) (m : ℕ) {r : ℝ} :
    (1 + r) ^ m * Real.exp (-a * r ^ 2) ≤ m ! / (a / 2) ^ m * Real.exp a := by
  set u := 1 + r
  rcases lt_or_ge |u| 1 with hu | hu
  · -- `|u| < 1`: the left-hand side is at most `1`, and so is no larger than the constant.
    have h := Real.pow_div_factorial_le_exp (x := a / 2) (by positivity) m
    rw [div_le_iff₀ (by positivity)] at h
    have hC : 1 ≤ m ! / (a / 2) ^ m * Real.exp a := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
      calc (a / 2) ^ m ≤ Real.exp (a / 2) * m ! := h
        _ ≤ Real.exp a * m ! := by gcongr; linarith
        _ = m ! * Real.exp a := mul_comm _ _
    refine le_trans ?_ hC
    calc u ^ m * Real.exp (-a * r ^ 2) ≤ |u| ^ m * Real.exp (-a * r ^ 2) :=
          mul_le_mul_of_nonneg_right ((le_abs_self _).trans_eq (abs_pow u m))
            (Real.exp_pos _).le
      _ ≤ 1 * 1 := mul_le_mul (pow_le_one₀ (abs_nonneg u) hu.le)
          (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])) (Real.exp_pos _).le zero_le_one
      _ = 1 := one_mul 1
  · -- `r² ≥ u² / 2 - 1`, so `exp (-a r²) ≤ exp a * exp (-(a / 2) u²)`.
    have hexp : Real.exp (-a * r ^ 2) ≤ Real.exp a * Real.exp (-(a / 2 * u ^ 2)) := by
      rw [← Real.exp_add]
      gcongr
      nlinarith [sq_nonneg (r - 1)]
    -- `u ^ m ≤ (u²) ^ m ≤ m! exp ((a / 2) u²) / (a / 2) ^ m`.
    have hpow : u ^ m ≤ m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) := by
      have h := Real.pow_div_factorial_le_exp (x := a / 2 * u ^ 2) (by positivity) m
      rw [div_le_iff₀ (by positivity), mul_pow] at h
      calc u ^ m ≤ |u| ^ m := (le_abs_self _).trans_eq (abs_pow u m)
        _ ≤ (|u| ^ 2) ^ m := by
            rw [← pow_mul]; exact pow_le_pow_right₀ hu (by omega)
        _ = (u ^ 2) ^ m := by rw [sq_abs]
        _ = (a / 2) ^ m * (u ^ 2) ^ m / (a / 2) ^ m := by field_simp
        _ ≤ Real.exp (a / 2 * u ^ 2) * m ! / (a / 2) ^ m := by gcongr
        _ = m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) := by ring
    calc u ^ m * Real.exp (-a * r ^ 2)
        ≤ m ! / (a / 2) ^ m * Real.exp (a / 2 * u ^ 2) *
            (Real.exp a * Real.exp (-(a / 2 * u ^ 2))) := by gcongr
      _ = m ! / (a / 2) ^ m * Real.exp a := by
        rw [mul_assoc, mul_left_comm (Real.exp (a / 2 * u ^ 2)), ← Real.exp_add, add_neg_cancel,
          Real.exp_zero, mul_one]

/-- For `0 < δ` and any `c : ℝ`, `t ↦ exp (c - δ * t ^ 2)` tends to `0` along `cocompact ℝ`. -/
theorem tendsto_exp_sub_mul_sq_cocompact {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (c - δ * t ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (cocompact ℝ) atTop :=
    ((tendsto_pow_atTop two_ne_zero).comp (tendsto_norm_cocompact_atTop (E := ℝ))).congr
      fun _ => by simp
  refine Real.tendsto_exp_atBot.comp ?_
  simpa [sub_eq_add_neg] using
    tendsto_atBot_add_const_left _ c ((tendsto_neg_atTop_atBot.comp hsq).const_mul_atBot hδ)

/-- Modulus of the complex Gaussian factor `exp (δ * (z - θ) ^ 2)`. -/
theorem norm_exp_ofReal_mul_sub_sq (δ θ : ℝ) (z : ℂ) :
    ‖Complex.exp (δ * (z - θ) ^ 2)‖ = Real.exp (δ * ((z.re - θ) ^ 2 - z.im ^ 2)) := by
  rw [Complex.norm_exp]; congr 1; simp [sq]

/-- Uniform bound on `exp (δ * (z - θ) ^ 2)` (`0 ≤ δ`) over the closed unit strip `0 ≤ re z ≤ 1`. -/
theorem norm_exp_ofReal_mul_sub_sq_le {δ : ℝ} (hδ : 0 ≤ δ) (θ : ℝ) {z : ℂ}
    (hz : z.re ∈ Set.Icc 0 1) :
    ‖Complex.exp (δ * (z - θ) ^ 2)‖ ≤ Real.exp (δ * (|θ| + 1) ^ 2) := by
  rw [norm_exp_ofReal_mul_sub_sq]
  refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hδ)
  have h : (z.re - θ) ^ 2 ≤ (|θ| + 1) ^ 2 :=
    sq_le_sq' (by linarith [hz.1, le_abs_self θ]) (by linarith [hz.2, neg_abs_le θ])
  nlinarith [sq_nonneg z.im]

/-- Along any vertical line `a + t * I`, `‖exp (δ * (a + t * I - θ) ^ 2)‖` tends to `0` at
infinity for `0 < δ`. -/
theorem tendsto_norm_exp_ofReal_mul_add_mul_I_sub_sq_cocompact {δ : ℝ} (hδ : 0 < δ) (θ a : ℝ) :
    Tendsto (fun t : ℝ => ‖Complex.exp (δ * ((a : ℂ) + t * Complex.I - θ) ^ 2)‖)
      (cocompact ℝ) (𝓝 0) :=
  (tendsto_exp_sub_mul_sq_cocompact hδ (δ * (a - θ) ^ 2)).congr fun t => by
    rw [norm_exp_ofReal_mul_sub_sq]; congr 1; simp [mul_sub]

end TauCeti
