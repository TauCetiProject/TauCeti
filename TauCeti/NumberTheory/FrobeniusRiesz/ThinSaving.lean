/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Transferring Riesz savings to the thin cutoff

The thin places in a Frobenius-restricted average use arguments at least
`exp (x ^ (ε / 3)) / 3`. A uniform logarithmic Riesz estimate at those arguments gives
an `exp (-D * x ^ (ε / 8))` saving, despite a conductor whose logarithm grows like
`x ^ (ε / 5) * (log x)^2`. With `D = 1`, this saving pays for the polynomial number
of thin-place terms in the average.

The scales are those of Levent Alpöge's `Formalism.MainNotions.ShortIntervalPrimes.Conclusion6`.
-/

public section

open Filter Real
open scoped Topology

namespace TauCeti

-- Use half of the power of `x` to absorb the constant from dividing the cutoff by three.
private theorem eventually_half_rpow_le_log_thinCutoff {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ y ≥ exp (x ^ (ε / 3)) / 3, x ^ (ε / 3) / 2 ≤ log y := by
  have h := (tendsto_rpow_atTop (show 0 < ε / 3 by positivity)).eventually_ge_atTop (2 * log 3)
  filter_upwards [h] with x hx y hy
  have hcut : 0 < exp (x ^ (ε / 3)) / 3 := by positivity
  have hlog := log_le_log hcut hy
  rw [log_div (exp_ne_zero _) (by norm_num), log_exp] at hlog
  linarith

-- The exponent margin is `31ε/150 - ε/5 = ε/150`.
private theorem eventually_conductor_le_thinCutoff {ε : ℝ} (hε : 0 < ε) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ y ≥ exp (x ^ (ε / 3)) / 3,
      A * x ^ (ε / 5) * log x ^ 2 ≤ log y ^ (31 / 50 : ℝ) := by
  have h := ((isLittleO_log_rpow_rpow_atTop 2 (show 0 < ε / 150 by positivity)).const_mul_left
    A).bound (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2) (31 / 50))
  filter_upwards [h, eventually_ge_atTop (0 : ℝ), eventually_half_rpow_le_log_thinCutoff hε]
    with x hs hx hlog y hy
  have hs' : A * log x ^ 2 ≤ (1 / 2 : ℝ) ^ (31 / 50 : ℝ) * x ^ (ε / 150) := by
    refine (le_abs_self _).trans ?_
    simpa only [Real.norm_eq_abs, rpow_two, abs_of_nonneg (rpow_nonneg hx _)] using hs
  calc
    _ = (A * log x ^ 2) * x ^ (ε / 5) := by ring
    _ ≤ ((1 / 2 : ℝ) ^ (31 / 50 : ℝ) * x ^ (ε / 150)) * x ^ (ε / 5) := by gcongr
    _ = (x ^ (ε / 3) / 2) ^ (31 / 50 : ℝ) := by
      rw [div_eq_mul_inv (x ^ (ε / 3)), mul_rpow (rpow_nonneg hx _) (by positivity), ← rpow_mul hx,
        mul_assoc, ← rpow_add_of_nonneg hx (by positivity) (by positivity)]
      simp only [one_div]
      rw [show ε / 150 + ε / 5 = ε / 3 * (31 / 50) by ring, mul_comm]
    _ ≤ _ := rpow_le_rpow (by positivity) (hlog y hy) (by norm_num)

-- The exponent margin is `19ε/150 - ε/8 = ε/600`.
private theorem eventually_rate_le_thinCutoff {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) (D : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ y ≥ exp (x ^ (ε / 3)) / 3,
      D * x ^ (ε / 8) ≤ c * log y ^ (19 / 50 : ℝ) := by
  have hC : 0 < c * (1 / 2 : ℝ) ^ (19 / 50 : ℝ) := by positivity
  have h := ((isLittleO_rpow_rpow_atTop (show ε / 8 < ε / 3 * (19 / 50) by linarith)).const_mul_left
    D).bound hC
  filter_upwards [h, eventually_ge_atTop (0 : ℝ), eventually_half_rpow_le_log_thinCutoff hε]
    with x hs hx hlog y hy
  calc
    _ ≤ (c * (1 / 2 : ℝ) ^ (19 / 50 : ℝ)) * x ^ (ε / 3 * (19 / 50)) := by
      exact (le_abs_self _).trans (by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (rpow_nonneg hx _)] using hs)
    _ = c * (x ^ (ε / 3) / 2) ^ (19 / 50 : ℝ) := by
      rw [div_eq_mul_inv (x ^ (ε / 3)), mul_rpow (rpow_nonneg hx _) (by positivity), ← rpow_mul hx,
        one_div]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (rpow_le_rpow (by positivity) (hlog y hy) (by norm_num)) hc.le

/-- Transfer a conductor-uniform logarithmic first Riesz bound to the thin cutoff.
The class `S` may include the trivial character. The resulting threshold is chosen before the
level `N`, the character at that level, and its Riesz argument `y`. -/
theorem eventually_norm_rieszRemainder_le_at_thinCutoff {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c)
    (A D : ℝ) {S : Set PrimitiveDirichletCharacter}
    (hprofile : ∀ᶠ y : ℝ in atTop, ∀ χ ∈ S, log χ.level ≤ log y ^ (31 / 50 : ℝ) →
      ‖χ.rieszRemainder y‖ ≤ y * exp (-c * log y ^ (19 / 50 : ℝ))) :
    ∀ᶠ x : ℝ in atTop, ∀ (N : ℕ) [NeZero N], log N ≤ A * x ^ (ε / 5) * log x ^ 2 →
      ∀ χ : DirichletCharacter ℂ N, PrimitiveDirichletCharacter.of χ ∈ S →
      ∀ y ≥ exp (x ^ (ε / 3)) / 3,
        ‖(PrimitiveDirichletCharacter.of χ).rieszRemainder y‖ ≤ y * exp (-D * x ^ (ε / 8)) := by
  obtain ⟨Y, hY⟩ := hprofile.exists_forall_of_atTop
  have hp : 0 < ε / 3 := by positivity
  have hcut := ((tendsto_exp_atTop.comp (tendsto_rpow_atTop hp)).atTop_div_const
    (by norm_num : 0 < (3 : ℝ))).eventually_ge_atTop Y
  filter_upwards [hcut, eventually_conductor_le_thinCutoff hε A,
    eventually_rate_le_thinCutoff hε hc D] with x hx hN hrate N h₀ hlev χ hχ y hy
  have hcond : log (PrimitiveDirichletCharacter.of χ).level ≤ log N := by
    have hpos : 0 < ((PrimitiveDirichletCharacter.of χ).level : ℝ) := by positivity
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero h₀.out)
      (PrimitiveDirichletCharacter.level_of_dvd χ)
    exact log_le_log hpos (by exact_mod_cast hle)
  have hbound := hY y (hx.trans hy) _ hχ (hcond.trans (hlev.trans (hN y hy)))
  exact hbound.trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith [hrate y hy]))
    ((by positivity : 0 ≤ exp (x ^ (ε / 3)) / 3).trans hy))

/-- The unit-coefficient thin-cutoff saving pays for the factor `2 * f * (x + 1)` in the
Frobenius average when the host degree `f` is polynomially bounded in `x`. -/
theorem eventually_thinCutoff_saving_cost_le {ε : ℝ} (hε : 0 < ε) (B M : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ f ≤ B * x ^ M, 2 * f * (x + 1) * exp (-(x ^ (ε / 8))) ≤ 1 / x := by
  have hp : 0 < ε / 8 := by positivity
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((M + 2) / (ε / 8)) 1 one_pos).comp
    (tendsto_rpow_atTop hp)).const_mul (4 * max B 0)
  rw [mul_zero] at h
  have hsmall := h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hs hx f hf
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hm : (x ^ (ε / 8)) ^ ((M + 2) / (ε / 8)) = x ^ (M + 2) := by
    rw [← rpow_mul hx₀.le, mul_div_cancel₀ _ hp.ne']
  simp only [Function.comp_apply, neg_one_mul, hm] at hs
  have hf' : f ≤ max B 0 * x ^ M := hf.trans (by gcongr; exact le_max_left _ _)
  rw [le_div_iff₀ hx₀]
  calc
    _ ≤ 2 * (max B 0 * x ^ M) * (2 * x) * exp (-(x ^ (ε / 8))) * x := by
      gcongr
      linarith
    _ = 4 * max B 0 * (x ^ (M + 2) * exp (-(x ^ (ε / 8)))) := by
      rw [rpow_add hx₀, rpow_two]
      ring
    _ ≤ _ := hs.le

end TauCeti
