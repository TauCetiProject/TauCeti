/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters

/-!
# The archimedean scale in the size of theta derivatives

The size of a derivative of order `j` at principal level `M` is measured by
`log (j!) + j * log (M / Ω)`. Here `Ω` incorporates the root discriminant and the
constant from the logarithmic derivative of the base quadratic L-function at one.
The estimates below control the coefficient of `j` in terms of the large cutoff `b`,
using the root-discriminant bounds and the separation of the cutoffs.

The normalization and constants follow `New.Parameters.bigOmega` and
`New.Data.log_M_div_bigOmega_mem_Icc` in lsernau/grh-lean, commit `72fead1`.
-/

public section

open Real Set

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters)

/-- The quadratic logarithmic correction to the archimedean scale, for the Legendre
character of `ℚ(√-d)` at the prime `d` of `P`. -/
noncomputable def jetLogCorrection : ℝ :=
  eulerMascheroniConstant - (logDeriv (DirichletCharacter.LFunction
    (N := P.d) ((quadraticChar (ZMod P.d)).ringHomComp (Int.castRingHom ℂ))) 1).re

/-- The logarithmic correction is Euler's constant minus the real part of `L′/L` at one. -/
theorem jetLogCorrection_def :
    P.jetLogCorrection = eulerMascheroniConstant - (logDeriv (DirichletCharacter.LFunction
      (N := P.d) ((quadraticChar (ZMod P.d)).ringHomComp (Int.castRingHom ℂ))) 1).re := (rfl)

/-- If the log-log scale of `b` dominates the quadratic correction and `log (2π)`, then the
cutoff condition `(log b)^100 ≤ x` supplies the logarithmic budget for `Ω`. -/
theorem abs_jetLogCorrection_add_log_le_log_of_cutoffs {x b : ℕ}
    (hcor : |P.jetLogCorrection| ≤ log (log (b : ℝ)))
    (hπ : log (2 * π) ≤ log (log (b : ℝ))) (hx : log (b : ℝ) ^ 100 ≤ (x : ℝ)) :
    |P.jetLogCorrection| + log (2 * π) ≤ log (x : ℝ) := by
  have hπpos : 0 < log (2 * π) := log_pos (by linarith [Real.two_le_pi])
  have hbb : 0 < log (log (b : ℝ)) := hπpos.trans_le hπ
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hbb
  have hbReal : 1 ≤ (b : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hb
  have hl : 0 < log (b : ℝ) := lt_of_le_of_ne (log_nonneg hbReal) (by
    intro he
    simp [← he] at hbb)
  have hh := log_le_log (pow_pos hl 100) hx
  norm_num [log_pow] at hh
  linarith

variable (E : Type*) [Field E] [NumberField E]

/-- The scale `Ω` relating the principal level to the size of theta derivatives over `E`. -/
noncomputable def jetScale : ℝ :=
  exp P.jetLogCorrection * (2 * π) / NumberField.rootDiscr E

/-- The scale is `2π` times the exponential of the correction, divided by the root discriminant. -/
theorem jetScale_def :
    P.jetScale E = exp P.jetLogCorrection * (2 * π) / NumberField.rootDiscr E := (rfl)

/-- The archimedean scale is strictly positive. -/
theorem jetScale_pos : 0 < P.jetScale E := by
  have hd : (0 : ℝ) < ↑|NumberField.discr E| := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero E)
  rw [jetScale_def, NumberField.rootDiscr_def]
  exact div_pos (mul_pos (exp_pos _) (by positivity)) (rpow_pos_of_pos hd _)

/-- The correction, `log (2π)`, and the log root discriminant contribute additively to
`log Ω`, with the discriminant contribution subtracted. -/
theorem log_jetScale :
    log (P.jetScale E) = P.jetLogCorrection + log (2 * π) - log (NumberField.rootDiscr E) := by
  have hπ : 0 < 2 * π := by positivity
  have hd : NumberField.rootDiscr E ≠ 0 := by
    intro h
    simpa [jetScale_def, h] using P.jetScale_pos E
  rw [jetScale_def, log_div (mul_pos (exp_pos _) hπ).ne' hd,
    log_mul (exp_pos _).ne' hπ.ne', log_exp]

/-- If the root discriminant is between `x^10` and `x^12`, the archimedean scale is between
`x^(-13)` and `1` once the logarithmic correction and the constant `2π` fit in `log x`. -/
theorem jetScale_mem_Icc {x : ℕ} (hscale : |P.jetLogCorrection| + log (2 * π) ≤ log (x : ℝ))
    (hdiscr : NumberField.rootDiscr E ∈ Icc ((x : ℝ) ^ 10) ((x : ℝ) ^ 12)) :
    P.jetScale E ∈ Icc ((x : ℝ) ^ (-13 : ℤ)) 1 := by
  have hπ : 0 < log (2 * π) := log_pos (by linarith [Real.two_le_pi])
  have hxlog : 0 < log (x : ℝ) := by linarith [abs_nonneg P.jetLogCorrection]
  have hx : 0 < (x : ℝ) := zero_lt_one.trans ((log_pos_iff (by positivity)).1 hxlog)
  have hlow := log_le_log (pow_pos hx _) hdiscr.1
  have hhigh := log_le_log ((pow_pos hx 10).trans_le hdiscr.1) hdiscr.2
  norm_num [log_pow] at hlow hhigh
  constructor
  · apply (log_le_log_iff (zpow_pos hx _) (P.jetScale_pos E)).mp
    rw [log_zpow, log_jetScale]
    push_cast
    linarith [neg_abs_le P.jetLogCorrection]
  · apply (log_le_log_iff (P.jetScale_pos E) zero_lt_one).mp
    rw [log_jetScale, log_one]
    linarith [le_abs_self P.jetLogCorrection]

/-- Given the discriminant bounds and separated cutoffs, the log of the principal level divided
by the archimedean scale lies between `20 log b` and `23 log b`. -/
theorem log_M_div_jetScale_mem_Icc {x b : ℕ} {M : ℝ}
    (hscale : |P.jetLogCorrection| + log (2 * π) ≤ log (x : ℝ))
    (hdiscr : NumberField.rootDiscr E ∈ Icc ((x : ℝ) ^ 10) ((x : ℝ) ^ 12))
    (hxb : x ^ 13 ≤ b) (hM : M ∈ Icc ((b : ℝ) ^ 20) ((b : ℝ) ^ 22)) :
    log (M / P.jetScale E) ∈ Icc (20 * log (b : ℝ)) (23 * log (b : ℝ)) := by
  have hπ : 0 < log (2 * π) := log_pos (by linarith [Real.two_le_pi])
  have hxlog : 0 < log (x : ℝ) := by linarith [abs_nonneg P.jetLogCorrection]
  have hx : 0 < (x : ℝ) := zero_lt_one.trans ((log_pos_iff (by positivity)).1 hxlog)
  have hxb' : (x : ℝ) ^ 13 ≤ (b : ℝ) := by exact_mod_cast hxb
  have hb := (pow_pos hx 13).trans_le hxb'
  have hMpos := (pow_pos hb 20).trans_le hM.1
  have hΩ := P.jetScale_mem_Icc E hscale hdiscr
  have hx_b := log_le_log (pow_pos hx 13) hxb'
  have hMlow := log_le_log (pow_pos hb 20) hM.1
  have hMhigh := log_le_log hMpos hM.2
  have hΩlow := log_le_log (zpow_pos hx (-13)) hΩ.1
  have hΩhigh := log_le_log (P.jetScale_pos E) hΩ.2
  norm_num [log_pow] at hx_b hMlow hMhigh
  norm_num [log_zpow] at hΩlow
  rw [log_one] at hΩhigh
  rw [log_div hMpos.ne' (P.jetScale_pos E).ne']
  exact ⟨by linarith, by linarith⟩

end TauCeti.OneSidedBound.Parameters
