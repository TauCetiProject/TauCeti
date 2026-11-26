/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
public import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannSiegelTheta.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# The Stirling asymptotic of the Riemann–Siegel theta function

Writing `log Γ` at `z = 1/4 + iT/2` as Stirling's main term plus the remainder `R = `
`TauCeti.stirlingRemainder` gives the exact identity
`ϑ(T) = (T/2) log |z| - (arg z)/4 - T/2 - (T/2) log π + Im R(z)`
(`TauCeti.riemannSiegelTheta_eq_add_im_stirlingRemainder`). For `T > 0`, the three error terms
against `(T/2) log (T/(2πe)) - π/8` are at most `1/(16T)` (the modulus, from
`Complex.abs_log_norm_sub_log_abs_im_le`), and `1/(8T)` (the argument, from
`Complex.pi_div_two_sub_arg_le_div`)
and `1/(2T)` (the remainder, from Nemes's bound `TauCeti.norm_stirlingRemainder_le_of_re_nonneg`).

## Main results

* `TauCeti.riemannSiegelTheta_eq_add_im_stirlingRemainder`: the exact Stirling form of `ϑ`.
* `TauCeti.abs_riemannSiegelTheta_sub_le`: the explicit asymptotic
  `|ϑ(T) - ((T/2) log (T/(2πe)) - π/8)| ≤ 1/T` for `T > 0`, and its `O(1/T)` form
  `TauCeti.isBigO_riemannSiegelTheta_sub`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (revised by
  D. R. Heath-Brown), §9.3.
* G. Nemes, *Error bounds and exponential improvements for the asymptotic expansions of the gamma
  function and its reciprocal*, Proc. Roy. Soc. Edinburgh Sect. A 145 (2015), 571–596, for the
  bound on the Stirling remainder used in the asymptotic.
-/

public section

open Complex Filter Asymptotics
open scoped Real

namespace TauCeti

/-- **The Stirling form of `ϑ`.** At `z = 1/4 + iT/2`,
`ϑ(T) = (T/2) log |z| - (arg z)/4 - T/2 - (T/2) log π + Im R(z)`, where `R` is the Stirling
remainder `TauCeti.stirlingRemainder`. -/
theorem riemannSiegelTheta_eq_add_im_stirlingRemainder (T : ℝ) :
    riemannSiegelTheta T =
      T / 2 * Real.log ‖(1 / 4 + (T : ℂ) / 2 * I)‖ - (1 / 4 + (T : ℂ) / 2 * I).arg / 4 - T / 2 -
        T / 2 * Real.log π + (stirlingRemainder (1 / 4 + (T : ℂ) / 2 * I)).im := by
  rw [riemannSiegelTheta_eq_im_logGamma_sub, logGamma_eq_add_stirlingRemainder]
  simp only [add_im, sub_im, mul_im, log_re, log_im, ofReal_im]
  simp
  ring

/-- The modulus term: `0 ≤ (T/2) log |1/4 + iT/2| - (T/2) log (T/2) ≤ 1/(16T)` for `T > 0`. -/
private theorem log_norm_quarter_add_bounds {T : ℝ} (hT : 0 < T) :
    0 ≤ T / 2 * Real.log ‖(1 / 4 + (T : ℂ) / 2 * I)‖ - T / 2 * Real.log (T / 2) ∧
      T / 2 * Real.log ‖(1 / 4 + (T : ℂ) / 2 * I)‖ - T / 2 * Real.log (T / 2) ≤ 1 / (16 * T) := by
  set z : ℂ := 1 / 4 + (T : ℂ) / 2 * I
  have hre : z.re = 1 / 4 := by simp [z]
  have him : z.im = T / 2 := by simp [z]
  have hzim : 0 < z.im := him ▸ half_pos hT
  have h0 := Real.log_le_log hzim (im_le_norm z)
  have h1 := (le_abs_self _).trans (Complex.abs_log_norm_sub_log_abs_im_le hzim.ne')
  rw [him] at h0
  simp only [hre, him, abs_of_pos (by positivity : 0 < T / 2), one_div, tsub_le_iff_right] at h1
  have hsq : T / 2 * ((1 / 4 / (T / 2)) ^ 2 / 2) = 1 / (16 * T) := by
    field_simp
    ring
  rw [← mul_sub]
  constructor
  · exact mul_nonneg (half_pos hT).le (sub_nonneg.mpr h0)
  · have hm := mul_le_mul_of_nonneg_left h1 (half_pos hT).le
    nlinarith [hm, hsq]

/-- The argument term: `0 ≤ π/8 - arg (1/4 + iT/2) / 4 ≤ 1/(8T)` for `T > 0`, since
`0 ≤ π/2 - arg z ≤ re z / im z` in the first quadrant. -/
private theorem arg_quarter_add_bounds {T : ℝ} (hT : 0 < T) :
    0 ≤ π / 8 - (1 / 4 + (T : ℂ) / 2 * I).arg / 4 ∧
      π / 8 - (1 / 4 + (T : ℂ) / 2 * I).arg / 4 ≤ 1 / (8 * T) := by
  set z : ℂ := 1 / 4 + (T : ℂ) / 2 * I
  have hre : z.re = 1 / 4 := by simp [z]
  have him : z.im = T / 2 := by simp [z]
  have hre0 : 0 ≤ z.re := by rw [hre]; norm_num
  have h0 : z.arg ≤ π / 2 := arg_le_pi_div_two_iff.mpr (Or.inl hre0)
  have h1 := pi_div_two_sub_arg_le_div hre0 (him ▸ half_pos hT)
  have hq : z.re / z.im / 4 = 1 / (8 * T) := by
    rw [hre, him]
    field_simp
    ring
  constructor <;> linarith

/-- The remainder term: `|Im R(1/4 + iT/2)| ≤ 1/(2T)` for `T > 0`, from Nemes's bound
`|R(z)| ≤ 1/(4|z|)` on the nonzero points of the closed right half-plane and `|z| ≥ T/2`. -/
private theorem abs_im_stirlingRemainder_quarter_add_le {T : ℝ} (hT : 0 < T) :
    |(stirlingRemainder (1 / 4 + (T : ℂ) / 2 * I)).im| ≤ 1 / (2 * T) := by
  set z : ℂ := 1 / 4 + (T : ℂ) / 2 * I
  have hre : 0 < z.re := by simp [z]
  have him : z.im = T / 2 := by simp [z]
  have hnorm : T / 2 ≤ ‖z‖ := him ▸ im_le_norm z
  have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos hre
  calc |(stirlingRemainder z).im| ≤ ‖stirlingRemainder z‖ := abs_im_le_norm _
    _ ≤ 1 / (4 * ‖z‖) := norm_stirlingRemainder_le_of_re_nonneg hre.le hz0
    _ ≤ 1 / (4 * (T / 2)) := by gcongr
    _ = 1 / (2 * T) := by ring

/-- **The asymptotic of `ϑ` with an explicit error.** For `T > 0`,
`|ϑ(T) - ((T/2) log (T/(2πe)) - π/8)| ≤ 1/T`. -/
theorem abs_riemannSiegelTheta_sub_le {T : ℝ} (hT : 0 < T) :
    |riemannSiegelTheta T - (T / 2 * Real.log (T / (2 * π * Real.exp 1)) - π / 8)| ≤ 1 / T := by
  obtain ⟨hm0, hm1⟩ := log_norm_quarter_add_bounds hT
  obtain ⟨ha0, ha1⟩ := arg_quarter_add_bounds hT
  have hR := abs_le.mp (abs_im_stirlingRemainder_quarter_add_le hT)
  have hmain : T / 2 * Real.log (T / (2 * π * Real.exp 1)) =
      T / 2 * Real.log (T / 2) - T / 2 - T / 2 * Real.log π := by
    simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_exp]
    ring
  have h16 : 1 / (16 * T) + 1 / (8 * T) + 1 / (2 * T) = 11 / 16 * (1 / T) := by
    field_simp
    ring
  have hT1 : 0 < 1 / T := one_div_pos.mpr hT
  rw [riemannSiegelTheta_eq_add_im_stirlingRemainder, hmain, abs_le]
  constructor <;> linarith

/-- **The asymptotic of `ϑ`:** `ϑ(T) = (T/2) log (T/(2πe)) - π/8 + O(1/T)` as `T → ∞`. -/
theorem isBigO_riemannSiegelTheta_sub :
    (fun T ↦ riemannSiegelTheta T - (T / 2 * Real.log (T / (2 * π * Real.exp 1)) - π / 8))
      =O[atTop] fun T ↦ T⁻¹ := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  simpa [abs_of_pos hT] using abs_riemannSiegelTheta_sub_le hT

end TauCeti
