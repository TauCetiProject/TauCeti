/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
public import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannSiegelTheta.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Sector
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The Stirling asymptotic of the Riemann–Siegel theta function

Writing `log Γ` at `z = 1/4 + iT/2` as Stirling's main term plus the remainder
`R = TauCeti.stirlingRemainder` gives the identity
`ϑ(T) = (T/2) log |z| - (arg z)/4 - T/2 - (T/2) log π + Im R(z)`
(`TauCeti.riemannSiegelTheta_eq_add_im_stirlingRemainder`). For `T > 0`, the three error terms
against `(T/2) log (T/(2πe)) - π/8` are at most `1/(16T)` (the modulus, from
`Complex.abs_log_norm_sub_log_abs_im_le`), and `1/(8T)` (the argument, from
`Complex.pi_div_two_sub_arg_le_div`)
and `1/(2T)` (the remainder, from Stieltjes' bound
`TauCeti.norm_stirlingRemainder_lt_of_re_nonneg`).

## Main results

* `TauCeti.riemannSiegelTheta_eq_add_im_stirlingRemainder`: the exact Stirling form of `ϑ`.
* `TauCeti.abs_riemannSiegelTheta_sub_le`: the explicit asymptotic
  `|ϑ(T) - ((T/2) log (T/(2πe)) - π/8)| ≤ 1/T` for `T > 0`, and its `O(1/T)` form
  `TauCeti.isBigO_riemannSiegelTheta_sub`.
* `TauCeti.abs_riemannSiegelTheta_sub_sub_lt`: the first correction `1 / (48 * T)` with an explicit
  cubic error, using `TauCeti.norm_stirlingSeriesRemainder_lt_of_abs_arg_le`.
* `TauCeti.riemannSiegelTheta_div_pi_add_one_sub_bounds`: the strict `7 / 8` bracket for the smooth
  main term of the zero count at `T ≥ exp 1`.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (revised by
  D. R. Heath-Brown), §9.3.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4, eq. (8.4.06).
* R. P. Brent, *On asymptotic approximations to the log-Gamma and Riemann–Siegel theta functions*,
  J. Aust. Math. Soc. 107 (2019), 319–337, §4, for the theta expansion and its first correction.
* T. J. Stieltjes, *Sur le développement de `log Γ(a)`*, J. Math. Pures Appl. (4) 5 (1889),
  425–444, for the `1 / (6 * ‖z‖)` right half-plane bound on the Stirling remainder.
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
  simp only [one_div, sub_re, add_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self',
    mul_re, div_ofNat_re, ofReal_re, I_re, mul_zero, div_ofNat_im, ofReal_im, zero_div, I_im,
    mul_one, sub_self, add_zero, inv_im, im_ofNat, neg_zero, zero_add, sub_zero]
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

/-- The remainder term: `|Im R(1/4 + iT/2)| ≤ 1/(2T)` for `T > 0`, from Stieltjes' bound
`|R(z)| < 1/(6|z|)` on the nonzero points of the closed right half-plane and `|z| ≥ T/2`. -/
private theorem abs_im_stirlingRemainder_quarter_add_le {T : ℝ} (hT : 0 < T) :
    |(stirlingRemainder (1 / 4 + (T : ℂ) / 2 * I)).im| ≤ 1 / (2 * T) := by
  set z : ℂ := 1 / 4 + (T : ℂ) / 2 * I
  have hre : 0 < z.re := by simp [z]
  have him : z.im = T / 2 := by simp [z]
  have hnorm : T / 2 ≤ ‖z‖ := him ▸ im_le_norm z
  have hz0 : z ≠ 0 := Complex.ne_zero_of_re_pos hre
  calc |(stirlingRemainder z).im| ≤ ‖stirlingRemainder z‖ := abs_im_le_norm _
    _ ≤ 1 / (6 * ‖z‖) := (norm_stirlingRemainder_lt_of_re_nonneg hre.le hz0).le
    _ ≤ 1 / (4 * ‖z‖) := by gcongr; norm_num
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

/-- The imaginary part of the order-two remainder at `1 / 4 + iT / 2` is bounded by
`4 / (45 * T ^ 3)` for positive `T`. -/
private theorem abs_im_stirlingSeriesRemainder_two_quarter_add_lt {T : ℝ} (hT : 0 < T) :
    |(stirlingSeriesRemainder 2 (1 / 4 + (T : ℂ) / 2 * I)).im| < 4 / (45 * T ^ 3) := by
  set z : ℂ := 1 / 4 + (T : ℂ) / 2 * I with hzdef
  have hre : 0 < z.re := by simp [hzdef]
  have him : z.im = T / 2 := by simp [hzdef]
  have hnorm : T / 2 ≤ ‖z‖ := him ▸ im_le_norm z
  have hangle : π / 2 / 2 = π / 4 := by ring
  have hsin : Real.sin (π / 2 / 2) ^ (2 * 2) = 1 / 4 := by
    rw [hangle, Real.sin_pi_div_four]
    rw [pow_mul, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hsec := norm_stirlingSeriesRemainder_lt_of_abs_arg_le
    (n := 2) (by lia) (δ := π / 2) (by positivity)
    (by rw [sub_half]; exact abs_arg_le_pi_div_two_iff.mpr hre.le) (ne_zero_of_re_pos hre)
  -- Convert the sector estimate to the explicit norm of the second Stirling term.
  simp only [hsin, stirlingTerm_two, norm_neg, norm_div, norm_one, norm_mul, norm_pow,
    Complex.norm_ofNat] at hsec
  calc
    |(stirlingSeriesRemainder 2 z).im| ≤ ‖stirlingSeriesRemainder 2 z‖ := abs_im_le_norm _
    _ < 1 / (360 * ‖z‖ ^ 3) / (1 / 4) := hsec
    _ ≤ 1 / (360 * (T / 2) ^ 3) / (1 / 4) := by gcongr
    _ = 4 / (45 * T ^ 3) := by ring

/-- The exact theta correction in terms of the reciprocal height `1 / (2 * T)` for
positive `T`, separating the logarithm, arctangent, first Stirling term and remainder. -/
private theorem riemannSiegelTheta_sub_main_eq {T : ℝ} (hT : 0 < T) :
    riemannSiegelTheta T - (T / 2 * Real.log (T / (2 * π * Real.exp 1)) - π / 8) =
      T / 4 * Real.log (1 + (1 / (2 * T)) ^ 2) + Real.arctan (1 / (2 * T)) / 4 -
        (1 / (2 * T)) / (3 * (1 + (1 / (2 * T)) ^ 2)) +
        (stirlingSeriesRemainder 2 (1 / 4 + (T : ℂ) / 2 * I)).im := by
  set x : ℝ := 1 / (2 * T) with hxdef
  set z : ℂ := 1 / 4 + (T : ℂ) / 2 * I with hzdef
  have hre : z.re = 1 / 4 := by simp [hzdef]
  have him : z.im = T / 2 := by simp [hzdef]
  have himpos : 0 < z.im := him ▸ half_pos hT
  have hnorm : ‖z‖ ^ 2 = (T / 2) ^ 2 * (1 + x ^ 2) := by
    rw [← normSq_eq_norm_sq, normSq_apply, hre, him, hxdef]
    field
  have hlog : Real.log ‖z‖ = Real.log (T / 2) + Real.log (1 + x ^ 2) / 2 := by
    have h := congrArg Real.log hnorm
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h
    norm_cast at h
    linarith
  have harg : z.arg = π / 2 - Real.arctan x := by
    have hratio : 1 / 4 / (T / 2) = x := by rw [hxdef]; ring
    rw [arg_eq_pi_div_two_sub_arctan_of_im_pos himpos, hre, him, hratio]
  have hterm : (stirlingTerm 1 z).im = -(x / (3 * (1 + x ^ 2))) := by
    rw [stirlingTerm_one, one_div, inv_im]
    simp only [mul_im, normSq_eq_norm_sq, norm_mul, Complex.norm_ofNat, mul_pow, re_ofNat, im_ofNat,
      zero_mul, add_zero]
    rw [hnorm, him, hxdef]
    field
  have hrem : stirlingRemainder z = stirlingTerm 1 z + stirlingSeriesRemainder 2 z := by
    rw [stirlingSeriesRemainder_succ 1, stirlingSeriesRemainder_one]
    ring
  have hmain : T / 2 * Real.log (T / (2 * π * Real.exp 1)) =
      T / 2 * Real.log (T / 2) - T / 2 - T / 2 * Real.log π := by
    have hTwoPi : (2 : ℝ) * π ≠ 0 := by positivity
    rw [Real.log_div hT.ne' (by positivity), Real.log_mul hTwoPi (by positivity), Real.log_exp,
      Real.log_mul (by norm_num) Real.pi_ne_zero, Real.log_div hT.ne' (by norm_num)]
    ring
  rw [riemannSiegelTheta_eq_add_im_stirlingRemainder, ← hzdef]
  -- Insert the modulus, argument and remainder corrections into the Stirling identity.
  rw [hlog, harg, hrem, add_im, hterm, hmain]
  ring

/-- For positive `T`, subtracting Brent's first correction `1 / (48 * T)` from the
Riemann–Siegel theta asymptotic leaves an error of magnitude less than `9 / (64 * T ^ 3)`. -/
theorem abs_riemannSiegelTheta_sub_sub_lt {T : ℝ} (hT : 0 < T) :
    |riemannSiegelTheta T - (T / 2 * Real.log (T / (2 * π * Real.exp 1)) - π / 8) -
      1 / (48 * T)| < 9 / (64 * T ^ 3) := by
  set x : ℝ := 1 / (2 * T) with hxdef
  set z : ℂ := 1 / 4 + (T : ℂ) / 2 * I with hzdef
  have hx : 0 < x := by positivity
  have hform : riemannSiegelTheta T - (T / 2 * Real.log (T / (2 * π * Real.exp 1)) - π / 8) =
      Real.log (1 + x ^ 2) / (8 * x) + Real.arctan x / 4 - x / (3 * (1 + x ^ 2)) +
        (stirlingSeriesRemainder 2 z).im := by
    have hcoef : T / 4 = 1 / (8 * x) := by grind
    rw [riemannSiegelTheta_sub_main_eq hT, ← hxdef, ← hzdef, hcoef]
    ring
  -- The elementary corrections each have a one-sided cubic error.
  have hlog : x / 8 - x ^ 3 / 8 ≤ Real.log (1 + x ^ 2) / (8 * x) ∧
      Real.log (1 + x ^ 2) / (8 * x) ≤ x / 8 := by
    have hy : 0 < 1 + x ^ 2 := by positivity
    have hlo := Real.one_sub_inv_le_log_of_pos hy
    have hhi := Real.log_le_sub_one_of_pos hy
    constructor
    · rw [le_div_iff₀ (by positivity)]
      refine le_trans ?_ hlo
      rw [le_sub_comm, inv_eq_one_div, div_le_iff₀ hy]
      have hpow : 0 ≤ x ^ 6 := by positivity
      nlinarith [hpow]
    · rw [div_le_iff₀ (by positivity)]
      linarith
  have harg : x / 4 - x ^ 3 / 4 ≤ Real.arctan x / 4 ∧ Real.arctan x / 4 ≤ x / 4 := by
    have h := (abs_le.mp (Real.abs_arctan_sub_self_le x)).1
    rw [abs_of_pos hx] at h
    constructor <;> linarith [Real.arctan_le_self hx.le]
  have hterm : 0 ≤ x / 3 - x / (3 * (1 + x ^ 2)) ∧
      x / 3 - x / (3 * (1 + x ^ 2)) ≤ x ^ 3 / 3 := by
    have heq : x / 3 - x / (3 * (1 + x ^ 2)) = x ^ 3 / (3 * (1 + x ^ 2)) := by
      field
    rw [heq]
    exact ⟨by positivity, by gcongr; nlinarith [sq_nonneg x]⟩
  have hrem : |(stirlingSeriesRemainder 2 z).im| < 32 / 45 * x ^ 3 := by
    refine (abs_im_stirlingSeriesRemainder_two_quarter_add_lt hT).trans_eq ?_
    rw [hxdef]
    ring
  have hlin : 1 / (48 * T) = x / 24 := by
    rw [hxdef]
    ring
  have hcub : 9 / (64 * T ^ 3) = 9 / 8 * x ^ 3 := by grind
  grind

/-- The Riemann–Siegel theta function gives the smooth main term in the Riemann–von Mangoldt
formula with a correction strictly between `7 / 8` and `7 / 8 + 1 / (40 * T)` for `T ≥ exp 1`. -/
theorem riemannSiegelTheta_div_pi_add_one_sub_bounds {T : ℝ} (hT : Real.exp 1 ≤ T) :
    7 / 8 < riemannSiegelTheta T / π + 1 - T / (2 * π) * Real.log (T / (2 * π * Real.exp 1)) ∧
    riemannSiegelTheta T / π + 1 - T / (2 * π) * Real.log (T / (2 * π * Real.exp 1)) <
      7 / 8 + 1 / (40 * T) := by
  have hlarge : (27 / 10 : ℝ) < T := ((by norm_num : (27 / 10 : ℝ) < 2.7182818283).trans
    Real.exp_one_gt_d9).trans_le hT
  have hpos : 0 < T := by linarith
  have hsq : (27 / 4 : ℝ) < T ^ 2 := by nlinarith [sq_nonneg (T - 27 / 10)]
  have hcub : 9 / (64 * T ^ 3) < 1 / (48 * T) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hpos (sub_pos.mpr hsq)]
  have hlin : 2 * (1 / (48 * T)) < 1 / (40 * T) * π := calc
    _ = (5 / 3) / (40 * T) := by ring
    _ < π / (40 * T) := by gcongr; linarith [Real.pi_gt_three]
    _ = _ := by ring
  obtain ⟨hlo, hhi⟩ := abs_lt.mp (abs_riemannSiegelTheta_sub_sub_lt hpos)
  have heq : riemannSiegelTheta T / π + 1 - T / (2 * π) * Real.log (T / (2 * π * Real.exp 1)) =
      7 / 8 + (riemannSiegelTheta T -
        (T / 2 * Real.log (T / (2 * π * Real.exp 1)) - π / 8)) / π := by grind
  rw [heq]
  constructor
  · exact lt_add_of_pos_right _ (div_pos (by linarith) Real.pi_pos)
  · rw [add_lt_add_iff_left, div_lt_iff₀ Real.pi_pos]
    linarith

end TauCeti
