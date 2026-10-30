/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# The cotangent over `ℤ` and away from the real axis

Mathlib's partial-fraction expansion of the cotangent (`cot_series_rep`) pairs the poles at `± n`.
Pairing each pole `n` instead with the constant `1 / n` gives an absolutely convergent series over
`ℤ` (`TauCeti.hasSum_one_div_sub_intCast_add_one_div_intCast`):

`π cot (π w) = ∑_{n ∈ ℤ} (1 / (w - n) + 1 / n)` for `w ∉ ℤ`,

the term at `n = 0` being `1 / w`. This is the form in which the cotangent appears as a row of the
lattice series of the Weierstrass `ζ` function.

Away from the real axis, `π cot (π u)` tends to `-π i` as `Im u → ∞`, and to `π i` as
`Im u → -∞`, exponentially fast: with `q = e^(2π i u)`, `π cot (π u) + π i = 2π q / (i (1 - q))`
(`TauCeti.norm_pi_mul_cot_pi_mul_add_pi_mul_I_le`,
`TauCeti.norm_pi_mul_cot_pi_mul_sub_pi_mul_I_le`).

## Main results

* `Complex.cot_neg`, `Complex.cot_zero`: the cotangent is odd, with junk value `0` at `0`.
* `TauCeti.hasSum_one_div_sub_intCast_add_one_div_intCast`: the expansion over `ℤ`.
* `TauCeti.norm_pi_mul_cot_pi_mul_add_pi_mul_I_le`,
  `TauCeti.norm_pi_mul_cot_pi_mul_sub_pi_mul_I_le`: the exponential approach to `∓ π i`.
-/

public section

open Complex
open scoped Real

namespace Complex

/-- The cotangent is odd. -/
@[simp]
theorem cot_neg (z : ℂ) : cot (-z) = -cot z := by
  simp [cot_eq_cos_div_sin, div_neg]

/-- The junk value of the cotangent at its pole `0` is `0`. -/
@[simp]
theorem cot_zero : cot 0 = 0 := by
  simp [cot_eq_cos_div_sin]

end Complex

namespace TauCeti

/-- **The partial-fraction expansion of the cotangent over `ℤ`.** For `w ∉ ℤ`,
`π cot (π w) = ∑_{n ∈ ℤ} (1 / (w - n) + 1 / n)`, the series converging absolutely; its term at
`n = 0` is `1 / w`. -/
theorem hasSum_one_div_sub_intCast_add_one_div_intCast {w : ℂ} (hw : w ∈ integerComplement) :
    HasSum (fun n : ℤ ↦ 1 / (w - n) + 1 / n) (π * cot (π * w)) := by
  set f : ℤ → ℂ := fun n ↦ 1 / (w - n) + 1 / n
  have hsub (n : ℤ) : w - n ≠ 0 := by
    simpa [sub_eq_add_neg] using integerComplement_add_ne_zero hw (-n)
  have hf : Summable f := by
    have hg := (EisensteinSeries.summable_linear_sub_mul_linear_add w 1 0).mul_left w
    have h0 : Summable fun n : ℤ ↦ if n = 0 then 1 / w else 0 :=
      summable_of_ne_finset_zero (s := {0}) fun n hn ↦ by simp_all
    refine (hg.add h0).congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [f]
    · have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
      simp only [Int.cast_one, one_mul, Int.cast_zero, zero_mul, zero_add, hn, ↓reduceIte,
        add_zero, f]
      field_simp [hsub n, hn']
      ring
  have h₁ : Summable fun n : ℕ+ ↦ f n :=
    hf.comp_injective (Nat.cast_injective.comp PNat.coe_injective)
  have h₂ : Summable fun n : ℕ+ ↦ f (-n) :=
    hf.comp_injective (neg_injective.comp (Nat.cast_injective.comp PNat.coe_injective))
  convert hf.hasSum using 1
  rw [tsum_int_eq_zero_add_tsum_pnat hf, add_assoc, ← h₁.tsum_add h₂, cot_series_rep hw]
  congr 1
  · simp [f]
  · refine tsum_congr fun n ↦ ?_
    simp only [f, Int.cast_neg, Int.cast_natCast, sub_neg_eq_add]
    ring

/-- **The cotangent tends to `-i` in the upper half-plane**: if `0 < t ≤ Im u`, then
`‖π cot (π u) + π i‖ ≤ 2π e^(-2π Im u) / (1 - e^(-2π t))`. -/
theorem norm_pi_mul_cot_pi_mul_add_pi_mul_I_le {u : ℂ} {t : ℝ} (ht : 0 < t) (hu : t ≤ u.im) :
    ‖π * cot (π * u) + π * I‖ ≤
      2 * π / (1 - Real.exp (-2 * π * t)) * Real.exp (-2 * π * u.im) := by
  set q := cexp (2 * π * I * u) with hqdef
  have hq : ‖q‖ = Real.exp (-2 * π * u.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hθ : Real.exp (-2 * π * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hle : ‖q‖ ≤ Real.exp (-2 * π * t) := by
    rw [hq, Real.exp_le_exp]
    nlinarith [Real.pi_pos]
  have h1q : 1 - Real.exp (-2 * π * t) ≤ ‖1 - q‖ :=
    (by linarith : 1 - Real.exp (-2 * π * t) ≤ 1 - ‖q‖).trans
      (by simpa using norm_sub_norm_le (1 : ℂ) q)
  have hpos : 0 < 1 - Real.exp (-2 * π * t) := by linarith
  have hq1 : 1 - q ≠ 0 := norm_pos_iff.mp (hpos.trans_le h1q)
  have heq : π * cot (π * u) + π * I = 2 * π * q / (I * (1 - q)) := by
    rw [cot_pi_eq_exp_ratio, ← hqdef]
    field_simp
    linear_combination (1 - q) * I_sq
  have h2π : ‖(2 * π : ℂ)‖ = 2 * π := by
    simp [abs_of_pos Real.pi_pos]
  rw [heq, norm_div, norm_mul I, norm_I, one_mul, norm_mul, h2π, hq]
  calc 2 * π * Real.exp (-2 * π * u.im) / ‖1 - q‖
      ≤ 2 * π * Real.exp (-2 * π * u.im) / (1 - Real.exp (-2 * π * t)) := by
        gcongr
    _ = _ := by ring

/-- **The cotangent tends to `i` in the lower half-plane**: if `0 < t ≤ -Im u`, then
`‖π cot (π u) - π i‖ ≤ 2π e^(2π Im u) / (1 - e^(-2π t))`. -/
theorem norm_pi_mul_cot_pi_mul_sub_pi_mul_I_le {u : ℂ} {t : ℝ} (ht : 0 < t) (hu : t ≤ -u.im) :
    ‖π * cot (π * u) - π * I‖ ≤
      2 * π / (1 - Real.exp (-2 * π * t)) * Real.exp (2 * π * u.im) := by
  have h := norm_pi_mul_cot_pi_mul_add_pi_mul_I_le ht (u := -u) (by simpa using hu)
  rw [mul_neg, cot_neg, Complex.neg_im, mul_neg, neg_add_eq_sub, norm_sub_rev] at h
  convert h using 3
  ring

end TauCeti
