/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical

/-!
# Stirling's formula for the archimedean gamma factors on vertical strips

The archimedean gamma factors `Γ_ℝ(s) = π^(-s/2) Γ(s/2)` and `Γ_ℂ(s) = 2 (2π)^(-s) Γ(s)` decay
exponentially along vertical lines. For every compact interval `[a, b]` and every shift `μ`,
uniformly for `σ ∈ [a, b]` as `|t| → ∞`,
```
log ‖Γ_ℝ(σ + i t + μ)‖ = ((σ + Re μ - 1) / 2) log |t| - π |t| / 4 + O(1),
log ‖Γ_ℂ(σ + i t + μ)‖ = (σ + Re μ - 1/2) log |t| - π |t| / 2 + O(1).
```
Both follow from Stirling's formula for `Γ` on vertical strips
(`TauCeti.exists_abs_log_norm_Gamma_add_vertical_sub_le`) and the moduli of the exponential
factors. They are the single-factor estimates whose sum over the shifts of an L-function's gamma
factor gives the growth of that gamma factor on vertical strips.

## Main declarations

* `Complex.norm_Gammaℝ`, `Complex.norm_Gammaℂ`: the moduli of the two factors in terms of `‖Γ‖`.
* `TauCeti.exists_abs_log_norm_Gammaℝ_add_vertical_sub_le`: the estimate for `Γ_ℝ(s + μ)`.
* `TauCeti.exists_abs_log_norm_Gammaℂ_add_vertical_sub_le`: the estimate for `Γ_ℂ(s + μ)`.

## References

* [DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9).
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  §5.1.
-/

public section

open Real Set

namespace Complex

/-- The modulus of the real archimedean gamma factor: `‖Γ_ℝ(s)‖ = π^(-Re s / 2) ‖Γ(s / 2)‖`. -/
theorem norm_Gammaℝ (s : ℂ) : ‖Gammaℝ s‖ = π ^ (-s.re / 2) * ‖Gamma (s / 2)‖ := by
  rw [Gammaℝ_def, norm_mul, norm_cpow_eq_rpow_re_of_pos pi_pos]
  simp [neg_div]

/-- The modulus of the complex archimedean gamma factor: `‖Γ_ℂ(s)‖ = 2 (2π)^(-Re s) ‖Γ(s)‖`. -/
theorem norm_Gammaℂ (s : ℂ) : ‖Gammaℂ s‖ = 2 * (2 * π) ^ (-s.re) * ‖Gamma s‖ := by
  have h2π : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [Gammaℂ_def, norm_mul, norm_mul, h2π, norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

end Complex

namespace TauCeti

open Complex

/-- **Stirling's formula for `Γ_ℝ` on vertical strips.** For every compact interval `[a, b]` and
every shift `μ` there are `C` and `X` such that
`|log ‖Γ_ℝ(s + μ)‖ - (((σ + Re μ - 1) / 2) log |t| - π |t| / 4)| ≤ C` for `s = σ + i t` with
`σ ∈ [a, b]` and `X ≤ |t|`. -/
theorem exists_abs_log_norm_Gammaℝ_add_vertical_sub_le (a b : ℝ) (μ : ℂ) :
    ∃ C X : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → X ≤ |s.im| →
      |Real.log ‖Gammaℝ (s + μ)‖ -
          ((s.re + μ.re - 1) / 2 * Real.log |s.im| - π * |s.im| / 4)| ≤ C := by
  obtain ⟨C, X, h⟩ := exists_abs_log_norm_Gamma_add_vertical_sub_le (a / 2) (b / 2) (μ / 2)
  set M := max |a| |b|
  refine ⟨|C| + (M + |μ.re|) / 2 * |Real.log π| + (M + |μ.re| + 1) / 2 * Real.log 2,
    max (2 * X) (|μ.im| + 1), fun s hs ht ↦ ?_⟩
  have hX := (le_max_left _ _).trans ht
  have hτ : |μ.im| + 1 ≤ |s.im| := (le_max_right _ _).trans ht
  have hτ0 : 0 < |s.im| := by linarith [abs_nonneg μ.im]
  -- Stirling for `Γ` at `s / 2 + μ / 2 = (s + μ) / 2`.
  have hE := h (s / 2) (by simpa using ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    (by rw [div_ofNat_im, abs_div, abs_two]; linarith)
  rw [← add_div, div_ofNat_im, abs_div, abs_two, Real.log_div hτ0.ne' two_ne_zero] at hE
  simp only [div_ofNat_re] at hE
  -- The modulus of `Γ_ℝ(s + μ)` splits off the exponential factor.
  have hΓ : Complex.Gamma ((s + μ) / 2) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm ↦ ?_
    have him := congr_arg im hm
    rw [div_ofNat_im, add_im, neg_im, natCast_im, neg_zero, div_eq_zero_iff] at him
    have : |s.im| = |μ.im| := by
      rw [eq_neg_of_add_eq_zero_left (him.resolve_right two_ne_zero), abs_neg]
    linarith
  have hlog : Real.log ‖Gammaℝ (s + μ)‖ =
      -((s.re + μ.re) / 2) * Real.log π + Real.log ‖Complex.Gamma ((s + μ) / 2)‖ := by
    rw [norm_Gammaℝ, Real.log_mul (by positivity) (norm_ne_zero_iff.2 hΓ),
      Real.log_rpow pi_pos, add_re, neg_div]
  have hσ := abs_le.1 (abs_le_max_abs_abs hs.1 hs.2)
  have hr := abs_le.1 (le_refl |μ.re|)
  have hπ : |(s.re + μ.re) / 2 * Real.log π| ≤ (M + |μ.re|) / 2 * |Real.log π| := by
    rw [abs_mul]
    gcongr
    rw [abs_div, abs_two]
    gcongr
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |(s.re + μ.re - 1) / 2 * Real.log 2| ≤ (M + |μ.re| + 1) / 2 * Real.log 2 := by
    rw [abs_mul, abs_of_pos (Real.log_pos one_lt_two)]
    gcongr
    rw [abs_div, abs_two]
    gcongr
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have key : Real.log ‖Gammaℝ (s + μ)‖ -
        ((s.re + μ.re - 1) / 2 * Real.log |s.im| - π * |s.im| / 4) =
      (Real.log ‖Complex.Gamma ((s + μ) / 2)‖ -
          ((s.re / 2 + μ.re / 2 - 1 / 2) * (Real.log |s.im| - Real.log 2) -
            π * (|s.im| / 2) / 2)) -
        (s.re + μ.re) / 2 * Real.log π - (s.re + μ.re - 1) / 2 * Real.log 2 := by
    rw [hlog]; ring
  rw [key]
  have e1 := abs_le.1 (hE.trans (le_abs_self C))
  have e2 := abs_le.1 hπ
  have e3 := abs_le.1 h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **Stirling's formula for `Γ_ℂ` on vertical strips.** For every compact interval `[a, b]` and
every shift `μ` there are `C` and `X` such that
`|log ‖Γ_ℂ(s + μ)‖ - ((σ + Re μ - 1/2) log |t| - π |t| / 2)| ≤ C` for `s = σ + i t` with
`σ ∈ [a, b]` and `X ≤ |t|`. -/
theorem exists_abs_log_norm_Gammaℂ_add_vertical_sub_le (a b : ℝ) (μ : ℂ) :
    ∃ C X : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → X ≤ |s.im| →
      |Real.log ‖Gammaℂ (s + μ)‖ -
          ((s.re + μ.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2)| ≤ C := by
  obtain ⟨C, X, h⟩ := exists_abs_log_norm_Gamma_add_vertical_sub_le a b μ
  set M := max |a| |b|
  refine ⟨|C| + Real.log 2 + (M + |μ.re|) * Real.log (2 * π), max X (|μ.im| + 1),
    fun s hs ht ↦ ?_⟩
  have hE := h s hs ((le_max_left _ _).trans ht)
  have hτ : |μ.im| + 1 ≤ |s.im| := (le_max_right _ _).trans ht
  have hΓ : Complex.Gamma (s + μ) ≠ 0 := by
    refine Complex.Gamma_ne_zero fun m hm ↦ ?_
    have him := congr_arg im hm
    rw [add_im, neg_im, natCast_im, neg_zero] at him
    have : |s.im| = |μ.im| := by rw [eq_neg_of_add_eq_zero_left him, abs_neg]
    linarith
  have hlog : Real.log ‖Gammaℂ (s + μ)‖ =
      Real.log 2 - (s.re + μ.re) * Real.log (2 * π) + Real.log ‖Complex.Gamma (s + μ)‖ := by
    rw [norm_Gammaℂ, Real.log_mul (by positivity) (norm_ne_zero_iff.2 hΓ),
      Real.log_mul two_ne_zero (by positivity), Real.log_rpow (by positivity), add_re]
    ring
  have hσ := abs_le.1 (abs_le_max_abs_abs hs.1 hs.2)
  have hr := abs_le.1 (le_refl |μ.re|)
  have hpos : 0 < Real.log (2 * π) := Real.log_pos (by linarith [two_le_pi])
  have h2π : |(s.re + μ.re) * Real.log (2 * π)| ≤ (M + |μ.re|) * Real.log (2 * π) := by
    rw [abs_mul, abs_of_pos hpos]
    gcongr
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have key : Real.log ‖Gammaℂ (s + μ)‖ -
        ((s.re + μ.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2) =
      (Real.log ‖Complex.Gamma (s + μ)‖ -
          ((s.re + μ.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2)) +
        Real.log 2 - (s.re + μ.re) * Real.log (2 * π) := by
    rw [hlog]; ring
  rw [key]
  have e1 := abs_le.1 (hE.trans (le_abs_self C))
  have e2 := abs_le.1 h2π
  have e3 : 0 < Real.log 2 := Real.log_pos one_lt_two
  exact abs_le.2 ⟨by linarith, by linarith⟩

end TauCeti
