/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.Complex.Basic

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
factors (`Complex.norm_Gammaℝ`, `Complex.norm_Gammaℂ`). They are the single-factor estimates
whose sum over the shifts of an L-function's gamma factor gives the growth of that gamma factor on
vertical strips.

## Main declarations

* `TauCeti.exists_abs_log_norm_Gammaℝ_add_vertical_sub_le`: the estimate for `Γ_ℝ(s + μ)`.
* `TauCeti.exists_abs_log_norm_Gammaℂ_add_vertical_sub_le`: the estimate for `Γ_ℂ(s + μ)`.

## References

* [DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9).
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004,
  §5.1.
-/

public section

open Real Set

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
    refine Gamma_ne_zero_of_im_ne_zero ?_
    rw [div_ofNat_im]
    exact div_ne_zero (add_im_ne_zero_of_abs_im_lt (by linarith)) two_ne_zero
  have hlog : Real.log ‖Gammaℝ (s + μ)‖ =
      -((s.re + μ.re) / 2) * Real.log π + Real.log ‖Complex.Gamma ((s + μ) / 2)‖ := by
    rw [norm_Gammaℝ, Real.log_mul (by positivity) (norm_ne_zero_iff.2 hΓ),
      Real.log_rpow pi_pos, add_re, neg_div]
  have hσμ : |s.re + μ.re| ≤ M + |μ.re| :=
    (abs_add_le _ _).trans (by gcongr; exact abs_le_max_abs_abs hs.1 hs.2)
  have hπ : |(s.re + μ.re) / 2 * Real.log π| ≤ (M + |μ.re|) / 2 * |Real.log π| := by
    rw [abs_mul, abs_div, abs_two]
    gcongr
  have h2 : |(s.re + μ.re - 1) / 2 * Real.log 2| ≤ (M + |μ.re| + 1) / 2 * Real.log 2 := by
    rw [abs_mul, abs_div, abs_two, abs_of_pos (Real.log_pos one_lt_two)]
    gcongr
    exact abs_le.2 ⟨by linarith [abs_le.1 hσμ], by linarith [abs_le.1 hσμ]⟩
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
  have hΓ : Complex.Gamma (s + μ) ≠ 0 :=
    Gamma_ne_zero_of_im_ne_zero (add_im_ne_zero_of_abs_im_lt (by linarith))
  have hlog : Real.log ‖Gammaℂ (s + μ)‖ =
      Real.log 2 - (s.re + μ.re) * Real.log (2 * π) + Real.log ‖Complex.Gamma (s + μ)‖ := by
    rw [norm_Gammaℂ, Real.log_mul (by positivity) (norm_ne_zero_iff.2 hΓ),
      Real.log_mul two_ne_zero (by positivity), Real.log_rpow (by positivity), add_re]
    ring
  have hσμ : |s.re + μ.re| ≤ M + |μ.re| :=
    (abs_add_le _ _).trans (by gcongr; exact abs_le_max_abs_abs hs.1 hs.2)
  have hpos : 0 < Real.log (2 * π) := Real.log_pos (by linarith [two_le_pi])
  have h2π : |(s.re + μ.re) * Real.log (2 * π)| ≤ (M + |μ.re|) * Real.log (2 * π) := by
    rw [abs_mul, abs_of_pos hpos]
    gcongr
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
