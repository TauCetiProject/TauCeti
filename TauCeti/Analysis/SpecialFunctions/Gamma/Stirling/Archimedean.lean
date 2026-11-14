/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import TauCeti.Analysis.SpecialFunctions.Log.MulLog

/-!
# Vertical-strip Stirling asymptotics for Deligne's archimedean gamma factors

Combining the vertical-strip Stirling formula `TauCeti.abs_log_norm_Gamma_vertical_sub_le` for
`Complex.Gamma` (`TauCeti/Analysis/SpecialFunctions/Gamma/Stirling/Vertical.lean`) with the norm
identities for `Complex.Gammaℝ` and `Complex.Gammaℂ`
(`TauCeti/Analysis/SpecialFunctions/Gamma/Archimedean.lean`) gives sharp `O(1 / |t|)` asymptotics
uniformly on every compact strip `Re s ∈ [a, b]`:
$$\log \|\Gamma_{\mathbb{R}}(\sigma + i t)\| =
  -\frac{\pi}{4} |t| + \frac{\sigma - 1}{2} \log |t|
  + \frac{\log 2 - (\sigma - 1) \log (2\pi)}{2} + O(|t|^{-1}),$$
$$\log \|\Gamma_{\mathbb{C}}(\sigma + i t)\| =
  -\frac{\pi}{2} |t| + \left(\sigma - \frac{1}{2}\right) \log |t|
  + \log 2 - \left(\sigma - \frac{1}{2}\right) \log (2\pi) + O(|t|^{-1}).$$
The constant terms add across Legendre's duplication identity
`Γ_ℝ(s) Γ_ℝ(s + 1) = Γ_ℂ(s)` (`Complex.Gammaℝ_mul_Gammaℝ_add_one`).

For shifted factors `s ↦ Γ_ℝ(s + μ)` and `s ↦ Γ_ℂ(s + ν)` with complex parameters `μ, ν : ℂ`,
replacing `|t + Im μ|` by `|t|` in the linear exponential term shifts it by at most `π |Im μ| / 4`
for `Γ_ℝ(s + μ)` and `π |Im ν| / 2` for `Γ_ℂ(s + ν)`, while the `σ`-dependent constant is bounded
on `[a, b]`. This yields the additive `O(1)` vertical strip asymptotics
$$\log \|\Gamma_{\mathbb{R}}(\sigma + i t + \mu)\| =
  -\frac{\pi}{4} |t| + \frac{\sigma + \operatorname{Re}\mu - 1}{2} \log |t| + O(1),$$
$$\log \|\Gamma_{\mathbb{C}}(\sigma + i t + \nu)\| =
  -\frac{\pi}{2} |t| + \left(\sigma + \operatorname{Re}\nu - \frac{1}{2}\right) \log |t| + O(1),$$
with uniform error bounds and height thresholds depending only on `a`, `b`, and an upper bound `M`
on `‖μ‖` or `‖ν‖`. An example at the end of the file shows that `O(1)` cannot be strengthened to
`o(1)` once `Im μ ≠ 0`.

## Main declarations

* `TauCeti.abs_log_norm_Gammaℝ_vertical_sub_le`,
  `TauCeti.abs_log_norm_Gammaℂ_vertical_sub_le`: explicit `O(1 / |Im s|)` bounds for unshifted
  `Gammaℝ` and `Gammaℂ` on `|Re s| ≤ |Im s|`.
* `TauCeti.isBigO_log_norm_Gammaℝ_vertical_sub`,
  `TauCeti.isBigO_log_norm_Gammaℂ_vertical_sub` (and strip / line variants): uniform `O(1 / |t|)`
  asymptotics on vertical strips.
* `TauCeti.exists_abs_log_norm_Gammaℝ_add_vertical_sub_le`,
  `TauCeti.exists_abs_log_norm_Gammaℂ_add_vertical_sub_le`: uniform `O(1)` bounds on `[a, b]` for
  all shifts with `‖μ‖ ≤ M`.
* `TauCeti.isBigO_log_norm_Gammaℝ_add_vertical_sub`,
  `TauCeti.isBigO_log_norm_Gammaℂ_add_vertical_sub` (and strip / line variants): `O(1)` asymptotics
  for individual complex-shifted factors.

## References

* [NIST Digital Library of Mathematical Functions, 5.11.9](https://dlmf.nist.gov/5.11.E9) and
  [5.5.5](https://dlmf.nist.gov/5.5.E5).
* P. Deligne, *Valeurs de fonctions L et périodes d'intégrales*, Proc. Symp. Pure Math. 33 (1979),
  Part 2, §5.3.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
-/

public section

open Complex Real Filter Set Asymptotics
open scoped Topology

namespace TauCeti

/-! ### Unshifted `Gammaℝ` on vertical strips -/

/-- **Stirling's formula for `Gammaℝ` on vertical strips**, explicit form: for `s = σ + i t` with
`t ≠ 0` and `|σ| ≤ |t|`,
`|log ‖Γ_ℝ(s)‖ - (-π |t| / 4 + ((σ - 1) / 2) log |t| + (log 2 - (σ - 1) log (2π)) / 2)| ≤
  (4 / (1 - cos (π / 4)) ^ 3 + |σ - 1| |σ| / 2 + σ ^ 2 / 2) / |t|`. -/
theorem abs_log_norm_Gammaℝ_vertical_sub_le {s : ℂ} (hs : s.im ≠ 0) (hre : |s.re| ≤ |s.im|) :
    |Real.log ‖Complex.Gammaℝ s‖ -
        (-π * |s.im| / 4 + (s.re - 1) / 2 * Real.log |s.im| +
          (Real.log 2 - (s.re - 1) * Real.log (2 * π)) / 2)| ≤
      (4 / (1 - Real.cos (π / 4)) ^ 3 + |s.re - 1| * |s.re| / 2 + s.re ^ 2 / 2) / |s.im| := by
  have him2 : (s / 2).im ≠ 0 := by simpa using div_ne_zero hs two_ne_zero
  have hre2 : |(s / 2).re| ≤ |(s / 2).im| := by
    simp only [div_ofNat_re, div_ofNat_im, abs_div, Nat.abs_ofNat]
    exact div_le_div_of_nonneg_right hre zero_le_two
  have hS := abs_log_norm_Gamma_vertical_sub_le him2 hre2
  simp only [div_ofNat_re, div_ofNat_im, abs_div, Nat.abs_ofNat] at hS
  have hlog_div : Real.log (|s.im| / 2) = Real.log |s.im| - Real.log 2 :=
    Real.log_div (abs_ne_zero.2 hs) two_ne_zero
  have hlog2pi : Real.log (2 * π) = Real.log 2 + Real.log π :=
    Real.log_mul two_ne_zero Real.pi_ne_zero
  rw [log_norm_Gammaℝ (Gammaℝ_ne_zero_of_im_ne_zero hs)]
  have hdiff : -(s.re / 2) * Real.log π + Real.log ‖Complex.Gamma (s / 2)‖ -
      (-π * |s.im| / 4 + (s.re - 1) / 2 * Real.log |s.im| +
        (Real.log 2 - (s.re - 1) * Real.log (2 * π)) / 2) =
      Real.log ‖Complex.Gamma (s / 2)‖ -
        ((s.re / 2 - 1 / 2) * Real.log (|s.im| / 2) - π * (|s.im| / 2) / 2 +
          Real.log (2 * π) / 2) := by
    rw [hlog_div, hlog2pi]
    ring
  have hsub_abs : |s.re / 2 - 1 / 2| = |s.re - 1| / 2 := by
    rw [← sub_div, abs_div, abs_two]
  have hrhs : (2 / (1 - Real.cos (π / 4)) ^ 3 + |s.re / 2 - 1 / 2| * (|s.re| / 2) +
        (s.re / 2) ^ 2) / (|s.im| / 2) =
      (4 / (1 - Real.cos (π / 4)) ^ 3 + |s.re - 1| * |s.re| / 2 + s.re ^ 2 / 2) / |s.im| := by
    rw [hsub_abs]
    field_simp
    ring
  rw [hdiff, ← hrhs]
  exact hS

private theorem abs_log_norm_Gammaℝ_vertical_sub_le_of_re_le {w : ℂ} {R : ℝ}
    (hwre : |w.re| ≤ R) (hwim : R + 1 ≤ |w.im|) :
    |Real.log ‖Complex.Gammaℝ w‖ -
        (-π * |w.im| / 4 + (w.re - 1) / 2 * Real.log |w.im| +
          (Real.log 2 - (w.re - 1) * Real.log (2 * π)) / 2)| ≤
      (4 / (1 - Real.cos (π / 4)) ^ 3 + (R + 1) * R / 2 + R ^ 2 / 2) / |w.im| := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hwre
  have hwim_pos : 0 < |w.im| := by linarith
  have hwre1 : |w.re - 1| ≤ R + 1 := abs_le.2
    ⟨by linarith [(abs_le.1 hwre).1], by linarith [(abs_le.1 hwre).2]⟩
  refine (abs_log_norm_Gammaℝ_vertical_sub_le (abs_pos.1 hwim_pos) (by linarith)).trans
    (div_le_div_of_nonneg_right ?_ hwim_pos.le)
  have h2 : |w.re - 1| * |w.re| ≤ (R + 1) * R :=
    mul_le_mul hwre1 hwre (abs_nonneg _) (by positivity)
  have h3 : w.re ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hwre 2
  linarith

/-- Uniform `O(1 / |Im s|)` bound for the Stirling remainder of `log ‖Gammaℝ s‖` on a compact
vertical strip `[a, b]`. -/
theorem exists_abs_log_norm_Gammaℝ_vertical_sub_le (a b : ℝ) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Complex.Gammaℝ s‖ -
          (-π * |s.im| / 4 + (s.re - 1) / 2 * Real.log |s.im| +
            (Real.log 2 - (s.re - 1) * Real.log (2 * π)) / 2)| ≤
        C / |s.im| :=
  ⟨4 / (1 - Real.cos (π / 4)) ^ 3 + (max |a| |b| + 1) * max |a| |b| / 2 + max |a| |b| ^ 2 / 2,
    max |a| |b| + 1,
    fun _ hs ht ↦ abs_log_norm_Gammaℝ_vertical_sub_le_of_re_le (abs_le_max_abs_abs hs.1 hs.2) ht⟩

/-- **Stirling's formula for `Gammaℝ` on vertical strips**:
`log ‖Γ_ℝ(σ + i t)‖ = -π |t| / 4 + ((σ - 1) / 2) log |t| + (log 2 - (σ - 1) log (2π)) / 2 +
  O(1 / |t|)` uniformly for `σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gammaℝ_vertical_sub (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖Complex.Gammaℝ (p.1 + p.2 * I)‖ -
        (-π * |p.2| / 4 + (p.1 - 1) / 2 * Real.log |p.2| +
          (Real.log 2 - (p.1 - 1) * Real.log (2 * π)) / 2))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun p ↦ |p.2|⁻¹ := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gammaℝ_vertical_sub_le a b
  refine isBigO_inv_vertical_of_exists ⟨C, T, fun p hσ ht ↦ ?_⟩
  simpa using h (p.1 + p.2 * I) (by simpa using hσ) (by simpa using ht)

/-- **Stirling's formula for `Gammaℝ`** as a function of `s` on the strip `Re s ∈ [a, b]`. -/
theorem isBigO_log_norm_Gammaℝ_vertical_strip_sub (a b : ℝ) :
    (fun s : ℂ ↦ Real.log ‖Complex.Gammaℝ s‖ -
        (-π * |s.im| / 4 + (s.re - 1) / 2 * Real.log |s.im| +
          (Real.log 2 - (s.re - 1) * Real.log (2 * π)) / 2))
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun s ↦ |s.im|⁻¹ := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gammaℝ_vertical_sub_le a b
  exact isBigO_inv_vertical_strip_of_exists ⟨C, T, fun s hs ht ↦ by simpa using h s hs ht⟩

/-- Stirling's formula for `Gammaℝ` on a single vertical line `Re s = σ`. -/
theorem isBigO_log_norm_Gammaℝ_vertical_line_sub (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gammaℝ (σ + t * I)‖ -
        (-π * |t| / 4 + (σ - 1) / 2 * Real.log |t| +
          (Real.log 2 - (σ - 1) * Real.log (2 * π)) / 2))
      =O[cocompact ℝ] fun t ↦ |t|⁻¹ :=
  (isBigO_log_norm_Gammaℝ_vertical_sub σ σ).cocompact_of_vertical (left_mem_Icc.2 le_rfl)

/-! ### Unshifted `Gammaℂ` on vertical strips -/

/-- **Stirling's formula for `Gammaℂ` on vertical strips**, explicit form: for `s = σ + i t` with
`t ≠ 0` and `|σ| ≤ |t|`,
`|log ‖Γ_ℂ(s)‖ - (-π |t| / 2 + (σ - 1 / 2) log |t| + log 2 - (σ - 1 / 2) log (2π))| ≤
  (2 / (1 - cos (π / 4)) ^ 3 + |σ - 1 / 2| |σ| + σ ^ 2) / |t|`. -/
theorem abs_log_norm_Gammaℂ_vertical_sub_le {s : ℂ} (hs : s.im ≠ 0) (hre : |s.re| ≤ |s.im|) :
    |Real.log ‖Complex.Gammaℂ s‖ -
        (-π * |s.im| / 2 + (s.re - 1 / 2) * Real.log |s.im| +
          Real.log 2 - (s.re - 1 / 2) * Real.log (2 * π))| ≤
      (2 / (1 - Real.cos (π / 4)) ^ 3 + |s.re - 1 / 2| * |s.re| + s.re ^ 2) / |s.im| := by
  rw [log_norm_Gammaℂ (Gammaℂ_ne_zero_of_im_ne_zero hs)]
  have hdiff : Real.log 2 - s.re * Real.log (2 * π) + Real.log ‖Complex.Gamma s‖ -
      (-π * |s.im| / 2 + (s.re - 1 / 2) * Real.log |s.im| +
        Real.log 2 - (s.re - 1 / 2) * Real.log (2 * π)) =
      Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2) := by
    ring
  rw [hdiff]
  exact abs_log_norm_Gamma_vertical_sub_le hs hre

/-- Uniform `O(1 / |Im s|)` bound for the Stirling remainder of `log ‖Gammaℂ s‖` on a compact
vertical strip `[a, b]`. -/
theorem exists_abs_log_norm_Gammaℂ_vertical_sub_le (a b : ℝ) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Complex.Gammaℂ s‖ -
          (-π * |s.im| / 2 + (s.re - 1 / 2) * Real.log |s.im| +
            Real.log 2 - (s.re - 1 / 2) * Real.log (2 * π))| ≤
        C / |s.im| := by
  obtain ⟨C, T, hCT⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  refine ⟨C, max T 1, fun s hs ht ↦ ?_⟩
  have ht0 : 0 < |s.im| := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans ht)
  rw [log_norm_Gammaℂ (Gammaℂ_ne_zero_of_im_ne_zero (abs_pos.1 ht0))]
  have hdiff : Real.log 2 - s.re * Real.log (2 * π) + Real.log ‖Complex.Gamma s‖ -
      (-π * |s.im| / 2 + (s.re - 1 / 2) * Real.log |s.im| +
        Real.log 2 - (s.re - 1 / 2) * Real.log (2 * π)) =
      Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2) := by
    ring
  rw [hdiff]
  exact hCT s hs ((le_max_left _ _).trans ht)

/-- **Stirling's formula for `Gammaℂ` on vertical strips**:
`log ‖Γ_ℂ(σ + i t)‖ = -π |t| / 2 + (σ - 1 / 2) log |t| + log 2 - (σ - 1 / 2) log (2π) +
  O(1 / |t|)` uniformly for `σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gammaℂ_vertical_sub (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖Complex.Gammaℂ (p.1 + p.2 * I)‖ -
        (-π * |p.2| / 2 + (p.1 - 1 / 2) * Real.log |p.2| +
          Real.log 2 - (p.1 - 1 / 2) * Real.log (2 * π)))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun p ↦ |p.2|⁻¹ := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gammaℂ_vertical_sub_le a b
  refine isBigO_inv_vertical_of_exists ⟨C, T, fun p hσ ht ↦ ?_⟩
  simpa using h (p.1 + p.2 * I) (by simpa using hσ) (by simpa using ht)

/-- **Stirling's formula for `Gammaℂ`** as a function of `s` on the strip `Re s ∈ [a, b]`. -/
theorem isBigO_log_norm_Gammaℂ_vertical_strip_sub (a b : ℝ) :
    (fun s : ℂ ↦ Real.log ‖Complex.Gammaℂ s‖ -
        (-π * |s.im| / 2 + (s.re - 1 / 2) * Real.log |s.im| +
          Real.log 2 - (s.re - 1 / 2) * Real.log (2 * π)))
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun s ↦ |s.im|⁻¹ := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gammaℂ_vertical_sub_le a b
  exact isBigO_inv_vertical_strip_of_exists ⟨C, T, fun s hs ht ↦ by simpa using h s hs ht⟩

/-- Stirling's formula for `Gammaℂ` on a single vertical line `Re s = σ`. -/
theorem isBigO_log_norm_Gammaℂ_vertical_line_sub (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gammaℂ (σ + t * I)‖ -
        (-π * |t| / 2 + (σ - 1 / 2) * Real.log |t| +
          Real.log 2 - (σ - 1 / 2) * Real.log (2 * π)))
      =O[cocompact ℝ] fun t ↦ |t|⁻¹ :=
  (isBigO_log_norm_Gammaℂ_vertical_sub σ σ).cocompact_of_vertical (left_mem_Icc.2 le_rfl)

/-! ### Complex-shifted `Gammaℝ` and `Gammaℂ` on vertical strips (`O(1)` form) -/

/-- Bound the perturbation when replacing `w = s + μ` by `s` in the main Stirling terms of
`Gammaℝ` and dropping the bounded constant term `(log 2 - (w.re - 1) log (2π)) / 2`. -/
private theorem abs_Gammaℝ_shift_perturbation_le {s w : ℂ} {R M : ℝ}
    (hwre1 : |w.re - 1| ≤ R + 1) (hwim1 : 1 ≤ |w.im|) (hsim1 : 1 ≤ |s.im|)
    (him_diff : |(|w.im| - |s.im|)| ≤ M) :
    |(-π * |w.im| / 4 - (-π * |s.im| / 4)) +
        ((w.re - 1) / 2 * (Real.log |w.im| - Real.log |s.im|) +
          (Real.log 2 - (w.re - 1) * Real.log (2 * π)) / 2)| ≤
      π * M / 4 + (R + 1) / 2 * M + (Real.log 2 + (R + 1) * Real.log (2 * π)) / 2 := by
  have hR1 : 0 ≤ R + 1 := (abs_nonneg _).trans hwre1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hlog2pi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.two_le_pi])
  have hexp_diff : |-π * |w.im| / 4 - (-π * |s.im| / 4)| ≤ π * M / 4 := by
    have hlin : -π * |w.im| / 4 - (-π * |s.im| / 4) = -(π / 4) * (|w.im| - |s.im|) := by ring
    rw [hlin, abs_mul, abs_neg, abs_of_nonneg (by positivity)]
    nlinarith [Real.pi_pos]
  have hlog_diff : |(w.re - 1) / 2 * (Real.log |w.im| - Real.log |s.im|)| ≤ (R + 1) / 2 * M := by
    rw [abs_mul, abs_div, abs_two]
    exact mul_le_mul (div_le_div_of_nonneg_right hwre1 zero_le_two)
      ((Real.abs_log_sub_log_le hwim1 hsim1).trans him_diff) (abs_nonneg _) (by positivity)
  have hconst : |(Real.log 2 - (w.re - 1) * Real.log (2 * π)) / 2| ≤
      (Real.log 2 + (R + 1) * Real.log (2 * π)) / 2 := by
    rw [abs_div, abs_two]
    refine div_le_div_of_nonneg_right ?_ zero_le_two
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg hlog2, abs_mul, abs_of_nonneg hlog2pi]
    linarith [mul_le_mul_of_nonneg_right hwre1 hlog2pi]
  exact ((abs_add_le _ _).trans
    (add_le_add hexp_diff ((abs_add_le _ _).trans (add_le_add hlog_diff hconst)))).trans_eq
    (by ring)

/-- Uniform `O(1)` vertical-strip bound for the Stirling remainder of `log ‖Gammaℝ (s + μ)‖` across
all shifts `μ` with `‖μ‖ ≤ M`: the constant `C` and threshold `T` depend only on `a`, `b`, and
`M`. -/
theorem exists_abs_log_norm_Gammaℝ_add_vertical_sub_le (a b : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∃ T > 0, ∀ μ : ℂ, ‖μ‖ ≤ M → ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Complex.Gammaℝ (s + μ)‖ -
          (-π * |s.im| / 4 + (s.re + μ.re - 1) / 2 * Real.log |s.im|)| ≤ C := by
  set B := max |a| |b|
  have : 0 ≤ B := (abs_nonneg a).trans (le_max_left _ _)
  set R := B + M
  set K := 4 / (1 - Real.cos (π / 4)) ^ 3 + (R + 1) * R / 2 + R ^ 2 / 2
  have hK0 : 0 ≤ K := by
    have : 0 ≤ 1 - Real.cos (π / 4) := sub_nonneg.2 (Real.cos_le_one _)
    positivity
  have : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.two_le_pi])
  set C := K + π * M / 4 + (R + 1) / 2 * M + (Real.log 2 + (R + 1) * Real.log (2 * π)) / 2
  refine ⟨C, by positivity, R + M + 2, by positivity, fun μ hμ s hs ht ↦ ?_⟩
  have hsB : |s.re| ≤ B := abs_le_max_abs_abs hs.1 hs.2
  have hμre : |μ.re| ≤ M := (abs_re_le_norm μ).trans hμ
  have hμim : |μ.im| ≤ M := (abs_im_le_norm μ).trans hμ
  set w := s + μ
  have hwre : |w.re| ≤ R := by
    simpa [w, R] using (abs_add_le s.re μ.re).trans (add_le_add hsB hμre)
  have hwim_ge : R + 2 ≤ |w.im| := by
    have h := abs_sub_abs_le_abs_sub s.im (-μ.im)
    simp only [abs_neg, sub_neg_eq_add] at h
    simpa [w] using (by linarith : R + 2 ≤ |s.im| - |μ.im|).trans h
  have hwre1 : |w.re - 1| ≤ R + 1 := abs_le.2
    ⟨by linarith [(abs_le.1 hwre).1], by linarith [(abs_le.1 hwre).2]⟩
  have hmain : |Real.log ‖Complex.Gammaℝ w‖ -
      (-π * |w.im| / 4 + (w.re - 1) / 2 * Real.log |w.im| +
        (Real.log 2 - (w.re - 1) * Real.log (2 * π)) / 2)| ≤ K :=
    (abs_log_norm_Gammaℝ_vertical_sub_le_of_re_le hwre (by linarith)).trans
      (div_le_self hK0 (by linarith))
  have htail := abs_Gammaℝ_shift_perturbation_le hwre1 (by linarith) (by linarith)
    ((abs_abs_sub_abs_le_abs_sub w.im s.im).trans (by simpa [w] using hμim))
  have hsplit : Real.log ‖Complex.Gammaℝ w‖ -
      (-π * |s.im| / 4 + (s.re + μ.re - 1) / 2 * Real.log |s.im|) =
      (Real.log ‖Complex.Gammaℝ w‖ -
        (-π * |w.im| / 4 + (w.re - 1) / 2 * Real.log |w.im| +
          (Real.log 2 - (w.re - 1) * Real.log (2 * π)) / 2)) +
      ((-π * |w.im| / 4 - (-π * |s.im| / 4)) +
        ((w.re - 1) / 2 * (Real.log |w.im| - Real.log |s.im|) +
          (Real.log 2 - (w.re - 1) * Real.log (2 * π)) / 2)) := by
    simp only [w, add_re]
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  dsimp only [C]
  linarith

/-- Uniform `O(1)` vertical-strip bound for the Stirling remainder of `log ‖Gammaℂ (s + ν)‖` across
all shifts `ν` with `‖ν‖ ≤ M`: the constant `C` and threshold `T` depend only on `a`, `b`, and
`M`. -/
theorem exists_abs_log_norm_Gammaℂ_add_vertical_sub_le (a b : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∃ T > 0, ∀ ν : ℂ, ‖ν‖ ≤ M → ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Complex.Gammaℂ (s + ν)‖ -
          (-π * |s.im| / 2 + (s.re + ν.re - 1 / 2) * Real.log |s.im|)| ≤ C := by
  obtain ⟨C, hC0, T, hT0, hR⟩ :=
    exists_abs_log_norm_Gammaℝ_add_vertical_sub_le a b (M := M + 1) (by linarith)
  refine ⟨2 * C, by positivity, max T (M + 2), by positivity, fun ν hν s hs ht ↦ ?_⟩
  have hν1 : ‖ν‖ ≤ M + 1 := by linarith
  have hν2 : ‖ν + 1‖ ≤ M + 1 := (norm_add_le ν 1).trans (by simpa using add_le_add_right hν 1)
  have htT : T ≤ |s.im| := (le_max_left _ _).trans ht
  have htM : M + 2 ≤ |s.im| := (le_max_right _ _).trans ht
  have hνim : |ν.im| ≤ M := (abs_im_le_norm ν).trans hν
  have him_ne : (s + ν).im ≠ 0 := by
    have h := abs_sub_abs_le_abs_sub s.im (-ν.im)
    simp only [abs_neg, sub_neg_eq_add] at h
    exact abs_pos.1 (by simpa using (by linarith : (0 : ℝ) < |s.im| - |ν.im|).trans_le h)
  have him1_ne : (s + ν + 1).im ≠ 0 := by simpa using him_ne
  -- Reduce `Gammaℂ (s + ν)` to `Gammaℝ (s + ν) * Gammaℝ (s + (ν + 1))` by duplication.
  have hdup : Real.log ‖Complex.Gammaℂ (s + ν)‖ =
      Real.log ‖Complex.Gammaℝ (s + ν)‖ + Real.log ‖Complex.Gammaℝ (s + (ν + 1))‖ := by
    rw [← Gammaℝ_mul_Gammaℝ_add_one (s + ν), norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 (Gammaℝ_ne_zero_of_im_ne_zero him_ne))
        (norm_ne_zero_iff.2 (Gammaℝ_ne_zero_of_im_ne_zero him1_ne)), add_assoc]
  have h1 := hR ν hν1 s hs htT
  have h2 := hR (ν + 1) hν2 s hs htT
  have hsplit : Real.log ‖Complex.Gammaℂ (s + ν)‖ -
      (-π * |s.im| / 2 + (s.re + ν.re - 1 / 2) * Real.log |s.im|) =
      (Real.log ‖Complex.Gammaℝ (s + ν)‖ -
        (-π * |s.im| / 4 + (s.re + ν.re - 1) / 2 * Real.log |s.im|)) +
      (Real.log ‖Complex.Gammaℝ (s + (ν + 1))‖ -
        (-π * |s.im| / 4 + (s.re + (ν + 1).re - 1) / 2 * Real.log |s.im|)) := by
    rw [hdup]
    simp only [add_re, one_re]
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (by linarith)

/-- `O(1)` vertical-strip asymptotic for a complex-shifted `Gammaℝ` factor along
`𝓟 (Icc a b) ×ˢ cocompact ℝ`. -/
theorem isBigO_log_norm_Gammaℝ_add_vertical_sub (a b : ℝ) (μ : ℂ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖Complex.Gammaℝ (p.1 + p.2 * I + μ)‖ -
        (-π * |p.2| / 4 + (p.1 + μ.re - 1) / 2 * Real.log |p.2|))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := exists_abs_log_norm_Gammaℝ_add_vertical_sub_le a b (norm_nonneg μ)
  refine isBigO_one_vertical_of_exists ⟨C, T, fun p hσ ht ↦ ?_⟩
  simpa using h μ le_rfl (p.1 + p.2 * I) (by simpa using hσ) (by simpa using ht)

/-- `O(1)` vertical-strip asymptotic for a complex-shifted `Gammaℝ` factor on `Re s ∈ [a, b]`. -/
theorem isBigO_log_norm_Gammaℝ_add_vertical_strip_sub (a b : ℝ) (μ : ℂ) :
    (fun s : ℂ ↦ Real.log ‖Complex.Gammaℝ (s + μ)‖ -
        (-π * |s.im| / 4 + (s.re + μ.re - 1) / 2 * Real.log |s.im|))
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := exists_abs_log_norm_Gammaℝ_add_vertical_sub_le a b (norm_nonneg μ)
  exact isBigO_one_vertical_strip_of_exists ⟨C, T, fun s hs ht ↦ by simpa using h μ le_rfl s hs ht⟩

/-- `O(1)` vertical-line asymptotic for `t ↦ log ‖Gammaℝ (σ + i t + μ)‖`. -/
theorem isBigO_log_norm_Gammaℝ_add_vertical_line_sub (σ : ℝ) (μ : ℂ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gammaℝ (σ + t * I + μ)‖ -
        (-π * |t| / 4 + (σ + μ.re - 1) / 2 * Real.log |t|))
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) :=
  (isBigO_log_norm_Gammaℝ_add_vertical_sub σ σ μ).cocompact_of_vertical (left_mem_Icc.2 le_rfl)

/-- `O(1)` vertical-strip asymptotic for a complex-shifted `Gammaℂ` factor along
`𝓟 (Icc a b) ×ˢ cocompact ℝ`. -/
theorem isBigO_log_norm_Gammaℂ_add_vertical_sub (a b : ℝ) (ν : ℂ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖Complex.Gammaℂ (p.1 + p.2 * I + ν)‖ -
        (-π * |p.2| / 2 + (p.1 + ν.re - 1 / 2) * Real.log |p.2|))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := exists_abs_log_norm_Gammaℂ_add_vertical_sub_le a b (norm_nonneg ν)
  refine isBigO_one_vertical_of_exists ⟨C, T, fun p hσ ht ↦ ?_⟩
  simpa using h ν le_rfl (p.1 + p.2 * I) (by simpa using hσ) (by simpa using ht)

/-- `O(1)` vertical-strip asymptotic for a complex-shifted `Gammaℂ` factor on `Re s ∈ [a, b]`. -/
theorem isBigO_log_norm_Gammaℂ_add_vertical_strip_sub (a b : ℝ) (ν : ℂ) :
    (fun s : ℂ ↦ Real.log ‖Complex.Gammaℂ (s + ν)‖ -
        (-π * |s.im| / 2 + (s.re + ν.re - 1 / 2) * Real.log |s.im|))
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := exists_abs_log_norm_Gammaℂ_add_vertical_sub_le a b (norm_nonneg ν)
  exact isBigO_one_vertical_strip_of_exists ⟨C, T, fun s hs ht ↦ by simpa using h ν le_rfl s hs ht⟩

/-- `O(1)` vertical-line asymptotic for `t ↦ log ‖Gammaℂ (σ + i t + ν)‖`. -/
theorem isBigO_log_norm_Gammaℂ_add_vertical_line_sub (σ : ℝ) (ν : ℂ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gammaℂ (σ + t * I + ν)‖ -
        (-π * |t| / 2 + (σ + ν.re - 1 / 2) * Real.log |t|))
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) :=
  (isBigO_log_norm_Gammaℂ_add_vertical_sub σ σ ν).cocompact_of_vertical (left_mem_Icc.2 le_rfl)

-- Non-real shift check: for `μ = I` along `s = t * I`, `Gammaℝ (conj z) = conj (Gammaℝ z)` pairs
-- `t` with `-(t + 2)`, where `log ‖Gammaℝ‖` cancels identically while the linear exponential terms
-- differ by `-π / 2`, so the `O(1)` error cannot be improved to `o(1)`.
example : ¬ ((fun t : ℝ ↦ Real.log ‖Complex.Gammaℝ ((0 : ℝ) + t * I + I)‖ -
    (-π * |t| / 4 + (0 + I.re - 1) / 2 * Real.log |t|)) =o[cocompact ℝ] fun _ ↦ (1 : ℝ)) := by
  set f : ℝ → ℝ := fun t ↦ Real.log ‖Complex.Gammaℝ ((0 : ℝ) + t * I + I)‖ -
    (-π * |t| / 4 + (0 + I.re - 1) / 2 * Real.log |t|)
  intro ho
  have hlim : Tendsto f (cocompact ℝ) (𝓝 0) := by simpa using ho.tendsto_div_nhds_zero
  have hatTop : Tendsto f atTop (𝓝 0) :=
    hlim.mono_left (le_sup_right.trans_eq _root_.cocompact_eq_atBot_atTop.symm)
  have hatBot : Tendsto (fun t : ℝ ↦ f (-(t + 2))) atTop (𝓝 0) :=
    (hlim.mono_left (le_sup_left.trans_eq _root_.cocompact_eq_atBot_atTop.symm)).comp
      (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right atTop 2 tendsto_id))
  have hdiff0 : Tendsto (fun t : ℝ ↦ f t - f (-(t + 2))) atTop (𝓝 0) := by
    simpa using hatTop.sub hatBot
  have hdiff_lim : Tendsto (fun t : ℝ ↦ -π / 2 - (Real.log (t + 2) - Real.log t) / 2)
      atTop (𝓝 (-π / 2)) := by
    simpa using tendsto_const_nhds.sub ((Real.tendsto_log_comp_add_sub_log 2).div_const 2)
  have hdiff_eq : (fun t : ℝ ↦ -π / 2 - (Real.log (t + 2) - Real.log t) / 2) =ᶠ[atTop]
      fun t : ℝ ↦ f t - f (-(t + 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hconj : ((0 : ℝ) : ℂ) + (-(t + 2) : ℝ) * I + I =
        (starRingEnd ℂ) (((0 : ℝ) : ℂ) + t * I + I) := by
      apply Complex.ext <;> simp
      ring
    have hnorm : ‖Complex.Gammaℝ (((0 : ℝ) : ℂ) + (-(t + 2) : ℝ) * I + I)‖ =
        ‖Complex.Gammaℝ (((0 : ℝ) : ℂ) + t * I + I)‖ := by
      rw [hconj, Complex.Gammaℝ_conj, Complex.norm_conj]
    have ht2 : -(t + 2) < 0 := by linarith
    dsimp only [f]
    rw [hnorm, abs_of_pos ht, abs_of_neg ht2, neg_neg]
    simp only [I_re]
    ring
  linarith [Real.pi_pos, tendsto_nhds_unique (hdiff_lim.congr' hdiff_eq) hdiff0]

end TauCeti
