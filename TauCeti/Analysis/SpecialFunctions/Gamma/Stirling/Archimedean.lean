/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean

/-!
# Stirling's formula for the archimedean factors on vertical strips

For every compact interval `[a, b]`, uniformly for `σ ∈ [a, b]` as `|t| → ∞`,

* `log ‖Γ_ℝ(σ + i t)‖ = ((σ - 1) / 2) log (|t| / 2π) - (π / 4) |t| + (log 2) / 2 + O(1 / |t|)`;
* `log ‖Γ_ℂ(σ + i t)‖ = (σ - 1/2) log (|t| / 2π) - (π / 2) |t| + log 2 + O(1 / |t|)`.

Here `Γ_ℝ(s) = π ^ (-s/2) Γ(s/2)` and `Γ_ℂ(s) = 2 (2π) ^ (-s) Γ(s)` are Mathlib's
`Complex.Gammaℝ` and `Complex.Gammaℂ`. Both follow from Stirling's formula for `Γ` on vertical
strips, `TauCeti.exists_abs_log_norm_Gamma_vertical_sub_le`, since `‖x ^ (-s)‖ = x ^ (-Re s)`
for `x > 0`. The two expansions are compatible with the duplication formula
`Γ_ℂ(s) = Γ_ℝ(s) Γ_ℝ(s + 1)`.

For a shift `μ : ℂ` the factors `Γ_ℝ(s + μ)` and `Γ_ℂ(s + μ)` satisfy the same expansions in the
coarser additive form with remainder `O(1)` and with `log |t|` in place of
`log (|t + Im μ| / 2π)`: the exponential rates `π / 4` and `π / 2` are unchanged, and the
coefficient of `log |t|` is `(σ + Re μ - 1) / 2`, respectively `σ + Re μ - 1/2`. This is the form
that adds up over the finite products of shifted factors forming the gamma factor of an
L-function.

## Main results

* `TauCeti.exists_abs_log_norm_Gammaℝ_vertical_sub_le`,
  `TauCeti.isBigO_log_norm_Gammaℝ_vertical_sub`: the expansion of `log ‖Γ_ℝ‖`.
* `TauCeti.exists_abs_log_norm_Gammaℂ_vertical_sub_le`,
  `TauCeti.isBigO_log_norm_Gammaℂ_vertical_sub`: the expansion of `log ‖Γ_ℂ‖`.
* `TauCeti.exists_abs_log_norm_Gammaℝ_add_vertical_sub_le`,
  `TauCeti.exists_abs_log_norm_Gammaℂ_add_vertical_sub_le`: the shifted factors, with
  remainder `O(1)`.

## References

* [DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9).
* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
-/

public section

open Complex Real Filter Set Asymptotics

namespace TauCeti

/-- A point off the real axis is not a nonpositive integer. -/
private theorem ne_neg_natCast_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) (m : ℕ) : s ≠ -(m : ℂ) :=
  fun h ↦ hs (by simp [h])

/-- `log ‖x ^ (-w)‖ = -(Re w) log x` for real `x > 0`. -/
private theorem log_norm_cpow_neg {x : ℝ} (hx : 0 < x) (w : ℂ) :
    Real.log ‖(x : ℂ) ^ (-w)‖ = -w.re * Real.log x := by
  rw [norm_cpow_eq_rpow_re_of_pos hx, Real.log_rpow hx, neg_re]

/-- A bound `|u s| ≤ C / |Im s|` on a strip `a ≤ Re s ≤ b` above a height threshold is an
`O(1 / |t|)` statement along `𝓟 (Icc a b) ×ˢ cocompact ℝ` in the coordinates `s = σ + i t`. -/
private theorem isBigO_vertical_of_exists_abs_le_div {u : ℂ → ℝ} {a b : ℝ}
    (h : ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| → |u s| ≤ C / |s.im|) :
    (fun p : ℝ × ℝ ↦ u (p.1 + p.2 * I)) =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun p ↦ |p.2|⁻¹ := by
  obtain ⟨C, T, h⟩ := h
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ t : ℝ in cocompact ℝ, T ≤ |t| := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop T] with t ht
    rwa [Real.norm_eq_abs] at ht
  filter_upwards [(eventually_principal.2 fun _ hσ ↦ hσ).prod_mk hT] with p hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_abs, ← div_eq_mul_inv]
  simpa using h (p.1 + p.2 * I) (by simpa using hp.1) (by simpa using hp.2)

/-- **Stirling's formula for `Γ_ℝ` on vertical strips**, explicit form: one constant and one
threshold for the strip `a ≤ Re s ≤ b`, with
`|log ‖Γ_ℝ(s)‖ - ((σ - 1)/2 log (|t| / 2π) - (π/4) |t| + (log 2)/2)| ≤ C / |t|` for
`s = σ + i t` with `T ≤ |t|`. -/
theorem exists_abs_log_norm_Gammaℝ_vertical_sub_le (a b : ℝ) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Gammaℝ s‖ -
          ((s.re - 1) / 2 * Real.log (|s.im| / (2 * π)) - π / 4 * |s.im| + Real.log 2 / 2)| ≤
        C / |s.im| := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le (a / 2) (b / 2)
  refine ⟨2 * C, max (2 * T) 1, fun s hs hT ↦ ?_⟩
  have ht : 0 < |s.im| := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hT)
  have hre : (s / 2).re = s.re / 2 := by simp
  have him : |(s / 2).im| = |s.im| / 2 := by simp [abs_div]
  have hΓ := h (s / 2) (by rw [hre]; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
    (by rw [him]; linarith [(le_max_left _ _).trans hT])
  rw [hre, him, div_div_eq_mul_div] at hΓ
  have hne : Complex.Gamma (s / 2) ≠ 0 :=
    Complex.Gamma_ne_zero (ne_neg_natCast_of_im_ne_zero (by simpa using abs_pos.1 ht))
  have hlog : Real.log ‖Gammaℝ s‖ =
      -(s.re / 2) * Real.log π + Real.log ‖Complex.Gamma (s / 2)‖ := by
    rw [Gammaℝ_def, norm_mul, Real.log_mul (by simp [Real.pi_pos.ne']) (norm_ne_zero_iff.2 hne),
      neg_div, log_norm_cpow_neg Real.pi_pos, div_ofNat_re]
  have h2π : Real.log (|s.im| / (2 * π)) = Real.log |s.im| - Real.log 2 - Real.log π := by
    rw [Real.log_div ht.ne' (by positivity), Real.log_mul two_ne_zero Real.pi_pos.ne']
    ring
  have h2 : Real.log (|s.im| / 2) = Real.log |s.im| - Real.log 2 :=
    Real.log_div ht.ne' two_ne_zero
  have h2π' : Real.log (2 * π) = Real.log 2 + Real.log π :=
    Real.log_mul two_ne_zero Real.pi_pos.ne'
  rw [hlog, h2π]
  rw [h2, h2π'] at hΓ
  calc _ = |Real.log ‖Complex.Gamma (s / 2)‖ - ((s.re / 2 - 1 / 2) *
          (Real.log |s.im| - Real.log 2) - π * (|s.im| / 2) / 2 +
            (Real.log 2 + Real.log π) / 2)| := by congr 1; ring
    _ ≤ C * 2 / |s.im| := hΓ
    _ = 2 * C / |s.im| := by rw [mul_comm]

/-- **Stirling's formula for `Γ_ℝ` on vertical strips**:
`log ‖Γ_ℝ(σ + i t)‖ = ((σ - 1)/2) log (|t| / 2π) - (π/4) |t| + (log 2)/2 + O(1 / |t|)` uniformly
for `σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gammaℝ_vertical_sub (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖Gammaℝ (p.1 + p.2 * I)‖ -
        ((p.1 - 1) / 2 * Real.log (|p.2| / (2 * π)) - π / 4 * |p.2| + Real.log 2 / 2))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun p ↦ |p.2|⁻¹ := by
  simpa using isBigO_vertical_of_exists_abs_le_div (exists_abs_log_norm_Gammaℝ_vertical_sub_le a b)

/-- **Stirling's formula for `Γ_ℂ` on vertical strips**, explicit form: one constant and one
threshold for the strip `a ≤ Re s ≤ b`, with
`|log ‖Γ_ℂ(s)‖ - ((σ - 1/2) log (|t| / 2π) - (π/2) |t| + log 2)| ≤ C / |t|` for `s = σ + i t`
with `T ≤ |t|`. -/
theorem exists_abs_log_norm_Gammaℂ_vertical_sub_le (a b : ℝ) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Gammaℂ s‖ -
          ((s.re - 1 / 2) * Real.log (|s.im| / (2 * π)) - π / 2 * |s.im| + Real.log 2)| ≤
        C / |s.im| := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  refine ⟨C, max T 1, fun s hs hT ↦ ?_⟩
  have ht : 0 < |s.im| := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hT)
  have hΓ := h s hs ((le_max_left _ _).trans hT)
  have hne : Complex.Gamma s ≠ 0 :=
    Complex.Gamma_ne_zero (ne_neg_natCast_of_im_ne_zero (abs_pos.1 ht))
  have h2π : 0 < 2 * π := by positivity
  have hlog : Real.log ‖Gammaℂ s‖ =
      Real.log 2 - s.re * Real.log (2 * π) + Real.log ‖Complex.Gamma s‖ := by
    rw [Gammaℂ_def, norm_mul, norm_mul,
      Real.log_mul (mul_ne_zero (by simp) (by simp)) (norm_ne_zero_iff.2 hne),
      Real.log_mul (by simp) (by simp), ← ofReal_ofNat, ← ofReal_mul,
      log_norm_cpow_neg h2π]
    simp
    ring
  rw [hlog, Real.log_div ht.ne' h2π.ne']
  calc _ = |Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2)| := by
          congr 1; ring
    _ ≤ C / |s.im| := hΓ

/-- **Stirling's formula for `Γ_ℂ` on vertical strips**:
`log ‖Γ_ℂ(σ + i t)‖ = (σ - 1/2) log (|t| / 2π) - (π/2) |t| + log 2 + O(1 / |t|)` uniformly for
`σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gammaℂ_vertical_sub (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖Gammaℂ (p.1 + p.2 * I)‖ -
        ((p.1 - 1 / 2) * Real.log (|p.2| / (2 * π)) - π / 2 * |p.2| + Real.log 2))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun p ↦ |p.2|⁻¹ := by
  simpa using isBigO_vertical_of_exists_abs_le_div (exists_abs_log_norm_Gammaℂ_vertical_sub_le a b)

/-- `|log |t + c| - log |t|| ≤ 1` once `2 |c| ≤ |t|` and `t ≠ 0`: the ratio `|t + c| / |t|` lies
in `[1/2, 3/2]`. -/
private theorem abs_log_abs_add_sub_log_abs_le {t c : ℝ} (ht : 0 < |t|) (hc : 2 * |c| ≤ |t|) :
    |Real.log |t + c| - Real.log (|t|)| ≤ 1 := by
  have hlo : |t| / 2 ≤ |t + c| := by
    have := abs_sub_abs_le_abs_sub t (-c)
    rw [sub_neg_eq_add, abs_neg] at this
    linarith
  have hhi : |t + c| ≤ 2 * |t| := by linarith [abs_add_le t c]
  have hpos : 0 < |t + c| := by linarith
  rw [← Real.log_div hpos.ne' ht.ne', abs_le]
  constructor
  · rw [neg_le, ← Real.log_inv, inv_div]
    refine (Real.log_le_sub_one_of_pos (div_pos ht hpos)).trans ?_
    rw [sub_le_iff_le_add, div_le_iff₀ hpos]
    linarith
  · refine (Real.log_le_sub_one_of_pos (div_pos hpos ht)).trans ?_
    rw [sub_le_iff_le_add, div_le_iff₀ ht]
    linarith

/-- Passing from an expansion `f(w) = p(Re w) log (|Im w| / 2π) - κ |Im w| + e + O(1/|Im w|)`
on vertical strips to the coarser expansion of the shifted function
`f(s + μ) = p(Re s + Re μ) log |Im s| - κ |Im s| + O(1)`, for continuous `p`. -/
private theorem exists_abs_add_vertical_sub_le_of_vertical {f : ℂ → ℝ} {p : ℝ → ℝ}
    (hp : Continuous p) (κ e : ℝ) (μ : ℂ) {a b : ℝ}
    (hf : ∃ C T : ℝ, ∀ w : ℂ, w.re ∈ Icc (a + μ.re) (b + μ.re) → T ≤ |w.im| →
      |f w - (p w.re * Real.log (|w.im| / (2 * π)) - κ * |w.im| + e)| ≤ C / |w.im|) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |f (s + μ) - (p (s.re + μ.re) * Real.log |s.im| - κ * |s.im|)| ≤ C := by
  obtain ⟨C, T, h⟩ := hf
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := a + μ.re) (b := b + μ.re)).exists_bound_of_continuousOn
    hp.continuousOn
  refine ⟨|C| + M * (1 + |Real.log (2 * π)|) + |κ| * |μ.im| + |e|, |T| + 2 * |μ.im| + 2,
    fun s hs hT ↦ ?_⟩
  set w := s + μ
  have hwre : w.re ∈ Icc (a + μ.re) (b + μ.re) := by
    simp only [w, add_re]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hwim : w.im = s.im + μ.im := by simp [w]
  have hts : 0 < |s.im| := by linarith [abs_nonneg T, abs_nonneg μ.im]
  have hlow : |s.im| - |μ.im| ≤ |w.im| := by
    have := abs_sub_abs_le_abs_sub s.im (-μ.im)
    rw [sub_neg_eq_add, abs_neg, ← hwim] at this
    exact this
  have hw1 : 1 ≤ |w.im| := by linarith [abs_nonneg T]
  have hwpos : 0 < |w.im| := by linarith
  have hfw := h w hwre (by linarith [le_abs_self T, abs_nonneg μ.im])
  -- the remainder `C / |Im w|` is at most `|C|`
  have hC : C / |w.im| ≤ |C| :=
    (div_le_div_of_nonneg_right (le_abs_self C) hwpos.le).trans (div_le_self (abs_nonneg C) hw1)
  -- the logarithmic term
  have hlog : |Real.log (|w.im| / (2 * π)) - Real.log (|s.im|)| ≤ 1 + |Real.log (2 * π)| := by
    rw [Real.log_div hwpos.ne' (by positivity), hwim]
    have := abs_log_abs_add_sub_log_abs_le hts (c := μ.im) (by linarith [abs_nonneg T])
    calc _ = |(Real.log |s.im + μ.im| - Real.log |s.im|) - Real.log (2 * π)| := by ring_nf
      _ ≤ _ := (abs_sub _ _).trans (by linarith)
  have hpw : |p w.re| ≤ M := by simpa using hM w.re hwre
  have hplog : |p w.re * (Real.log (|w.im| / (2 * π)) - Real.log |s.im|)| ≤
      M * (1 + |Real.log (2 * π)|) := by
    rw [abs_mul]
    exact mul_le_mul hpw hlog (abs_nonneg _) ((abs_nonneg _).trans hpw)
  -- the exponential-rate term
  have habs : |κ * (|w.im| - |s.im|)| ≤ |κ| * |μ.im| := by
    rw [abs_mul, hwim]
    exact mul_le_mul_of_nonneg_left (by simpa using abs_abs_sub_abs_le_abs_sub (s.im + μ.im) s.im)
      (abs_nonneg κ)
  have hsplit : f w - (p (s.re + μ.re) * Real.log |s.im| - κ * |s.im|) =
      (f w - (p w.re * Real.log (|w.im| / (2 * π)) - κ * |w.im| + e)) +
        p w.re * (Real.log (|w.im| / (2 * π)) - Real.log |s.im|) - κ * (|w.im| - |s.im|) + e := by
    simp only [w, add_re]
    ring
  have h1 := abs_le.1 (hfw.trans hC)
  have h2 := abs_le.1 hplog
  have h3 := abs_le.1 habs
  rw [hsplit, abs_le]
  constructor <;> linarith [neg_abs_le e, le_abs_self e]

/-- Stirling's formula for a shifted `Γ_ℝ` on vertical strips, in additive form with bounded
remainder: for `μ : ℂ` there are `C` and `T` with
`|log ‖Γ_ℝ(s + μ)‖ - (((σ + Re μ - 1)/2) log |t| - (π/4) |t|)| ≤ C` for `s = σ + i t`,
`σ ∈ [a, b]` and `T ≤ |t|`. -/
theorem exists_abs_log_norm_Gammaℝ_add_vertical_sub_le (a b : ℝ) (μ : ℂ) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Gammaℝ (s + μ)‖ -
          ((s.re + μ.re - 1) / 2 * Real.log |s.im| - π / 4 * |s.im|)| ≤ C :=
  exists_abs_add_vertical_sub_le_of_vertical (f := fun w ↦ Real.log ‖Gammaℝ w‖)
    (p := fun σ ↦ (σ - 1) / 2) (by fun_prop) (π / 4) (Real.log 2 / 2) μ
    (exists_abs_log_norm_Gammaℝ_vertical_sub_le _ _)

/-- Stirling's formula for a shifted `Γ_ℂ` on vertical strips, in additive form with bounded
remainder: for `ν : ℂ` there are `C` and `T` with
`|log ‖Γ_ℂ(s + ν)‖ - ((σ + Re ν - 1/2) log |t| - (π/2) |t|)| ≤ C` for `s = σ + i t`,
`σ ∈ [a, b]` and `T ≤ |t|`. -/
theorem exists_abs_log_norm_Gammaℂ_add_vertical_sub_le (a b : ℝ) (ν : ℂ) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Gammaℂ (s + ν)‖ -
          ((s.re + ν.re - 1 / 2) * Real.log |s.im| - π / 2 * |s.im|)| ≤ C :=
  exists_abs_add_vertical_sub_le_of_vertical (f := fun w ↦ Real.log ‖Gammaℂ w‖)
    (p := fun σ ↦ σ - 1 / 2) (by fun_prop) (π / 2) (Real.log 2) ν
    (exists_abs_log_norm_Gammaℂ_vertical_sub_le _ _)

end TauCeti
