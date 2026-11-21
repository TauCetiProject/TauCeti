/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
import Mathlib.Analysis.Asymptotics.Prod
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.Asymptotics.VerticalStrip
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.SpecialFunctions.Log.GrowthScale
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Stirling's formula on vertical strips

For every compact interval `[a, b]`,
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)`
uniformly for `σ ∈ [a, b]` as `|t| → ∞`, that is along `cocompact ℝ`
([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9), with the remainder of
[DLMF 5.11.1](https://dlmf.nist.gov/5.11.E1)). The statement is additive in `log ‖Γ‖`, so it adds
up over finite products of shifted Gamma factors. Exponentiating and combining with compactness on
bounded imaginary parts gives uniform norm bounds with pointwise real-part exponents for `Γ` away
from the real axis, on any pole-free vertical line (including complex shifts `w ± i y`), and for
the entire reciprocal `Γ⁻¹` across the whole strip; Cauchy's estimate on unit circles then bounds
the derivative of `Γ⁻¹` across the strip and uniformly on unit balls.

The proof is the sector form `TauCeti.abs_log_norm_Gamma_sub_stirling_le`
(`TauCeti/Analysis/SpecialFunctions/Gamma/Stirling/Basic.lean`) at the angle `π / 4`.
Once `|σ| ≤ |t|` the point `σ + i t` has `|arg| ≤ 3π/4`, and the sector main term
`(σ - 1/2) log ‖s‖ - t arg s - σ` differs from the vertical one by two terms of size `O(1 / |t|)`:

* `0 ≤ log ‖s‖ - log |t| ≤ |σ| / |t|`, since `|t| ≤ ‖s‖ ≤ |t| + |σ|`;
* for `t > 0`, `π / 2 - arg s = arctan (σ / t)` (`Complex.arg_eq_pi_div_two_sub_arctan_of_im_pos`)
  and `|arctan x - x| ≤ |x| ^ 3` (`Real.abs_arctan_sub_self_le`), so `t (π / 2 - arg s) - σ` is at
  most `σ ^ 2 / t` in absolute value.

Negative `t` reduces to positive `t` by `Γ(conj s) = conj (Γ s)`.

## Main declarations

* `TauCeti.abs_log_norm_Gamma_vertical_sub_le`: the explicit bound
  `(1 / (8 * sin (π / 8) ^ 2) + |σ - 1/2| |σ| + σ ^ 2) / |t|` at every `s = σ + i t` with
  `t ≠ 0` and `|σ| ≤ |t|`.
* `TauCeti.exists_abs_log_norm_Gamma_vertical_sub_le`: one constant and one threshold for all `s`
  with `Re s ∈ [a, b]`.
* `TauCeti.exists_abs_log_norm_Gamma_add_vertical_sub_le`: the same for `Γ(s + μ)` with a fixed
  shift `μ`, measured against `log |Im s|` and `|Im s|` up to a bounded error.
* `TauCeti.isBigO_log_norm_Gamma_vertical_sub`: the uniform `O(1 / |t|)` form in `(σ, t)` along
  `𝓟 (Icc a b) ×ˢ cocompact ℝ`.
* `TauCeti.isBigO_log_norm_Gamma_vertical_strip_sub`: the same as a function of `s : ℂ`, along
  `cocompact ℂ` restricted to the strip `Re s ∈ [a, b]`.
* `TauCeti.isBigO_log_norm_Gamma_vertical_line_sub`: the same on a single vertical line, along
  `cocompact ℝ`.
* `TauCeti.exists_norm_Gamma_vertical_strip_le`: uniform upper bound
  `C (1 + |Im s|) ^ (Re s - 1/2) exp (-π |Im s| / 2)` on `Re s ∈ [a, b]` and `δ ≤ |Im s|`.
* `TauCeti.exists_norm_Gamma_vertical_line_le`, `TauCeti.exists_norm_Gamma_add_I_le`,
  `TauCeti.exists_norm_Gamma_sub_I_le`: uniform upper bounds
  `C (1 + |t|) ^ (σ - 1/2) exp (-π |t| / 2)` and `C (1 + |y|) ^ (Re w - 1/2) exp (-π |y| / 2)` on
  pole-free vertical lines.
* `TauCeti.exists_norm_inv_Gamma_vertical_strip_le`,
  `TauCeti.exists_norm_deriv_inv_Gamma_vertical_strip_le`,
  `TauCeti.exists_norm_inv_Gamma_and_deriv_ball_add_I_le`: uniform upper bounds for `‖(Γ s)⁻¹‖`
  and `‖deriv (Γ ·)⁻¹ s‖` across the strip `Re s ∈ [a, b]` and on shifted vertical lines over unit
  balls.
-/

public section

open Complex Real Filter Set Asymptotics

namespace TauCeti

/-- The modulus term: `0 ≤ log ‖σ + i t‖ - log t ≤ |σ| / t` for `t > 0`, since
`t ≤ ‖σ + i t‖ ≤ t + |σ|`. -/
private theorem abs_log_norm_sub_log_im_le {σ t : ℝ} (ht : 0 < t) :
    |Real.log ‖(σ : ℂ) + t * I‖ - Real.log t| ≤ |σ| / t := by
  set s : ℂ := σ + t * I
  have hts : t ≤ ‖s‖ := by simpa [s, abs_of_pos ht] using abs_im_le_norm s
  have hst : ‖s‖ ≤ |σ| + t := by simpa [s, abs_of_pos ht] using norm_le_abs_re_add_abs_im s
  rw [abs_of_nonneg (sub_nonneg.2 (Real.log_le_log ht hts)),
    ← Real.log_div (ht.trans_le hts).ne' ht.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos (ht.trans_le hts) ht)).trans ?_
  rw [div_sub_one ht.ne']
  exact div_le_div_of_nonneg_right (by linarith) ht.le

/-- The angle term: `|t (arctan (σ / t) - σ / t)| ≤ σ ^ 2 / t` for `|σ| ≤ t`, from the cubic
bound `|arctan x - x| ≤ |x| ^ 3` at `|x| ≤ 1`. -/
private theorem abs_mul_arctan_div_sub_div_le {σ t : ℝ} (ht : 0 < t) (hσt : |σ| ≤ t) :
    |t * (Real.arctan (σ / t) - σ / t)| ≤ σ ^ 2 / t := by
  have hx1 : |σ / t| ≤ 1 := by
    rw [abs_div, abs_of_pos ht]
    exact div_le_one_of_le₀ hσt ht.le
  rw [abs_mul, abs_of_pos ht]
  calc t * |Real.arctan (σ / t) - σ / t| ≤ t * |σ / t| ^ 2 :=
        mul_le_mul_of_nonneg_left ((Real.abs_arctan_sub_self_le _).trans
          (pow_le_pow_of_le_one (abs_nonneg _) hx1 (by norm_num))) ht.le
    _ = σ ^ 2 / t := by
      rw [sq_abs]
      field_simp

/-- The explicit vertical bound in the upper half-plane. -/
private theorem abs_log_norm_Gamma_vertical_sub_le_of_pos {σ t : ℝ} (ht : 0 < t)
    (hσt : |σ| ≤ t) :
    |Real.log ‖Complex.Gamma (σ + t * I)‖ -
        ((σ - 1 / 2) * Real.log |t| - π * |t| / 2 + Real.log (2 * π) / 2)| ≤
      (1 / (8 * Real.sin (π / 8) ^ 2) + |σ - 1 / 2| * |σ| + σ ^ 2) / |t| := by
  set s : ℂ := σ + t * I
  set K : ℝ := 1 / (8 * Real.sin (π / 8) ^ 2)
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  rw [abs_of_pos ht]
  have hs0 : s ≠ 0 := fun h ↦ ht.ne' (by rw [← him, h, zero_im])
  have hts : t ≤ ‖s‖ := by simpa [him, abs_of_pos ht] using abs_im_le_norm s
  have hK : 0 ≤ K := by positivity
  -- the angle: `arg s = π / 2 - arctan (σ / t)` with `|arctan (σ / t)| ≤ π / 4`
  have harg := arg_eq_pi_div_two_sub_arctan_of_im_pos (w := s) (by rwa [him])
  rw [hre, him] at harg
  have hatan_le : |Real.arctan (σ / t)| ≤ π / 4 := by
    have hx1 : |σ / t| ≤ 1 := by
      rw [abs_div, abs_of_pos ht]
      exact div_le_one_of_le₀ hσt ht.le
    rw [← Real.arctan_one, abs_le, ← Real.arctan_neg]
    exact ⟨Real.arctan_mono (abs_le.1 hx1).1, Real.arctan_mono (abs_le.1 hx1).2⟩
  have hsector : |s.arg| ≤ π - π / 4 := by
    rw [harg, abs_le]
    obtain ⟨h1, h2⟩ := abs_le.1 hatan_le
    constructor <;> linarith [Real.pi_pos]
  -- Stirling on the sector `|arg s| ≤ 3π/4`
  have hS := abs_log_norm_Gamma_sub_stirling_le (by positivity) hsector hs0
  rw [hre, him, show π / 4 / 2 = π / 8 by ring, ← div_div] at hS
  have hS' : K / ‖s‖ ≤ K / t := div_le_div_of_nonneg_left hK ht hts
  -- the modulus term
  have hA : |(σ - 1 / 2) * (Real.log ‖s‖ - Real.log t)| ≤ |σ - 1 / 2| * |σ| / t := by
    rw [abs_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (abs_log_norm_sub_log_im_le ht) (abs_nonneg _)
  have hsplit : Real.log ‖Complex.Gamma s‖ -
      ((σ - 1 / 2) * Real.log t - π * t / 2 + Real.log (2 * π) / 2) =
      (Real.log ‖Complex.Gamma s‖ - ((σ - 1 / 2) * Real.log ‖s‖ - t * s.arg - σ +
        Real.log (2 * π) / 2)) + (σ - 1 / 2) * (Real.log ‖s‖ - Real.log t) +
      t * (Real.arctan (σ / t) - σ / t) := by
    have hσ : t * (σ / t) = σ := by field_simp
    rw [harg]
    linear_combination hσ
  rw [hsplit, add_div, add_div]
  refine (abs_add_three _ _ _).trans ?_
  linarith [hS.trans hS', abs_mul_arctan_div_sub_div_le ht hσt]

/-- The explicit vertical bound in the coordinates `s = σ + i t`. -/
private theorem abs_log_norm_Gamma_vertical_sub_le_of_ne_zero {σ t : ℝ} (ht : t ≠ 0)
    (hσt : |σ| ≤ |t|) :
    |Real.log ‖Complex.Gamma (σ + t * I)‖ -
        ((σ - 1 / 2) * Real.log |t| - π * |t| / 2 + Real.log (2 * π) / 2)| ≤
      (1 / (8 * Real.sin (π / 8) ^ 2) + |σ - 1 / 2| * |σ| + σ ^ 2) / |t| := by
  rcases ht.lt_or_gt with ht | ht
  · have hpos := abs_log_norm_Gamma_vertical_sub_le_of_pos (σ := σ) (neg_pos.2 ht)
      (by rwa [abs_of_neg ht] at hσt)
    have hconj : (σ : ℂ) + t * I = (starRingEnd ℂ) ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [abs_neg] at hpos
    rwa [hconj, Complex.Gamma_conj, Complex.norm_conj]
  · exact abs_log_norm_Gamma_vertical_sub_le_of_pos ht (by rwa [abs_of_pos ht] at hσt)

/-- **Stirling's formula on vertical strips**, explicit form: for `s = σ + i t` with `t ≠ 0` and
`|σ| ≤ |t|`,
`|log ‖Γ(s)‖ - ((σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2)| ≤
(1 / (8 * sin (π / 8) ^ 2) + |σ - 1/2| |σ| + σ ^ 2) / |t|`. -/
theorem abs_log_norm_Gamma_vertical_sub_le {s : ℂ} (hs : s.im ≠ 0) (hre : |s.re| ≤ |s.im|) :
    |Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2)| ≤
      (1 / (8 * Real.sin (π / 8) ^ 2) + |s.re - 1 / 2| * |s.re| + s.re ^ 2) / |s.im| := by
  simpa only [re_add_im] using abs_log_norm_Gamma_vertical_sub_le_of_ne_zero hs hre

/-- Stirling's formula on vertical strips, with one constant and one threshold for the whole
strip `a ≤ Re s ≤ b`: for `s = σ + i t` with `σ ∈ [a, b]` and `T ≤ |t|`,
`|log ‖Γ(s)‖ - ((σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2)| ≤ C / |t|`. -/
theorem exists_abs_log_norm_Gamma_vertical_sub_le (a b : ℝ) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Complex.Gamma s‖ -
          ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2)| ≤
        C / |s.im| := by
  set M := max |a| |b|
  refine ⟨1 / (8 * Real.sin (π / 8) ^ 2) + (M + 1 / 2) * M + M ^ 2, M + 1,
    fun s hs ht ↦ ?_⟩
  have hσM : |s.re| ≤ M := abs_le_max_abs_abs hs.1 hs.2
  have hM : 0 ≤ M := (abs_nonneg _).trans hσM
  have ht0 : 0 < |s.im| := by linarith
  refine (abs_log_norm_Gamma_vertical_sub_le (abs_pos.1 ht0) (by linarith)).trans ?_
  refine div_le_div_of_nonneg_right ?_ ht0.le
  have h1 : |s.re - 1 / 2| ≤ M + 1 / 2 := by
    obtain ⟨hl, hu⟩ := abs_le.1 hσM
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |s.re - 1 / 2| * |s.re| ≤ (M + 1 / 2) * M :=
    mul_le_mul h1 hσM (abs_nonneg _) (by linarith)
  have h3 : s.re ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hσM 2
  linarith

/-- Stirling's formula on vertical strips for a shifted argument, measured against `log |t|`:
for every compact interval `[a, b]` and every shift `μ`, there are `C` and `X` such that
`|log ‖Γ(s + μ)‖ - ((σ + Re μ - 1/2) log |t| - π |t| / 2)| ≤ C` for `s = σ + i t` with
`σ ∈ [a, b]` and `X ≤ |t|`. The constant `log (2π) / 2` and the effect of the shift on
`log |t|` and `|t|` are absorbed into `C`; this is the form in which the estimate adds up over
the shifted factors of an archimedean gamma factor. -/
theorem exists_abs_log_norm_Gamma_add_vertical_sub_le (a b : ℝ) (μ : ℂ) :
    ∃ C X : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → X ≤ |s.im| →
      |Real.log ‖Complex.Gamma (s + μ)‖ -
          ((s.re + μ.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2)| ≤ C := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le (a + μ.re) (b + μ.re)
  set M := max |a| |b|
  refine ⟨|C| + (M + |μ.re| + 1 / 2) + π * |μ.im| / 2 + |Real.log (2 * π) / 2|,
    2 * (max T 1 + |μ.im|), fun s hs ht ↦ ?_⟩
  set τ := s.im with hτ_def
  set v := τ + μ.im with hv_def
  have hT1 : 1 ≤ max T 1 := le_max_right _ _
  have hvτ : |v - τ| ≤ |μ.im| := by simp [v]
  have hvabs := abs_abs_sub_abs_le_abs_sub v τ
  have hv : max T 1 ≤ |v| := by linarith [abs_le.1 (hvabs.trans hvτ)]
  have hv0 : 0 < |v| := by linarith
  have hτ0 : 0 < |τ| := by linarith [abs_nonneg μ.im]
  -- Stirling at `s + μ`, whose imaginary part is `v`.
  have hE := h (s + μ) (by simpa [add_re] using ⟨hs.1, hs.2⟩)
    (by simpa [add_im, v] using (le_max_left T 1).trans hv)
  simp only [add_re, add_im] at hE
  rw [← hτ_def, ← hv_def] at hE
  have hCv : C / |v| ≤ |C| :=
    (div_le_div_of_nonneg_right (le_abs_self C) hv0.le).trans
      (div_le_self (abs_nonneg C) (hT1.trans hv))
  -- The comparison `|log |v| - log |τ|| ≤ 1`, since `|τ| / 2 ≤ |v| ≤ 2 |τ|`.
  have hlog : |Real.log (|v|) - Real.log (|τ|)| ≤ 1 :=
    (Real.abs_log_sub_log_le_log hv0 hτ0 (c := 2) (by linarith [abs_le.1 hvabs])
      (by linarith [abs_le.1 hvabs])).trans (Real.log_two_lt_d9.le.trans (by norm_num))
  have hcoef : |s.re + μ.re - 1 / 2| ≤ M + |μ.re| + 1 / 2 := by
    have hσμ : |s.re + μ.re| ≤ M + |μ.re| :=
      (abs_add_le _ _).trans (by gcongr; exact abs_le_max_abs_abs hs.1 hs.2)
    exact abs_le.2 ⟨by linarith [abs_le.1 hσμ], by linarith [abs_le.1 hσμ]⟩
  have hprod :
      |(s.re + μ.re - 1 / 2) * (Real.log (|v|) - Real.log (|τ|))| ≤ M + |μ.re| + 1 / 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (s.re + μ.re - 1 / 2), abs_nonneg (Real.log (|v|) - Real.log (|τ|))]
  have hdist : |π * (|v| - |τ|) / 2| ≤ π * |μ.im| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos pi_pos, abs_two]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hvabs.trans hvτ) pi_pos.le) two_pos.le
  have key : Real.log ‖Complex.Gamma (s + μ)‖ -
        ((s.re + μ.re - 1 / 2) * Real.log |τ| - π * |τ| / 2) =
      (Real.log ‖Complex.Gamma (s + μ)‖ -
          ((s.re + μ.re - 1 / 2) * Real.log |v| - π * |v| / 2 + Real.log (2 * π) / 2)) +
        (s.re + μ.re - 1 / 2) * (Real.log |v| - Real.log |τ|) - π * (|v| - |τ|) / 2 +
        Real.log (2 * π) / 2 := by ring
  rw [key]
  have e1 := abs_le.1 (hE.trans hCv)
  have e2 := abs_le.1 hprod
  have e3 := abs_le.1 hdist
  exact abs_le.2 ⟨by linarith [neg_abs_le (Real.log (2 * π) / 2)],
    by linarith [le_abs_self (Real.log (2 * π) / 2)]⟩

/-- **Stirling's formula on vertical strips** ([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9)):
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)` uniformly for
`σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gamma_vertical_sub (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖Complex.Gamma (p.1 + p.2 * I)‖ -
        ((p.1 - 1 / 2) * Real.log |p.2| - π * |p.2| / 2 + Real.log (2 * π) / 2))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun p ↦ |p.2|⁻¹ := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  refine isBigO_inv_vertical_of_exists ⟨C, T, fun p hσ ht ↦ ?_⟩
  simpa using h (p.1 + p.2 * I) (by simpa using hσ) (by simpa using ht)

/-- **Stirling's formula on vertical strips** as a function of `s = σ + i t`:
`log ‖Γ(s)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)` as `s → ∞` in the strip
`a ≤ Re s ≤ b`. -/
theorem isBigO_log_norm_Gamma_vertical_strip_sub (a b : ℝ) :
    (fun s : ℂ ↦ Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2))
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun s ↦ |s.im|⁻¹ := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  exact isBigO_inv_vertical_strip_of_exists (Metric.isBounded_Icc a b)
    ⟨C, T, fun s hs ht ↦ by simpa using h s hs ht⟩

/-- Stirling's formula on a single vertical line `Re s = σ`:
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gamma_vertical_line_sub (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gamma (σ + t * I)‖ -
        ((σ - 1 / 2) * Real.log |t| - π * |t| / 2 + Real.log (2 * π) / 2))
      =O[cocompact ℝ] fun t ↦ |t|⁻¹ :=
  (isBigO_log_norm_Gamma_vertical_sub σ σ).fiberwise_right (left_mem_Icc.2 le_rfl)

/-- Continuity of the Stirling comparison weight `(1 + |Im z|) ^ (p z) * exp (q z)`. -/
private lemma continuous_stirlingWeight {p q : ℂ → ℝ} (hp : Continuous p) (hq : Continuous q) :
    Continuous fun z : ℂ ↦ (((1 + |z.im|) ^ p z * Real.exp (q z) : ℝ) : ℂ) :=
  continuous_ofReal.comp <|
    ((continuous_const.add (continuous_abs.comp continuous_im)).rpow hp fun z ↦
      Or.inl (add_pos_of_pos_of_nonneg one_pos (abs_nonneg z.im)).ne').mul
      (Real.continuous_exp.comp hq)

/-- Uniform upper bound for `‖Γ(s)‖` on a vertical strip `a ≤ Re s ≤ b` away from the real axis:
for every `δ > 0`, `‖Γ(s)‖ ≤ C (1 + |Im s|) ^ (Re s - 1/2) exp (-π |Im s| / 2)` for all `s` with
`Re s ∈ [a, b]` and `δ ≤ |Im s|`. -/
theorem exists_norm_Gamma_vertical_strip_le (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b → δ ≤ |s.im| →
      ‖Complex.Gamma s‖ ≤ C * (1 + |s.im|) ^ (s.re - 1 / 2) * Real.exp (-(π * |s.im| / 2)) := by
  obtain ⟨C₀, T₀, hS⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  set T : ℝ := max (max T₀ 1) δ
  have hT1 : 1 ≤ T := (le_max_right T₀ 1).trans (le_max_left _ δ)
  let w : ℂ → ℝ := fun s ↦ (1 + |s.im|) ^ (s.re - 1 / 2) * Real.exp (-(π * |s.im| / 2))
  have hw_pos (s : ℂ) : 0 < w s := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  -- Compactness handles the bounded band `δ ≤ |Im s| ≤ T`.
  let K : Set ℂ := ((fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * I) '' (Icc a b ×ˢ Icc (-T) T)) ∩
    {s : ℂ | δ ≤ |s.im|}
  have hK : IsCompact K := ((isCompact_Icc.prod isCompact_Icc).image (by fun_prop)).inter_right
    (isClosed_le continuous_const (continuous_abs.comp continuous_im))
  have hw_cont : Continuous fun z : ℂ ↦ (w z : ℂ) :=
    continuous_stirlingWeight (by fun_prop) (by fun_prop)
  have hcont : ContinuousOn (fun s : ℂ ↦ Complex.Gamma s / (w s : ℂ)) K := fun s hs ↦ by
    have him0 : s.im ≠ 0 := abs_pos.mp (hδ.trans_le hs.2)
    have hΓ : ContinuousAt Complex.Gamma s :=
      Complex.continuousAt_Gamma s fun m hm ↦ him0 (by simp [hm])
    exact (hΓ.div hw_cont.continuousAt (ofReal_ne_zero.mpr (hw_pos s).ne')).continuousWithinAt
  obtain ⟨C_mid, hC_mid⟩ := hK.exists_bound_of_continuousOn hcont
  -- Stirling's vertical-strip formula handles the tail `|Im s| > T`.
  set M_exp : ℝ := max |a - 1 / 2| |b - 1 / 2|
  set C₁ : ℝ := Real.exp (M_exp * Real.log 2 + Real.log (2 * π) / 2 + |C₀|)
  refine ⟨max (max C₁ C_mid) 1, by positivity, fun s hs him ↦ ?_⟩
  rcases le_or_gt |s.im| T with hle | hgt
  · have hsK : s ∈ K := ⟨⟨(s.re, s.im), ⟨hs, abs_le.mp hle⟩, re_add_im s⟩, him⟩
    have hbnd := hC_mid s hsK
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hw_pos s).le,
      div_le_iff₀ (hw_pos s)] at hbnd
    simpa only [w, mul_assoc] using hbnd.trans <| mul_le_mul_of_nonneg_right
      ((le_max_right C₁ C_mid).trans (le_max_left _ 1)) (hw_pos s).le
  · have ht1 : 1 ≤ |s.im| := hT1.trans hgt.le
    have him0 : s.im ≠ 0 := abs_pos.mp (zero_lt_one.trans_le ht1)
    have hΓ0 : 0 < ‖Complex.Gamma s‖ :=
      norm_pos_iff.mpr (Complex.Gamma_ne_zero fun m hm ↦ him0 (by simp [hm]))
    have hlog :=
      (abs_le.mp (hS s hs ((le_max_left T₀ 1).trans (le_max_left _ δ) |>.trans hgt.le))).2
    have herr : C₀ / |s.im| ≤ |C₀| :=
      (div_le_div_of_nonneg_right (le_abs_self C₀) (by positivity)).trans
        (div_le_self (abs_nonneg C₀) ht1)
    have hp_le : |s.re - 1 / 2| * Real.log 2 ≤ M_exp * Real.log 2 :=
      mul_le_mul_of_nonneg_right
        (abs_le_max_abs_abs (by linarith [hs.1]) (by linarith [hs.2]))
        (Real.log_nonneg one_le_two)
    have hexp_le : Real.log ‖Complex.Gamma s‖ ≤
        (M_exp * Real.log 2 + Real.log (2 * π) / 2 + |C₀|) +
          (s.re - 1 / 2) * Real.log (1 + |s.im|) + (-(π * |s.im| / 2)) := by
      linarith [Real.mul_log_le_mul_log_one_add (s.re - 1 / 2) ht1]
    calc ‖Complex.Gamma s‖ = Real.exp (Real.log ‖Complex.Gamma s‖) := (Real.exp_log hΓ0).symm
      _ ≤ Real.exp ((M_exp * Real.log 2 + Real.log (2 * π) / 2 + |C₀|) +
            (s.re - 1 / 2) * Real.log (1 + |s.im|) + (-(π * |s.im| / 2))) :=
          Real.exp_le_exp.mpr hexp_le
      _ = C₁ * (1 + |s.im|) ^ (s.re - 1 / 2) * Real.exp (-(π * |s.im| / 2)) := by
          rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos (by positivity),
            mul_comm (Real.log _)]
      _ ≤ max (max C₁ C_mid) 1 * (1 + |s.im|) ^ (s.re - 1 / 2) * Real.exp (-(π * |s.im| / 2)) := by
          gcongr
          exact (le_max_left C₁ C_mid).trans (le_max_left _ 1)

/-- Uniform upper bound for `‖Γ(σ + i t)‖` on any vertical line `Re s = σ` avoiding the poles of
`Γ`: `‖Γ(σ + i t)‖ ≤ C (1 + |t|) ^ (σ - 1/2) exp (-π |t| / 2)` for all `t : ℝ`. -/
theorem exists_norm_Gamma_vertical_line_le {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) :
    ∃ C > 0, ∀ t : ℝ,
      ‖Complex.Gamma (σ + t * I)‖ ≤ C * (1 + |t|) ^ (σ - 1 / 2) * Real.exp (-(π * |t| / 2)) := by
  obtain ⟨C₁, hC₁, htail⟩ := exists_norm_Gamma_vertical_strip_le σ σ zero_lt_one
  let w : ℝ → ℝ := fun t ↦ (1 + |t|) ^ (σ - 1 / 2) * Real.exp (-(π * |t| / 2))
  have hw_pos (t : ℝ) : 0 < w t := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  have hw_cont : Continuous fun u : ℝ ↦ (w u : ℂ) := by
    simpa [w, Function.comp_def, Complex.ofReal_exp] using
      (continuous_stirlingWeight (p := fun _ ↦ σ - 1 / 2) continuous_const
        (by fun_prop : Continuous fun z : ℂ ↦ -(π * |z.im| / 2))).comp
        (by fun_prop : Continuous fun u : ℝ ↦ (σ : ℂ) + u * I)
  have hcont : ContinuousOn (fun t : ℝ ↦ Complex.Gamma (σ + t * I) / (w t : ℂ)) (Icc (-1) 1) :=
    fun t _ ↦ ((Complex.continuous_Gamma_add_mul_I (by simpa using hσ)).continuousAt.div
      hw_cont.continuousAt (ofReal_ne_zero.mpr (hw_pos t).ne')).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), fun t ↦ ?_⟩
  rcases le_or_gt |t| 1 with ht | ht
  · have hbnd := hC₂ t (abs_le.mp ht)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hw_pos t).le,
      div_le_iff₀ (hw_pos t)] at hbnd
    simpa only [w, mul_assoc] using hbnd.trans
      (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (hw_pos t).le)
  · have hbnd := htail (σ + t * I) (by simp) (by simpa using ht.le)
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, add_im, ofReal_im,
      mul_I_im, zero_add] at hbnd
    exact hbnd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (by positivity)) (Real.exp_pos _).le)

/-- Shifted vertical-line Stirling bound: if `Re w` is not a nonpositive integer, then
`‖Γ(w + i y)‖ ≤ C (1 + |y|) ^ (Re w - 1/2) exp (-π |y| / 2)` for all `y : ℝ`. -/
theorem exists_norm_Gamma_add_I_le {w : ℂ} (hw : ∀ n : ℕ, w.re ≠ -n) :
    ∃ C > 0, ∀ y : ℝ,
      ‖Complex.Gamma (w + y * I)‖ ≤
        C * (1 + |y|) ^ (w.re - 1 / 2) * Real.exp (-(π * |y| / 2)) := by
  obtain ⟨C₀, hC₀, hbnd⟩ := exists_norm_Gamma_vertical_line_le hw
  set p : ℝ := w.re - 1 / 2
  refine ⟨C₀ * (1 + |w.im|) ^ |p| * Real.exp (π * |w.im| / 2), by positivity, fun y ↦ ?_⟩
  have hw_eq : w + y * I = (w.re : ℂ) + ↑(w.im + y) * I := by
    apply Complex.ext <;> simp
  have h0 := hbnd (w.im + y)
  rw [← hw_eq] at h0
  have hrpow : (1 + |w.im + y|) ^ p ≤ (1 + |w.im|) ^ |p| * (1 + |y|) ^ p := by
    simpa only [Real.norm_eq_abs] using one_add_norm_add_rpow_le_mul p w.im y
  have hexp : Real.exp (-(π * |w.im + y| / 2)) ≤
      Real.exp (π * |w.im| / 2) * Real.exp (-(π * |y| / 2)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hsub : |y| ≤ |w.im| + |w.im + y| := by
      simpa using abs_add_le (-w.im) (w.im + y)
    nlinarith [Real.pi_pos]
  calc ‖Complex.Gamma (w + y * I)‖
      ≤ C₀ * (1 + |w.im + y|) ^ p * Real.exp (-(π * |w.im + y| / 2)) := h0
    _ ≤ C₀ * ((1 + |w.im|) ^ |p| * (1 + |y|) ^ p) *
          (Real.exp (π * |w.im| / 2) * Real.exp (-(π * |y| / 2))) := by gcongr
    _ = C₀ * (1 + |w.im|) ^ |p| * Real.exp (π * |w.im| / 2) *
          (1 + |y|) ^ p * Real.exp (-(π * |y| / 2)) := by ring

/-- Reflected shifted vertical-line Stirling bound: if `Re w` is not a nonpositive integer, then
`‖Γ(w - i y)‖ ≤ C (1 + |y|) ^ (Re w - 1/2) exp (-π |y| / 2)` for all `y : ℝ`. -/
theorem exists_norm_Gamma_sub_I_le {w : ℂ} (hw : ∀ n : ℕ, w.re ≠ -n) :
    ∃ C > 0, ∀ y : ℝ,
      ‖Complex.Gamma (w - y * I)‖ ≤
        C * (1 + |y|) ^ (w.re - 1 / 2) * Real.exp (-(π * |y| / 2)) := by
  obtain ⟨C, hC, hbnd⟩ := exists_norm_Gamma_add_I_le hw
  exact ⟨C, hC, fun y ↦ by simpa [sub_eq_add_neg] using hbnd (-y)⟩

/-- Uniform upper bound for the reciprocal Gamma function across an entire vertical strip
`a ≤ Re s ≤ b` (including at poles, where `(Γ s)⁻¹ = 0`):
`‖(Γ s)⁻¹‖ ≤ C (1 + |Im s|) ^ (1/2 - Re s) exp (π |Im s| / 2)`. -/
theorem exists_norm_inv_Gamma_vertical_strip_le (a b : ℝ) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by
  obtain ⟨C₀, T₀, hS⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  set T : ℝ := max T₀ 1
  have hT1 : 1 ≤ T := le_max_right T₀ 1
  let w : ℂ → ℝ := fun s ↦ (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2)
  have hw_pos (s : ℂ) : 0 < w s := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  -- Compactness of `[a, b] × [-T, T]` bounds the entire function `Γ⁻¹` near the real axis.
  let K : Set ℂ := (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * I) '' (Icc a b ×ˢ Icc (-T) T)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hw_cont : Continuous fun z : ℂ ↦ (w z : ℂ) :=
    continuous_stirlingWeight (by fun_prop) (by fun_prop)
  have hcont : ContinuousOn (fun s : ℂ ↦ (Complex.Gamma s)⁻¹ / (w s : ℂ)) K := fun s _ ↦
    (Complex.differentiable_one_div_Gamma.continuous.continuousAt.div hw_cont.continuousAt
      (ofReal_ne_zero.mpr (hw_pos s).ne')).continuousWithinAt
  obtain ⟨C_mid, hC_mid⟩ := hK.exists_bound_of_continuousOn hcont
  -- Stirling's vertical-strip lower bound on `log ‖Γ s‖` handles `|Im s| > T`.
  set M_exp : ℝ := max |1 / 2 - b| |1 / 2 - a|
  set C₁ : ℝ := Real.exp (M_exp * Real.log 2 - Real.log (2 * π) / 2 + |C₀|)
  refine ⟨max (max C₁ C_mid) 1, by positivity, fun s hs ↦ ?_⟩
  rcases le_or_gt |s.im| T with hle | hgt
  · have hsK : s ∈ K := ⟨(s.re, s.im), ⟨hs, abs_le.mp hle⟩, re_add_im s⟩
    have hbnd := hC_mid s hsK
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hw_pos s).le,
      div_le_iff₀ (hw_pos s)] at hbnd
    simpa only [w, mul_assoc] using hbnd.trans <| mul_le_mul_of_nonneg_right
      ((le_max_right C₁ C_mid).trans (le_max_left _ 1)) (hw_pos s).le
  · have ht1 : 1 ≤ |s.im| := hT1.trans hgt.le
    have him0 : s.im ≠ 0 := abs_pos.mp (zero_lt_one.trans_le ht1)
    have hΓ0 : 0 < ‖Complex.Gamma s‖ :=
      norm_pos_iff.mpr (Complex.Gamma_ne_zero fun m hm ↦ him0 (by simp [hm]))
    have hlog := (abs_le.mp (hS s hs ((le_max_left T₀ 1).trans hgt.le))).1
    have herr : C₀ / |s.im| ≤ |C₀| :=
      (div_le_div_of_nonneg_right (le_abs_self C₀) (by positivity)).trans
        (div_le_self (abs_nonneg C₀) ht1)
    have hp_le : |1 / 2 - s.re| * Real.log 2 ≤ M_exp * Real.log 2 :=
      mul_le_mul_of_nonneg_right
        (abs_le_max_abs_abs (by linarith [hs.2]) (by linarith [hs.1]))
        (Real.log_nonneg one_le_two)
    have hexp_le : -Real.log ‖Complex.Gamma s‖ ≤
        (M_exp * Real.log 2 - Real.log (2 * π) / 2 + |C₀|) +
          (1 / 2 - s.re) * Real.log (1 + |s.im|) + π * |s.im| / 2 := by
      linarith [Real.mul_log_le_mul_log_one_add (1 / 2 - s.re) ht1]
    calc ‖(Complex.Gamma s)⁻¹‖
        = Real.exp (-Real.log ‖Complex.Gamma s‖) := by
            rw [norm_inv, Real.exp_neg, Real.exp_log hΓ0]
      _ ≤ Real.exp ((M_exp * Real.log 2 - Real.log (2 * π) / 2 + |C₀|) +
            (1 / 2 - s.re) * Real.log (1 + |s.im|) + π * |s.im| / 2) :=
          Real.exp_le_exp.mpr hexp_le
      _ = C₁ * (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by
          rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos (by positivity),
            mul_comm (Real.log _)]
      _ ≤ max (max C₁ C_mid) 1 * (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by
          gcongr
          exact (le_max_left C₁ C_mid).trans (le_max_left _ 1)

/-- Comparison of the polynomial factors in the shifted strip bounds: for `s = w + (x + i T)`,
`e ≤ K` and `0 ≤ K`, `(1 + |Im s|) ^ e ≤ (1 + |Im w|) ^ K (1 + |T|) ^ K`. -/
private theorem one_add_abs_im_add_rpow_le (w : ℂ) (x T : ℝ) {e K : ℝ} (he : e ≤ K)
    (hK : 0 ≤ K) :
    (1 + |(w + (x + T * I)).im|) ^ e ≤ (1 + |w.im|) ^ K * (1 + |T|) ^ K := by
  have hup : |(w + (x + T * I)).im| ≤ |w.im| + |T| := by simpa using abs_add_le w.im T
  calc (1 + |(w + (x + T * I)).im|) ^ e ≤ (1 + |(w + (x + T * I)).im|) ^ K :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (w + (x + T * I)).im]) he
    _ ≤ ((1 + |w.im|) * (1 + |T|)) ^ K :=
        Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg T, abs_nonneg w.im]) hK
    _ = (1 + |w.im|) ^ K * (1 + |T|) ^ K := Real.mul_rpow (by positivity) (by positivity)

/-- Comparison of the growing exponential factors in the shifted strip bounds: for
`s = w + (x + i T)`, `exp (π |Im s| / 2) ≤ exp (π |Im w| / 2) exp (π |T| / 2)`. -/
private theorem exp_abs_im_add_le (w : ℂ) (x T : ℝ) :
    Real.exp (π * |(w + (x + T * I)).im| / 2) ≤
      Real.exp (π * |w.im| / 2) * Real.exp (π * |T| / 2) := by
  have hup : |(w + (x + T * I)).im| ≤ |w.im| + |T| := by simpa using abs_add_le w.im T
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])

/-- For `s = w + (x + i T)`, `|T| - |Im w| ≤ |Im s|`. -/
private theorem abs_sub_abs_im_le_abs_im_add (w : ℂ) (x T : ℝ) :
    |T| - |w.im| ≤ |(w + (x + T * I)).im| := by
  have := abs_sub_abs_le_abs_sub T (-w.im)
  rw [abs_neg, sub_neg_eq_add, add_comm] at this
  simpa using this

/-- Comparison of the decaying exponential factors in the shifted strip bounds: for
`s = w + (x + i T)`, `exp (-π |Im s| / 2) ≤ exp (π |Im w| / 2) exp (-π |T| / 2)`. -/
private theorem exp_neg_abs_im_add_le (w : ℂ) (x T : ℝ) :
    Real.exp (-(π * |(w + (x + T * I)).im| / 2)) ≤
      Real.exp (π * |w.im| / 2) * Real.exp (-(π * |T| / 2)) := by
  have hlow := abs_sub_abs_im_le_abs_im_add w x T
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])

/-- Shifted Stirling bound on a vertical strip, uniform in the real part: for `w : ℂ` and
`A ≤ x ≤ B`, `‖Γ(w + x + i T)‖ ≤ C (1 + |T|) ^ K exp (-π |T| / 2)` once `|T| ≥ T₀`. -/
theorem exists_norm_Gamma_add_vertical_strip_le (w : ℂ) (A B : ℝ) :
    ∃ C ≥ 0, ∃ K T₀ : ℝ, ∀ x ∈ Icc A B, ∀ T : ℝ, T₀ ≤ |T| →
      ‖Complex.Gamma (w + (x + T * I))‖ ≤ C * (1 + |T|) ^ K * Real.exp (-(π * |T| / 2)) := by
  obtain ⟨C₀, hC₀, h⟩ :=
    exists_norm_Gamma_vertical_strip_le (w.re + A) (w.re + B) one_pos
  set m := |w.im|
  set K := max (w.re + B - 1 / 2) 0
  refine ⟨C₀ * (1 + m) ^ K * Real.exp (π * m / 2), by positivity, K, m + 1,
    fun x hx T hT ↦ ?_⟩
  set s : ℂ := w + (x + T * I)
  have hre : s.re = w.re + x := by simp [s]
  have hlow : |T| - m ≤ |s.im| := abs_sub_abs_im_le_abs_im_add w x T
  calc ‖Complex.Gamma s‖ ≤ C₀ * (1 + |s.im|) ^ (s.re - 1 / 2) * Real.exp (-(π * |s.im| / 2)) :=
        h s (by rw [hre]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩) (by linarith)
    _ ≤ C₀ * ((1 + m) ^ K * (1 + |T|) ^ K) *
          (Real.exp (π * m / 2) * Real.exp (-(π * |T| / 2))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (one_add_abs_im_add_rpow_le w x T
            (le_max_of_le_left (by rw [hre]; linarith [hx.2])) (le_max_right _ _)) hC₀.le)
          (exp_neg_abs_im_add_le w x T) (by positivity) (by positivity)
    _ = C₀ * (1 + m) ^ K * Real.exp (π * m / 2) * (1 + |T|) ^ K *
          Real.exp (-(π * |T| / 2)) := by ring

/-- Shifted Stirling bound for the reciprocal Gamma function on a vertical strip, uniform in the
real part: for `w : ℂ` and `A ≤ x ≤ B`, `‖Γ(w + x + i T)⁻¹‖ ≤ C (1 + |T|) ^ K exp (π |T| / 2)`. -/
theorem exists_norm_inv_Gamma_add_vertical_strip_le (w : ℂ) (A B : ℝ) :
    ∃ C ≥ 0, ∃ K : ℝ, ∀ x ∈ Icc A B, ∀ T : ℝ,
      ‖(Complex.Gamma (w + (x + T * I)))⁻¹‖ ≤ C * (1 + |T|) ^ K * Real.exp (π * |T| / 2) := by
  obtain ⟨C₀, hC₀, h⟩ := exists_norm_inv_Gamma_vertical_strip_le (w.re + A) (w.re + B)
  set m := |w.im|
  set K := max (1 / 2 - w.re - A) 0
  refine ⟨C₀ * (1 + m) ^ K * Real.exp (π * m / 2), by positivity, K, fun x hx T ↦ ?_⟩
  set s : ℂ := w + (x + T * I)
  have hre : s.re = w.re + x := by simp [s]
  calc ‖(Complex.Gamma s)⁻¹‖ ≤ C₀ * (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) :=
        h s (by rw [hre]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    _ ≤ C₀ * ((1 + m) ^ K * (1 + |T|) ^ K) *
          (Real.exp (π * m / 2) * Real.exp (π * |T| / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (one_add_abs_im_add_rpow_le w x T
            (le_max_of_le_left (by rw [hre]; linarith [hx.1])) (le_max_right _ _)) hC₀.le)
          (exp_abs_im_add_le w x T) (by positivity) (by positivity)
    _ = C₀ * (1 + m) ^ K * Real.exp (π * m / 2) * (1 + |T|) ^ K *
          Real.exp (π * |T| / 2) := by ring

/-- Uniform upper bound for the derivative of the entire function `z ↦ (Γ z)⁻¹` across a vertical
strip `a ≤ Re s ≤ b`:
`‖deriv (Γ ·)⁻¹ s‖ ≤ C (1 + |Im s|) ^ (3/2 - Re s) exp (π |Im s| / 2)`. -/
theorem exists_norm_deriv_inv_Gamma_vertical_strip_le (a b : ℝ) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖deriv (fun z : ℂ ↦ (Complex.Gamma z)⁻¹) s‖ ≤
        C * (1 + |s.im|) ^ (3 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by
  obtain ⟨C₀, hC₀, hbnd⟩ := exists_norm_inv_Gamma_vertical_strip_le (a - 1) (b + 1)
  set M_exp : ℝ := max |3 / 2 - b| |3 / 2 - a|
  refine ⟨C₀ * 2 ^ M_exp * Real.exp (π / 2), by positivity, fun s hs ↦ ?_⟩
  have hdiff : DiffContOnCl ℂ (fun z : ℂ ↦ (Complex.Gamma z)⁻¹) (Metric.ball s 1) :=
    Complex.differentiable_one_div_Gamma.diffContOnCl
  have hsphere : ∀ z ∈ Metric.sphere s 1, ‖(Complex.Gamma z)⁻¹‖ ≤
      C₀ * 2 ^ M_exp * Real.exp (π / 2) * (1 + |s.im|) ^ (3 / 2 - s.re) *
        Real.exp (π * |s.im| / 2) := by
    intro z hz
    have hzs : ‖z - s‖ = 1 := mem_sphere_iff_norm.mp hz
    have hre_diff : |z.re - s.re| ≤ 1 := by
      simpa only [← sub_re, hzs] using abs_re_le_norm (z - s)
    have him_diff : ‖z.im - s.im‖ ≤ 1 := by
      simpa only [Real.norm_eq_abs, ← sub_im, hzs] using abs_im_le_norm (z - s)
    have hz_re : z.re ∈ Icc (a - 1) (b + 1) := by
      obtain ⟨h1, h2⟩ := abs_le.mp hre_diff
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hrpow_z : (1 + |z.im|) ^ (1 / 2 - z.re) ≤ (1 + |z.im|) ^ (3 / 2 - s.re) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im])
        (by linarith [(abs_le.mp hre_diff).1])
    have hrpow_shift : (1 + |z.im|) ^ (3 / 2 - s.re) ≤
        2 ^ M_exp * (1 + |s.im|) ^ (3 / 2 - s.re) := by
      have h1 := one_add_norm_rpow_le_two_rpow_abs_mul_of_norm_sub_le_one (3 / 2 - s.re) him_diff
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at h1
      exact h1.trans <| mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le one_le_two
          (abs_le_max_abs_abs (by linarith [hs.2]) (by linarith [hs.1])))
        (by positivity)
    have hexp : Real.exp (π * |z.im| / 2) ≤ Real.exp (π / 2) * Real.exp (π * |s.im| / 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hz_im : |z.im| ≤ 1 + |s.im| := by
        have := abs_sub_abs_le_abs_sub z.im s.im
        rw [Real.norm_eq_abs] at him_diff
        linarith [(abs_le.mp him_diff).2]
      nlinarith [Real.pi_pos]
    calc ‖(Complex.Gamma z)⁻¹‖
        ≤ C₀ * (1 + |z.im|) ^ (1 / 2 - z.re) * Real.exp (π * |z.im| / 2) := hbnd z hz_re
      _ ≤ C₀ * (2 ^ M_exp * (1 + |s.im|) ^ (3 / 2 - s.re)) *
            (Real.exp (π / 2) * Real.exp (π * |s.im| / 2)) := by
          gcongr
          exact hrpow_z.trans hrpow_shift
      _ = C₀ * 2 ^ M_exp * Real.exp (π / 2) * (1 + |s.im|) ^ (3 / 2 - s.re) *
            Real.exp (π * |s.im| / 2) := by ring
  simpa only [div_one] using
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le zero_lt_one hdiff hsphere

/-- Uniform vertical-line bounds on `‖(Γ(w + i y))⁻¹‖` and `‖deriv (Γ ·)⁻¹ (w + i y)‖` for `w` in
the open unit ball around `w₀`. -/
theorem exists_norm_inv_Gamma_and_deriv_ball_add_I_le (w₀ : ℂ) :
    ∃ C > 0, ∀ w ∈ Metric.ball w₀ 1, ∀ y : ℝ,
      ‖(Complex.Gamma (w + y * I))⁻¹‖ ≤
        C * (1 + |y|) ^ (3 / 2 - w₀.re) * Real.exp (π * |y| / 2) ∧
      ‖deriv (fun z : ℂ ↦ (Complex.Gamma z)⁻¹) (w + y * I)‖ ≤
        C * (1 + |y|) ^ (5 / 2 - w₀.re) * Real.exp (π * |y| / 2) := by
  obtain ⟨Ci, hCi, hbi⟩ := exists_norm_inv_Gamma_vertical_strip_le (w₀.re - 1) (w₀.re + 1)
  obtain ⟨Cd, hCd, hbd⟩ := exists_norm_deriv_inv_Gamma_vertical_strip_le (w₀.re - 1) (w₀.re + 1)
  let C_im (q : ℝ) : ℝ := (1 + (|w₀.im| + 1)) ^ |q| * Real.exp (π * (|w₀.im| + 1) / 2)
  have hC_im_pos (q : ℝ) : 0 < C_im q := by positivity
  have hshift (q : ℝ) {w : ℂ} (him_le : |w.im| ≤ |w₀.im| + 1) (y : ℝ) :
      (1 + |(w + y * I).im|) ^ q * Real.exp (π * |(w + y * I).im| / 2) ≤
        C_im q * (1 + |y|) ^ q * Real.exp (π * |y| / 2) := by
    have him_eq : (w + y * I).im = w.im + y := by simp
    rw [him_eq]
    have hrp : (1 + |w.im + y|) ^ q ≤ (1 + |w.im|) ^ |q| * (1 + |y|) ^ q := by
      simpa only [Real.norm_eq_abs] using one_add_norm_add_rpow_le_mul q w.im y
    have hrp2 : (1 + |w.im|) ^ |q| ≤ (1 + (|w₀.im| + 1)) ^ |q| :=
      Real.rpow_le_rpow (by positivity) (by linarith) (abs_nonneg q)
    have hexp : Real.exp (π * |w.im + y| / 2) ≤
        Real.exp (π * (|w₀.im| + 1) / 2) * Real.exp (π * |y| / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by have := abs_add_le w.im y; nlinarith [Real.pi_pos])
    calc (1 + |w.im + y|) ^ q * Real.exp (π * |w.im + y| / 2)
        ≤ ((1 + (|w₀.im| + 1)) ^ |q| * (1 + |y|) ^ q) *
            (Real.exp (π * (|w₀.im| + 1) / 2) * Real.exp (π * |y| / 2)) :=
          mul_le_mul (hrp.trans (mul_le_mul_of_nonneg_right hrp2 (by positivity))) hexp
            (Real.exp_pos _).le (by positivity)
      _ = C_im q * (1 + |y|) ^ q * Real.exp (π * |y| / 2) := by dsimp [C_im]; ring
  set C : ℝ := max (Ci * C_im (3 / 2 - w₀.re)) (Cd * C_im (5 / 2 - w₀.re))
  have hC : 0 < C := lt_of_lt_of_le (mul_pos hCi (hC_im_pos _)) (le_max_left _ _)
  refine ⟨C, hC, fun w hw y ↦ ?_⟩
  have hww : ‖w - w₀‖ < 1 := mem_ball_iff_norm.mp hw
  have hre_diff : |w.re - w₀.re| ≤ 1 := by
    simpa [sub_re] using (abs_re_le_norm (w - w₀)).trans hww.le
  have hre_mem : (w + y * I).re ∈ Icc (w₀.re - 1) (w₀.re + 1) := by
    obtain ⟨h1, h2⟩ := abs_le.mp hre_diff
    simp only [add_re, mul_I_re, ofReal_im, neg_zero, add_zero, mem_Icc]
    exact ⟨by linarith, by linarith⟩
  have him_le : |w.im| ≤ |w₀.im| + 1 := by
    have him : |w.im - w₀.im| ≤ 1 := by
      simpa [sub_im] using (abs_im_le_norm (w - w₀)).trans hww.le
    linarith [abs_sub_abs_le_abs_sub w.im w₀.im, (abs_le.mp him).2]
  refine ⟨?_, ?_⟩
  · have hrp_up : (1 + |(w + y * I).im|) ^ (1 / 2 - (w + y * I).re) ≤
        (1 + |(w + y * I).im|) ^ (3 / 2 - w₀.re) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (w + y * I).im])
        (by simp; linarith [(abs_le.mp hre_diff).1])
    calc ‖(Complex.Gamma (w + y * I))⁻¹‖
        ≤ Ci * ((1 + |(w + y * I).im|) ^ (3 / 2 - w₀.re) *
            Real.exp (π * |(w + y * I).im| / 2)) := by
            refine (hbi _ hre_mem).trans ?_; rw [← mul_assoc]; gcongr
      _ ≤ Ci * (C_im (3 / 2 - w₀.re) * (1 + |y|) ^ (3 / 2 - w₀.re) * Real.exp (π * |y| / 2)) :=
            mul_le_mul_of_nonneg_left (hshift _ him_le y) hCi.le
      _ ≤ C * (1 + |y|) ^ (3 / 2 - w₀.re) * Real.exp (π * |y| / 2) := by
            rw [← mul_assoc, ← mul_assoc]; gcongr; exact le_max_left _ _
  · have hrp_up : (1 + |(w + y * I).im|) ^ (3 / 2 - (w + y * I).re) ≤
        (1 + |(w + y * I).im|) ^ (5 / 2 - w₀.re) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (w + y * I).im])
        (by simp; linarith [(abs_le.mp hre_diff).1])
    calc ‖deriv (fun z : ℂ ↦ (Complex.Gamma z)⁻¹) (w + y * I)‖
        ≤ Cd * ((1 + |(w + y * I).im|) ^ (5 / 2 - w₀.re) *
            Real.exp (π * |(w + y * I).im| / 2)) := by
            refine (hbd _ hre_mem).trans ?_; rw [← mul_assoc]; gcongr
      _ ≤ Cd * (C_im (5 / 2 - w₀.re) * (1 + |y|) ^ (5 / 2 - w₀.re) * Real.exp (π * |y| / 2)) :=
            mul_le_mul_of_nonneg_left (hshift _ him_le y) hCd.le
      _ ≤ C * (1 + |y|) ^ (5 / 2 - w₀.re) * Real.exp (π * |y| / 2) := by
            rw [← mul_assoc, ← mul_assoc]; gcongr; exact le_max_right _ _

end TauCeti
