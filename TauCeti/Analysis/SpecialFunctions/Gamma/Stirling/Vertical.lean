/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Stirling's formula on vertical strips

For every compact interval `[a, b]`,
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)`
uniformly for `σ ∈ [a, b]` as `|t| → ∞`, that is along `cocompact ℝ`
([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9), with the remainder of
[DLMF 5.11.1](https://dlmf.nist.gov/5.11.E1)). The statement is additive in `log ‖Γ‖`, so it adds
up over finite products of shifted Gamma factors.

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
  `(2 / (1 - cos (π / 4)) ^ 3 + |σ - 1/2| |σ| + σ ^ 2) / |t|` at every `s = σ + i t` with `t ≠ 0`
  and `|σ| ≤ |t|`.
* `TauCeti.exists_abs_log_norm_Gamma_vertical_sub_le`: one constant and one threshold for all `s`
  with `Re s ∈ [a, b]`.
* `TauCeti.isBigO_log_norm_Gamma_vertical_sub`: the uniform `O(1 / |t|)` form in `(σ, t)` along
  `𝓟 (Icc a b) ×ˢ cocompact ℝ`.
* `TauCeti.isBigO_log_norm_Gamma_vertical_strip_sub`: the same as a function of `s : ℂ`, along
  `cocompact ℂ` restricted to the strip `Re s ∈ [a, b]`.
* `TauCeti.isBigO_log_norm_Gamma_vertical_line_sub`: the same on a single vertical line, along
  `cocompact ℝ`.
* `TauCeti.exists_norm_Gamma_le_of_re_mem_Icc`: uniform norm upper bound for `Γ(s)` on a vertical
  strip away from the real axis.
* `TauCeti.exists_norm_inv_Gamma_le_of_re_mem_Icc`: uniform norm upper bound for `(Γ(s))⁻¹` on a
  vertical strip away from the real axis.
* `TauCeti.exists_norm_Gamma_add_mul_I_le_exp_neg`,
  `TauCeti.exists_norm_Gamma_sub_mul_I_le_exp_neg`: exponential vertical-line decay
  `O(exp (-((π / 2 - ε) |y|)))` for `Γ(a ± i y)`.
* `TauCeti.exists_norm_inv_Gamma_add_mul_I_le_exp_on_closedBall`,
  `TauCeti.exists_norm_inv_Gamma_add_mul_I_le_exp`: exponential vertical-line upper bound
  `O(exp ((π / 2 + ε) |y|))` for `(Γ(w + i y))⁻¹`, uniformly on closed balls and on a single line.
* `TauCeti.exists_norm_deriv_inv_Gamma_add_mul_I_le_exp_on_closedBall`: Cauchy derivative bound
  for `w ↦ (Γ(w + i y))⁻¹` uniformly on closed balls.
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
      (2 / (1 - Real.cos (π / 4)) ^ 3 + |σ - 1 / 2| * |σ| + σ ^ 2) / |t| := by
  set s : ℂ := σ + t * I
  set K : ℝ := 2 / (1 - Real.cos (π / 4)) ^ 3
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  rw [abs_of_pos ht]
  have hs0 : s ≠ 0 := fun h ↦ ht.ne' (by rw [← him, h, zero_im])
  have hts : t ≤ ‖s‖ := by simpa [him, abs_of_pos ht] using abs_im_le_norm s
  have hK : 0 ≤ K := div_nonneg zero_le_two (pow_nonneg (sub_nonneg.2 (Real.cos_le_one _)) 3)
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
  have hS := abs_log_norm_Gamma_sub_stirling_le (by positivity) (by linarith [Real.pi_pos])
    hsector hs0
  rw [hre, him, ← div_div] at hS
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
      (2 / (1 - Real.cos (π / 4)) ^ 3 + |σ - 1 / 2| * |σ| + σ ^ 2) / |t| := by
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
(2 / (1 - cos (π / 4)) ^ 3 + |σ - 1/2| |σ| + σ ^ 2) / |t|`. -/
theorem abs_log_norm_Gamma_vertical_sub_le {s : ℂ} (hs : s.im ≠ 0) (hre : |s.re| ≤ |s.im|) :
    |Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2)| ≤
      (2 / (1 - Real.cos (π / 4)) ^ 3 + |s.re - 1 / 2| * |s.re| + s.re ^ 2) / |s.im| := by
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
  refine ⟨2 / (1 - Real.cos (π / 4)) ^ 3 + (M + 1 / 2) * M + M ^ 2, M + 1,
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

/-- **Stirling's formula on vertical strips** ([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9)):
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)` uniformly for
`σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gamma_vertical_sub (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖Complex.Gamma (p.1 + p.2 * I)‖ -
        ((p.1 - 1 / 2) * Real.log |p.2| - π * |p.2| / 2 + Real.log (2 * π) / 2))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun p ↦ |p.2|⁻¹ := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ t : ℝ in cocompact ℝ, T ≤ |t| := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop T] with t ht
    rwa [Real.norm_eq_abs] at ht
  filter_upwards [(eventually_principal.2 fun _ hσ ↦ hσ).prod_mk hT] with p hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_abs, ← div_eq_mul_inv]
  simpa using h (p.1 + p.2 * I) (by simpa using hp.1) (by simpa using hp.2)

/-- **Stirling's formula on vertical strips** as a function of `s = σ + i t`:
`log ‖Γ(s)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)` as `s → ∞` in the strip
`a ≤ Re s ≤ b`. -/
theorem isBigO_log_norm_Gamma_vertical_strip_sub (a b : ℝ) :
    (fun s : ℂ ↦ Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2))
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun s ↦ |s.im|⁻¹ := by
  obtain ⟨C, T, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ s : ℂ in cocompact ℂ, T + max |a| |b| ≤ ‖s‖ :=
    (tendsto_norm_cocompact_atTop (E := ℂ)).eventually_ge_atTop _
  filter_upwards [hT.filter_mono inf_le_left,
    (eventually_principal.2 fun _ hs ↦ hs).filter_mono inf_le_right] with s hs hre
  have hM : |s.re| ≤ max |a| |b| := abs_le_max_abs_abs hre.1 hre.2
  have hnorm := norm_le_abs_re_add_abs_im s
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_abs, ← div_eq_mul_inv]
  exact h s hre (by linarith)

/-- Stirling's formula on a single vertical line `Re s = σ`:
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gamma_vertical_line_sub (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gamma (σ + t * I)‖ -
        ((σ - 1 / 2) * Real.log |t| - π * |t| / 2 + Real.log (2 * π) / 2))
      =O[cocompact ℝ] fun t ↦ |t|⁻¹ :=
  (isBigO_log_norm_Gamma_vertical_sub σ σ).comp_tendsto
    ((tendsto_principal.2 (Eventually.of_forall fun _ ↦ left_mem_Icc.2 le_rfl)).prodMk tendsto_id)

/-- Upper bound for `‖Γ(s)‖` on a vertical strip `a ≤ Re s ≤ b` away from the real axis:
`‖Γ(s)‖ ≤ C * |Im s| ^ (Re s - 1 / 2) * exp (-(π * |Im s| / 2))` for `|Im s| ≥ T`. -/
theorem exists_norm_Gamma_le_of_re_mem_Icc (a b : ℝ) :
    ∃ C > 0, ∃ T : ℝ, 1 ≤ T ∧ ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      ‖Complex.Gamma s‖ ≤ C * |s.im| ^ (s.re - 1 / 2) * Real.exp (-(π * |s.im| / 2)) := by
  obtain ⟨C₀, T₀, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  refine ⟨Real.exp (Real.log (2 * π) / 2 + max C₀ 0), Real.exp_pos _, max T₀ 1, le_max_right _ _,
    fun s hs ht ↦ ?_⟩
  have ht1 : 1 ≤ |s.im| := (le_max_right T₀ 1).trans ht
  have ht0 : 0 < |s.im| := by linarith
  have hΓ : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.mpr <| Complex.Gamma_ne_zero fun m hm ↦ by
    have him : s.im = 0 := by rw [hm]; simp
    exact ht0.ne' (by simp [him])
  have hst := (abs_sub_le_iff.mp (h s hs ((le_max_left T₀ 1).trans ht))).1
  have hC : C₀ / |s.im| ≤ max C₀ 0 :=
    (div_le_div_of_nonneg_right (le_max_left C₀ 0) ht0.le).trans
      (div_le_self (le_max_right _ _) ht1)
  have hlog : Real.log ‖Complex.Gamma s‖ ≤
      (Real.log (2 * π) / 2 + max C₀ 0) + (s.re - 1 / 2) * Real.log |s.im| + -(π * |s.im| / 2) := by
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log hΓ, Real.exp_add, Real.exp_add, mul_comm (s.re - 1 / 2),
    ← Real.rpow_def_of_pos ht0] at hexp

/-- Upper bound for `‖(Γ(s))⁻¹‖` on a vertical strip `a ≤ Re s ≤ b` away from the real axis:
`‖(Γ(s))⁻¹‖ ≤ C * |Im s| ^ (1 / 2 - Re s) * exp (π * |Im s| / 2)` for `|Im s| ≥ T`. -/
theorem exists_norm_inv_Gamma_le_of_re_mem_Icc (a b : ℝ) :
    ∃ C > 0, ∃ T : ℝ, 1 ≤ T ∧ ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * |s.im| ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by
  obtain ⟨C₀, T₀, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  refine ⟨Real.exp (max C₀ 0 - Real.log (2 * π) / 2), Real.exp_pos _, max T₀ 1, le_max_right _ _,
    fun s hs ht ↦ ?_⟩
  have ht1 : 1 ≤ |s.im| := (le_max_right T₀ 1).trans ht
  have ht0 : 0 < |s.im| := by linarith
  have hΓ : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.mpr <| Complex.Gamma_ne_zero fun m hm ↦ by
    have him : s.im = 0 := by rw [hm]; simp
    exact ht0.ne' (by simp [him])
  have hst := (abs_sub_le_iff.mp (h s hs ((le_max_left T₀ 1).trans ht))).2
  have hC : C₀ / |s.im| ≤ max C₀ 0 :=
    (div_le_div_of_nonneg_right (le_max_left C₀ 0) ht0.le).trans
      (div_le_self (le_max_right _ _) ht1)
  have hlog : -Real.log ‖Complex.Gamma s‖ ≤
      (max C₀ 0 - Real.log (2 * π) / 2) + (1 / 2 - s.re) * Real.log |s.im| + π * |s.im| / 2 := by
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_neg, Real.exp_log hΓ, ← norm_inv, Real.exp_add, Real.exp_add,
    mul_comm (1 / 2 - s.re), ← Real.rpow_def_of_pos ht0] at hexp

/-- Exponential vertical-line decay for `Γ(a + i y)`: for every `ε > 0` and every `a` whose real
part is not a nonpositive integer, `‖Γ(a + i y)‖ ≤ C exp (-((π / 2 - ε) |y|))` for all `y : ℝ`. -/
theorem exists_norm_Gamma_add_mul_I_le_exp_neg (a : ℂ) (ha : ∀ n : ℕ, a.re ≠ -n) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C > 0, ∀ y : ℝ, ‖Complex.Gamma (a + y * I)‖ ≤ C * Real.exp (-((π / 2 - ε) * |y|)) := by
  obtain ⟨C₁, hC₁, T₁, hT₁, hSt⟩ := exists_norm_Gamma_le_of_re_mem_Icc a.re a.re
  obtain ⟨M₂, _, hpow⟩ := exists_rpow_mul_exp_neg_mul_le (le_max_right (a.re - 1 / 2) 0) hε
  set C₂ : ℝ := max M₂ 1
  have hC₂ : 0 < C₂ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set T : ℝ := max (2 * |a.im|) (2 * T₁)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (Complex.continuous_Gamma_add_mul_I ha).continuousOn (s := Icc (-T) T)
  set Ctail : ℝ := C₁ * C₂ * Real.exp ((π / 2 + ε) * |a.im|)
  set Cmid : ℝ := max B 1 * Real.exp (|π / 2 - ε| * T)
  refine ⟨max Ctail Cmid, lt_of_lt_of_le (by positivity) (le_max_left _ _), fun y ↦ ?_⟩
  by_cases hy : T ≤ |y|
  · -- Tail `|y| ≥ T`: absorb the power factor `|a.im + y| ^ (a.re - 1 / 2)` into `exp (ε |y|)`.
    set u : ℝ := |a.im + y|
    have hy1 : 2 * |a.im| ≤ |y| := (le_max_left _ _).trans hy
    have hy2 : 2 * T₁ ≤ |y| := (le_max_right _ _).trans hy
    have hu_ge : |y| - |a.im| ≤ u := by
      have h := abs_add_le (y + a.im) (-a.im)
      rw [add_neg_cancel_right, abs_neg, add_comm y a.im] at h
      linarith
    have hu_le : u ≤ |y| + |a.im| := by simpa [u, add_comm] using abs_add_le y a.im
    have hu_T₁ : T₁ ≤ u := by linarith
    have hu_1 : 1 ≤ u := hT₁.trans hu_T₁
    have hs := hSt (a + y * I) (by simp) (by simpa [u] using hu_T₁)
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero, add_im, mul_im] at hs
    have hu_pow : u ^ (a.re - 1 / 2) * Real.exp (-(ε * u)) ≤ C₂ :=
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hu_1 (le_max_left _ _)) (Real.exp_pos _).le).trans
        ((hpow u (by linarith)).trans (le_max_left _ _))
    have hexp : Real.exp (ε * u - π * u / 2) ≤
        Real.exp ((π / 2 + ε) * |a.im|) * Real.exp (-((π / 2 - ε) * |y|)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hsplit : u ^ (a.re - 1 / 2) * Real.exp (-(π * u / 2)) =
        (u ^ (a.re - 1 / 2) * Real.exp (-(ε * u))) * Real.exp (ε * u - π * u / 2) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    calc ‖Complex.Gamma (a + y * I)‖
        ≤ C₁ * (u ^ (a.re - 1 / 2) * Real.exp (-(π * u / 2))) := by simpa [mul_assoc] using hs
      _ = C₁ * ((u ^ (a.re - 1 / 2) * Real.exp (-(ε * u))) * Real.exp (ε * u - π * u / 2)) := by
          rw [hsplit]
      _ ≤ C₁ * (C₂ * (Real.exp ((π / 2 + ε) * |a.im|) * Real.exp (-((π / 2 - ε) * |y|)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hu_pow hexp (Real.exp_pos _).le hC₂.le) hC₁.le
      _ = Ctail * Real.exp (-((π / 2 - ε) * |y|)) := by simp [Ctail, mul_assoc]
      _ ≤ max Ctail Cmid * Real.exp (-((π / 2 - ε) * |y|)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · -- Compact segment `|y| < T`: bounded by continuity.
    push Not at hy
    have hnorm : ‖Complex.Gamma (a + y * I)‖ ≤ max B 1 :=
      (hB y (abs_le.mp hy.le)).trans (le_max_left _ _)
    have hexp : 1 ≤ Real.exp (|π / 2 - ε| * T) * Real.exp (-((π / 2 - ε) * |y|)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have h1 : (π / 2 - ε) * |y| ≤ |π / 2 - ε| * |y| :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
      have h2 : |π / 2 - ε| * |y| ≤ |π / 2 - ε| * T :=
        mul_le_mul_of_nonneg_left hy.le (abs_nonneg _)
      linarith
    calc ‖Complex.Gamma (a + y * I)‖ ≤ max B 1 * 1 := by simpa using hnorm
      _ ≤ max B 1 * (Real.exp (|π / 2 - ε| * T) * Real.exp (-((π / 2 - ε) * |y|))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = Cmid * Real.exp (-((π / 2 - ε) * |y|)) := by simp [Cmid, mul_assoc]
      _ ≤ max Ctail Cmid * Real.exp (-((π / 2 - ε) * |y|)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- Exponential vertical-line decay for `Γ(a - i y)`: for every `ε > 0` and every `a` whose real
part is not a nonpositive integer, `‖Γ(a - i y)‖ ≤ C exp (-((π / 2 - ε) |y|))` for all `y : ℝ`. -/
theorem exists_norm_Gamma_sub_mul_I_le_exp_neg (a : ℂ) (ha : ∀ n : ℕ, a.re ≠ -n) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C > 0, ∀ y : ℝ, ‖Complex.Gamma (a - y * I)‖ ≤ C * Real.exp (-((π / 2 - ε) * |y|)) := by
  obtain ⟨C, hC, h⟩ := exists_norm_Gamma_add_mul_I_le_exp_neg a ha hε
  refine ⟨C, hC, fun y ↦ ?_⟩
  have heq : a - (y : ℂ) * I = a + ((-y : ℝ) : ℂ) * I := by push_cast; ring
  simpa [heq, abs_neg] using h (-y)

/-- Uniform exponential vertical-line bound for `(Γ(w + i y))⁻¹` on `Metric.closedBall c₀ R`:
for every `ε > 0`, `‖(Γ(w + i y))⁻¹‖ ≤ C exp ((π / 2 + ε) |y|)` uniformly for
`w ∈ closedBall c₀ R` and `y : ℝ`. -/
theorem exists_norm_inv_Gamma_add_mul_I_le_exp_on_closedBall (c₀ : ℂ) (R : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C > 0, ∀ w ∈ Metric.closedBall c₀ R, ∀ y : ℝ,
      ‖(Complex.Gamma (w + y * I))⁻¹‖ ≤ C * Real.exp ((π / 2 + ε) * |y|) := by
  obtain ⟨C₁, hC₁, T₁, hT₁, hSt⟩ := exists_norm_inv_Gamma_le_of_re_mem_Icc (c₀.re - R) (c₀.re + R)
  obtain ⟨M₂, _, hpow⟩ := exists_rpow_mul_exp_neg_mul_le (le_max_right (1 / 2 - (c₀.re - R)) 0) hε
  set C₂ : ℝ := max M₂ 1
  have hC₂ : 0 < C₂ := lt_of_lt_of_le one_pos (le_max_right _ _)
  set S : ℝ := |c₀.im| + R
  set T : ℝ := max (2 * S) (2 * T₁)
  obtain ⟨B, hB⟩ := (isCompact_closedBall c₀ (R + T)).exists_bound_of_continuousOn
    Complex.differentiable_one_div_Gamma.continuous.continuousOn
  set Ctail : ℝ := C₁ * C₂ * Real.exp ((π / 2 + ε) * S)
  refine ⟨max Ctail (max B 1), lt_of_lt_of_le (by positivity) (le_max_left _ _), fun w hw y ↦ ?_⟩
  have hdist : ‖w - c₀‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hw
  have hw_re : w.re ∈ Icc (c₀.re - R) (c₀.re + R) := by
    have hre : |w.re - c₀.re| ≤ R := (abs_re_le_norm (w - c₀)).trans hdist
    exact ⟨by linarith [(abs_le.mp hre).1], by linarith [(abs_le.mp hre).2]⟩
  have hw_im : |w.im| ≤ S := by
    have him : |w.im - c₀.im| ≤ R := (abs_im_le_norm (w - c₀)).trans hdist
    have htri : |w.im| ≤ |w.im - c₀.im| + |c₀.im| := by
      simpa [sub_add_cancel] using abs_add_le (w.im - c₀.im) c₀.im
    linarith
  by_cases hy : T ≤ |y|
  · -- Tail `|y| ≥ T`: Stirling's vertical-strip bound on `[c₀.re - R, c₀.re + R]`.
    set u : ℝ := |w.im + y|
    have hy1 : 2 * S ≤ |y| := (le_max_left _ _).trans hy
    have hy2 : 2 * T₁ ≤ |y| := (le_max_right _ _).trans hy
    have hu_ge : |y| - S ≤ u := by
      have h := abs_add_le (y + w.im) (-w.im)
      rw [add_neg_cancel_right, abs_neg, add_comm y w.im] at h
      linarith
    have hu_le : u ≤ |y| + S := by
      have h : u ≤ |y| + |w.im| := by simpa [u, add_comm] using abs_add_le y w.im
      linarith
    have hu_T₁ : T₁ ≤ u := by linarith
    have hu_1 : 1 ≤ u := hT₁.trans hu_T₁
    have hs := hSt (w + y * I) (by simpa using hw_re) (by simpa [u] using hu_T₁)
    simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero, add_im, mul_im] at hs
    have hu_pow : u ^ (1 / 2 - w.re) * Real.exp (-(ε * u)) ≤ C₂ :=
      (mul_le_mul_of_nonneg_right
        ((Real.rpow_le_rpow_of_exponent_le hu_1 (by linarith [hw_re.1])).trans
          (Real.rpow_le_rpow_of_exponent_le hu_1 (le_max_left _ _)))
        (Real.exp_pos _).le).trans ((hpow u (by linarith)).trans (le_max_left _ _))
    have hexp : Real.exp ((π / 2 + ε) * u) ≤
        Real.exp ((π / 2 + ε) * S) * Real.exp ((π / 2 + ε) * |y|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have hsplit : u ^ (1 / 2 - w.re) * Real.exp (π * u / 2) =
        (u ^ (1 / 2 - w.re) * Real.exp (-(ε * u))) * Real.exp ((π / 2 + ε) * u) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    calc ‖(Complex.Gamma (w + y * I))⁻¹‖
        ≤ C₁ * (u ^ (1 / 2 - w.re) * Real.exp (π * u / 2)) := by simpa [mul_assoc] using hs
      _ = C₁ * ((u ^ (1 / 2 - w.re) * Real.exp (-(ε * u))) * Real.exp ((π / 2 + ε) * u)) := by
          rw [hsplit]
      _ ≤ C₁ * (C₂ * (Real.exp ((π / 2 + ε) * S) * Real.exp ((π / 2 + ε) * |y|))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hu_pow hexp (Real.exp_pos _).le hC₂.le) hC₁.le
      _ = Ctail * Real.exp ((π / 2 + ε) * |y|) := by simp [Ctail, mul_assoc]
      _ ≤ max Ctail (max B 1) * Real.exp ((π / 2 + ε) * |y|) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · -- Compact region `|y| < T`: bounded by continuity of `Γ⁻¹`.
    push Not at hy
    have hmem : w + y * I ∈ Metric.closedBall c₀ (R + T) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖w + y * I - c₀‖ = ‖(w - c₀) + y * I‖ := by ring_nf
        _ ≤ ‖w - c₀‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
        _ = ‖w - c₀‖ + |y| := by simp
        _ ≤ R + T := by linarith
    have hnorm : ‖(Complex.Gamma (w + y * I))⁻¹‖ ≤ max B 1 :=
      (hB _ hmem).trans (le_max_left _ _)
    have hexp : 1 ≤ Real.exp ((π / 2 + ε) * |y|) :=
      Real.one_le_exp (mul_nonneg (by positivity [Real.pi_pos]) (abs_nonneg _))
    calc ‖(Complex.Gamma (w + y * I))⁻¹‖ ≤ max B 1 * 1 := by simpa using hnorm
      _ ≤ max B 1 * Real.exp ((π / 2 + ε) * |y|) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ max Ctail (max B 1) * Real.exp ((π / 2 + ε) * |y|) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- Exponential vertical-line bound for `(Γ(c + i y))⁻¹` on a single vertical line:
for every `ε > 0`, `‖(Γ(c + i y))⁻¹‖ ≤ C exp ((π / 2 + ε) |y|)` for all `y : ℝ`. -/
theorem exists_norm_inv_Gamma_add_mul_I_le_exp (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C > 0, ∀ y : ℝ, ‖(Complex.Gamma (c + y * I))⁻¹‖ ≤ C * Real.exp ((π / 2 + ε) * |y|) := by
  obtain ⟨C, hC, h⟩ := exists_norm_inv_Gamma_add_mul_I_le_exp_on_closedBall c 0 hε
  exact ⟨C, hC, fun y ↦ h c (Metric.mem_closedBall_self le_rfl) y⟩

/-- Cauchy derivative estimate on `Metric.closedBall c₀ R` for `w ↦ (Γ(w + i y))⁻¹`:
for every `ε > 0`, `‖deriv (fun w ↦ (Γ(w + i y))⁻¹) c‖ ≤ C exp ((π / 2 + ε) |y|)` uniformly
for `c ∈ closedBall c₀ R` and `y : ℝ`. -/
theorem exists_norm_deriv_inv_Gamma_add_mul_I_le_exp_on_closedBall (c₀ : ℂ) (R : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ C > 0, ∀ c ∈ Metric.closedBall c₀ R, ∀ y : ℝ,
      ‖deriv (fun w : ℂ ↦ (Complex.Gamma (w + y * I))⁻¹) c‖ ≤ C * Real.exp ((π / 2 + ε) * |y|) := by
  obtain ⟨C, hC, h⟩ := exists_norm_inv_Gamma_add_mul_I_le_exp_on_closedBall c₀ (R + 1) hε
  refine ⟨C, hC, fun c hc y ↦ ?_⟩
  have hdiff : Differentiable ℂ fun w : ℂ ↦ (Complex.Gamma (w + y * I))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add (differentiable_const _))
  have hbound : ∀ w ∈ Metric.sphere c 1,
      ‖(Complex.Gamma (w + y * I))⁻¹‖ ≤ C * Real.exp ((π / 2 + ε) * |y|) := by
    intro w hw
    refine h w ?_ y
    rw [Metric.mem_closedBall] at hc ⊢
    rw [Metric.mem_sphere] at hw
    linarith [dist_triangle w c c₀]
  simpa using norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hdiff.diffContOnCl hbound

end TauCeti
