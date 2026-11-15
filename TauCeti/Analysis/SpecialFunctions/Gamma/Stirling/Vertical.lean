/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
import Mathlib.Analysis.Complex.Liouville
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Stirling's formula on vertical strips

For every compact interval `[a, b]`,
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)`
uniformly for `σ ∈ [a, b]` as `|t| → ∞`, that is along `cocompact ℝ`
([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9), with the remainder of
[DLMF 5.11.1](https://dlmf.nist.gov/5.11.E1)). The statement is additive in `log ‖Γ‖`, so it adds
up over finite products of shifted Gamma factors. Exponentiating and combining with compactness near
the real axis gives global vertical-strip norm bounds for `Γ` away from the real axis, for `Γ` on
every pole-free vertical line, and for the entire function `1 / Γ` and its derivative across the
whole strip.

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
* `TauCeti.exists_norm_Gamma_vertical_strip_le`: exponential decay
  `‖Γ(s)‖ ≤ C (1 + |Im s|)^{Re s - 1/2} exp (-π |Im s| / 2)` for `Re s ∈ [a, b]` and `δ ≤ |Im s|`.
* `TauCeti.exists_norm_Gamma_vertical_le`, `TauCeti.exists_norm_Gamma_add_mul_I_le`, and
  `TauCeti.exists_norm_Gamma_sub_mul_I_le`: exponential decay
  `‖Γ(z ± i y)‖ ≤ C (1 + |y|)^{Re z - 1/2} exp (-π |y| / 2)` along pole-free vertical lines.
* `TauCeti.exists_norm_inv_Gamma_vertical_strip_le` and
  `TauCeti.exists_norm_deriv_inv_Gamma_vertical_strip_le`: growth bounds of order
  `(1 + |Im s|)^{1/2 - Re s} exp (π |Im s| / 2)` and
  `(1 + |Im s|)^{3/2 - Re s} exp (π |Im s| / 2)` for `1 / Γ` and its derivative on `Re s ∈ [a, b]`.
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

/-- Uniform `O(1)` comparison of `log ‖Γ(s)‖` with `(Re s - 1/2) log (1 + |Im s|) - π |Im s| / 2`
for large `|Im s|` in a vertical strip. -/
private theorem exists_abs_log_norm_Gamma_vertical_one_add_sub_le (a b : ℝ) :
    ∃ C T : ℝ, 1 ≤ T ∧ ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Complex.Gamma s‖ -
          ((s.re - 1 / 2) * Real.log (1 + |s.im|) - π * |s.im| / 2)| ≤ C := by
  obtain ⟨C₀, T₀, hS⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  set K : ℝ := max |a - 1 / 2| |b - 1 / 2|
  refine ⟨|C₀| + |Real.log (2 * π) / 2| + K * Real.log 2, max T₀ 1, le_max_right _ _,
    fun s hs ht ↦ ?_⟩
  have ht1 : 1 ≤ |s.im| := (le_max_right T₀ 1).trans ht
  have ht0 : 0 < |s.im| := zero_lt_one.trans_le ht1
  have hmain := hS s hs ((le_max_left T₀ 1).trans ht)
  have hC₀ : C₀ / |s.im| ≤ |C₀| :=
    (div_le_div_of_nonneg_right (le_abs_self C₀) ht0.le).trans
      (div_le_self (abs_nonneg C₀) ht1)
  have hlog : |Real.log (1 + |s.im|) - Real.log (|s.im|)| ≤ Real.log 2 := by
    rw [abs_of_nonneg (sub_nonneg.2 (Real.log_le_log ht0 (by linarith))),
      ← Real.log_div (by positivity) ht0.ne']
    exact Real.log_le_log (by positivity) ((div_le_iff₀ ht0).2 (by linarith))
  have hK : |s.re - 1 / 2| ≤ K :=
    abs_le_max_abs_abs (sub_le_sub_right hs.1 _) (sub_le_sub_right hs.2 _)
  have hmul : |(s.re - 1 / 2) * (Real.log |s.im| - Real.log (1 + |s.im|))| ≤ K * Real.log 2 := by
    rw [abs_mul, abs_sub_comm (Real.log |s.im|)]
    exact mul_le_mul hK hlog (abs_nonneg _) ((abs_nonneg _).trans hK)
  have hsplit : Real.log ‖Complex.Gamma s‖ -
      ((s.re - 1 / 2) * Real.log (1 + |s.im|) - π * |s.im| / 2) =
      (Real.log ‖Complex.Gamma s‖ -
        ((s.re - 1 / 2) * Real.log |s.im| - π * |s.im| / 2 + Real.log (2 * π) / 2)) +
      Real.log (2 * π) / 2 +
      (s.re - 1 / 2) * (Real.log |s.im| - Real.log (1 + |s.im|)) := by ring
  rw [hsplit]
  exact (abs_add_three _ _ _).trans (by linarith [le_abs_self (Real.log (2 * π) / 2)])

/-- Exponential decay of `Γ` on a vertical strip away from the real axis: for `Re s ∈ [a, b]` and
`δ ≤ |Im s|` (`0 < δ`), `‖Γ(s)‖ ≤ C (1 + |Im s|)^{Re s - 1/2} exp (-π |Im s| / 2)`. -/
theorem exists_norm_Gamma_vertical_strip_le (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → δ ≤ |s.im| →
      ‖Complex.Gamma s‖ ≤ C * (1 + |s.im|) ^ (s.re - 1 / 2) * Real.exp (-π * |s.im| / 2) := by
  obtain ⟨C₁, T₁, hT₁, hS⟩ := exists_abs_log_norm_Gamma_vertical_one_add_sub_le a b
  set T : ℝ := max T₁ δ
  have hTpos : 0 < 1 + T := by linarith [hT₁.trans (le_max_left T₁ δ)]
  let φ : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) + p.2 * I
  let S : Set (ℝ × ℝ) := Icc a b ×ˢ (Icc (-T) (-δ) ∪ Icc δ T)
  have hK : IsCompact (φ '' S) :=
    (isCompact_Icc.prod (isCompact_Icc.union isCompact_Icc)).image (by fun_prop)
  have hcont : ContinuousOn Complex.Gamma (φ '' S) := by
    refine continuousOn_of_forall_continuousAt fun w hw ↦ ?_
    rcases hw with ⟨⟨σ, t⟩, ⟨_, ht⟩, rfl⟩
    have ht0 : t ≠ 0 := by
      rcases ht with ht | ht <;> linarith [ht.1, ht.2]
    refine (Complex.differentiableAt_Gamma _ fun m hm ↦ ht0 ?_).continuousAt
    simpa [φ] using congrArg Complex.im hm
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
  set m₀ : ℝ := min 1 ((1 + T) ^ (a - 1 / 2)) * Real.exp (-π * T / 2)
  have hm₀ : 0 < m₀ := mul_pos (lt_min one_pos (Real.rpow_pos_of_pos hTpos _)) (Real.exp_pos _)
  refine ⟨max (Real.exp C₁) (max M 0 / m₀), fun s hs hδs ↦ ?_⟩
  rcases le_or_gt T |s.im| with hTs | hTs
  · -- Tail `T ≤ |s.im|`: exponentiate Stirling's strip estimate.
    have ht1 : 1 ≤ |s.im| := (hT₁.trans (le_max_left T₁ δ)).trans hTs
    have him0 : s.im ≠ 0 := abs_pos.1 (zero_lt_one.trans_le ht1)
    have hΓpos : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.2 (Complex.Gamma_ne_zero fun m hm ↦
      him0 (by simpa using congrArg Complex.im hm))
    have hlog : Real.log ‖Complex.Gamma s‖ ≤
        C₁ + (s.re - 1 / 2) * Real.log (1 + |s.im|) - π * |s.im| / 2 := by
      linarith [(abs_le.1 (hS s hs ((le_max_left T₁ δ).trans hTs))).2]
    calc ‖Complex.Gamma s‖ = Real.exp (Real.log ‖Complex.Gamma s‖) :=
          (Real.exp_log hΓpos).symm
      _ ≤ Real.exp (C₁ + (s.re - 1 / 2) * Real.log (1 + |s.im|) - π * |s.im| / 2) :=
          Real.exp_le_exp.2 hlog
      _ = Real.exp C₁ * (1 + |s.im|) ^ (s.re - 1 / 2) * Real.exp (-π * |s.im| / 2) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_add,
            Real.rpow_def_of_pos (by positivity), mul_comm (Real.log _)]
          ring_nf
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _
  · -- Compact collar `δ ≤ |s.im| < T`.
    have hsK : s ∈ φ '' S := by
      refine ⟨(s.re, s.im), ⟨hs, ?_⟩, Complex.re_add_im s⟩
      rcases le_or_gt 0 s.im with him | him
      · rw [abs_of_nonneg him] at hδs hTs
        exact Or.inr ⟨hδs, hTs.le⟩
      · rw [abs_of_neg him] at hδs hTs
        exact Or.inl ⟨by linarith, by linarith⟩
    have hrpow : min 1 ((1 + T) ^ (a - 1 / 2)) ≤ (1 + |s.im|) ^ (s.re - 1 / 2) := by
      refine (le_of_le_of_eq ?_ rfl).trans
        (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im])
          (sub_le_sub_right hs.1 _))
      rcases le_total 0 (a - 1 / 2) with hp | hp
      · exact (min_le_left _ _).trans
          (by simpa using Real.rpow_le_rpow zero_le_one (by linarith [abs_nonneg s.im]) hp)
      · exact (min_le_right _ _).trans
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [hTs.le]) hp)
    have hexp : Real.exp (-π * T / 2) ≤ Real.exp (-π * |s.im| / 2) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, hTs.le])
    have hm_le : m₀ ≤ (1 + |s.im|) ^ (s.re - 1 / 2) * Real.exp (-π * |s.im| / 2) :=
      mul_le_mul hrpow hexp (Real.exp_pos _).le (by positivity)
    calc ‖Complex.Gamma s‖ ≤ max M 0 := (hM s hsK).trans (le_max_left M 0)
      _ = max M 0 / m₀ * m₀ := (div_mul_cancel₀ _ hm₀.ne').symm
      _ ≤ max M 0 / m₀ * ((1 + |s.im|) ^ (s.re - 1 / 2) * Real.exp (-π * |s.im| / 2)) :=
          mul_le_mul_of_nonneg_left hm_le (div_nonneg (le_max_right M 0) hm₀.le)
      _ ≤ _ := by
          rw [← mul_assoc]
          gcongr
          exact le_max_right _ _

/-- Exponential decay of `Γ` on a vertical line `Re s = σ` avoiding the poles of `Γ`:
`‖Γ(σ + i t)‖ ≤ C (1 + |t|)^{σ - 1/2} exp (-π |t| / 2)` for all `t : ℝ`. -/
theorem exists_norm_Gamma_vertical_le {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) :
    ∃ C : ℝ, ∀ t : ℝ,
      ‖Complex.Gamma (σ + t * I)‖ ≤ C * (1 + |t|) ^ (σ - 1 / 2) * Real.exp (-π * |t| / 2) := by
  obtain ⟨C₁, hC₁⟩ := exists_norm_Gamma_vertical_strip_le σ σ one_pos
  have hcont : ContinuousOn (fun t : ℝ ↦ Complex.Gamma (σ + t * I)) (Icc (-1) 1) := by
    refine continuousOn_of_forall_continuousAt fun t _ ↦ ?_
    refine ((Complex.differentiableAt_Gamma _ fun m hm ↦ hσ m ?_).continuousAt).comp (by fun_prop)
    simpa using congrArg Complex.re hm
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set m₀ : ℝ := min 1 ((2 : ℝ) ^ (σ - 1 / 2)) * Real.exp (-π / 2)
  have hm₀ : 0 < m₀ := mul_pos (lt_min one_pos (by positivity)) (Real.exp_pos _)
  refine ⟨max C₁ (max M 0 / m₀), fun t ↦ ?_⟩
  rcases le_or_gt 1 |t| with ht | ht
  · have h := hC₁ (σ + t * I) (by simp) (by simpa using ht)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at h
    refine h.trans ?_
    gcongr
    exact le_max_left _ _
  · have htIcc : t ∈ Icc (-1 : ℝ) 1 := abs_le.1 ht.le
    have hrpow : min 1 ((2 : ℝ) ^ (σ - 1 / 2)) ≤ (1 + |t|) ^ (σ - 1 / 2) := by
      rcases le_total 0 (σ - 1 / 2) with hp | hp
      · exact (min_le_left _ _).trans
          (by simpa using Real.rpow_le_rpow zero_le_one (by linarith [abs_nonneg t]) hp)
      · exact (min_le_right _ _).trans
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [ht.le]) hp)
    have hexp : Real.exp (-π / 2) ≤ Real.exp (-π * |t| / 2) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, ht.le])
    have hm_le : m₀ ≤ (1 + |t|) ^ (σ - 1 / 2) * Real.exp (-π * |t| / 2) :=
      mul_le_mul hrpow hexp (Real.exp_pos _).le (by positivity)
    calc ‖Complex.Gamma (σ + t * I)‖ ≤ max M 0 := (hM t htIcc).trans (le_max_left M 0)
      _ = max M 0 / m₀ * m₀ := (div_mul_cancel₀ _ hm₀.ne').symm
      _ ≤ max M 0 / m₀ * ((1 + |t|) ^ (σ - 1 / 2) * Real.exp (-π * |t| / 2)) :=
          mul_le_mul_of_nonneg_left hm_le (div_nonneg (le_max_right M 0) hm₀.le)
      _ ≤ _ := by
          rw [← mul_assoc]
          gcongr
          exact le_max_right _ _

/-- Exponential decay of `y ↦ Γ(z + i y)` along the vertical line through `z` when `Re z` is not
a nonpositive integer: `‖Γ(z + i y)‖ ≤ C (1 + |y|)^{Re z - 1/2} exp (-π |y| / 2)`. -/
theorem exists_norm_Gamma_add_mul_I_le {z : ℂ} (hz : ∀ n : ℕ, z.re ≠ -n) :
    ∃ C : ℝ, ∀ y : ℝ,
      ‖Complex.Gamma (z + y * I)‖ ≤ C * (1 + |y|) ^ (z.re - 1 / 2) * Real.exp (-π * |y| / 2) := by
  obtain ⟨C₀, hC₀⟩ := exists_norm_Gamma_vertical_le hz
  set C₁ : ℝ := max C₀ 0
  refine ⟨C₁ * (1 + |z.im|) ^ |z.re - 1 / 2| * Real.exp (π * |z.im| / 2), fun y ↦ ?_⟩
  have hz_eq : z + y * I = (z.re : ℂ) + ((z.im + y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hy_sub : |y| ≤ |z.im| + |z.im + y| := by
    have h := abs_add_le (-z.im) (z.im + y)
    rwa [neg_add_cancel_left, abs_neg] at h
  have hrpow : (1 + |z.im + y|) ^ (z.re - 1 / 2) ≤
      (1 + |z.im|) ^ |z.re - 1 / 2| * (1 + |y|) ^ (z.re - 1 / 2) := by
    rcases le_or_gt 0 (z.re - 1 / 2) with hp | hp
    · have hup : 1 + |z.im + y| ≤ (1 + |z.im|) * (1 + |y|) := by
        nlinarith [abs_add_le z.im y, abs_nonneg z.im, abs_nonneg y]
      calc (1 + |z.im + y|) ^ (z.re - 1 / 2)
          ≤ ((1 + |z.im|) * (1 + |y|)) ^ (z.re - 1 / 2) :=
            Real.rpow_le_rpow (by positivity) hup hp
        _ = (1 + |z.im|) ^ |z.re - 1 / 2| * (1 + |y|) ^ (z.re - 1 / 2) := by
            rw [Real.mul_rpow (by positivity) (by positivity), abs_of_nonneg hp]
    · have hlo : (1 + |z.im|)⁻¹ * (1 + |y|) ≤ 1 + |z.im + y| := by
        rw [inv_mul_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg z.im, abs_nonneg (z.im + y)]
      calc (1 + |z.im + y|) ^ (z.re - 1 / 2)
          ≤ ((1 + |z.im|)⁻¹ * (1 + |y|)) ^ (z.re - 1 / 2) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hlo hp.le
        _ = (1 + |z.im|) ^ |z.re - 1 / 2| * (1 + |y|) ^ (z.re - 1 / 2) := by
            rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
              ← Real.rpow_neg (by positivity), abs_of_neg hp]
  have hexp : Real.exp (-π * |z.im + y| / 2) ≤
      Real.exp (π * |z.im| / 2) * Real.exp (-π * |y| / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  calc ‖Complex.Gamma (z + y * I)‖
      ≤ C₁ * (1 + |z.im + y|) ^ (z.re - 1 / 2) * Real.exp (-π * |z.im + y| / 2) := by
        rw [hz_eq]
        refine (hC₀ (z.im + y)).trans ?_
        gcongr
        exact le_max_left C₀ 0
    _ ≤ C₁ * ((1 + |z.im|) ^ |z.re - 1 / 2| * (1 + |y|) ^ (z.re - 1 / 2)) *
          (Real.exp (π * |z.im| / 2) * Real.exp (-π * |y| / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hrpow (le_max_right C₀ 0)) hexp
          (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- Exponential decay of `y ↦ Γ(z - i y)` along the vertical line through `z` when `Re z` is not
a nonpositive integer: `‖Γ(z - i y)‖ ≤ C (1 + |y|)^{Re z - 1/2} exp (-π |y| / 2)`. -/
theorem exists_norm_Gamma_sub_mul_I_le {z : ℂ} (hz : ∀ n : ℕ, z.re ≠ -n) :
    ∃ C : ℝ, ∀ y : ℝ,
      ‖Complex.Gamma (z - y * I)‖ ≤ C * (1 + |y|) ^ (z.re - 1 / 2) * Real.exp (-π * |y| / 2) := by
  obtain ⟨C, hC⟩ := exists_norm_Gamma_add_mul_I_le hz
  refine ⟨C, fun y ↦ ?_⟩
  have h := hC (-y)
  rwa [ofReal_neg, neg_mul, ← sub_eq_add_neg, abs_neg] at h

/-- Growth bound for the entire function `1 / Γ` on a vertical strip `Re s ∈ [a, b]`:
`‖Γ(s)⁻¹‖ ≤ C (1 + |Im s|)^{1/2 - Re s} exp (π |Im s| / 2)` for all `s` in the strip. -/
theorem exists_norm_inv_Gamma_vertical_strip_le (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by
  obtain ⟨C₁, T, hT₁, hS⟩ := exists_abs_log_norm_Gamma_vertical_one_add_sub_le a b
  have hTpos : 0 < 1 + T := by linarith
  let φ : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) + p.2 * I
  have hK : IsCompact (φ '' (Icc a b ×ˢ Icc (-T) T)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : Continuous (fun z : ℂ ↦ (Complex.Gamma z)⁻¹) := by
    simpa only [one_div] using Complex.differentiable_one_div_Gamma.continuous
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  set m₀ : ℝ := min 1 ((1 + T) ^ (1 / 2 - b))
  have hm₀ : 0 < m₀ := lt_min one_pos (Real.rpow_pos_of_pos hTpos _)
  refine ⟨max (Real.exp C₁) (max M 0 / m₀), fun s hs ↦ ?_⟩
  rcases le_or_gt T |s.im| with hTs | hTs
  · -- Tail `T ≤ |s.im|`: exponentiate Stirling's logarithmic strip estimate for `Γ⁻¹`.
    have him0 : s.im ≠ 0 := abs_pos.1 ((zero_lt_one.trans_le hT₁).trans_le hTs)
    have hΓpos : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.2 (Complex.Gamma_ne_zero fun m hm ↦
      him0 (by simpa using congrArg Complex.im hm))
    have hlog : -Real.log ‖Complex.Gamma s‖ ≤
        C₁ + (1 / 2 - s.re) * Real.log (1 + |s.im|) + π * |s.im| / 2 := by
      linarith [(abs_le.1 (hS s hs hTs)).1]
    calc ‖(Complex.Gamma s)⁻¹‖ = (Real.exp (Real.log ‖Complex.Gamma s‖))⁻¹ := by
          rw [norm_inv, Real.exp_log hΓpos]
      _ = Real.exp (-Real.log ‖Complex.Gamma s‖) := (Real.exp_neg _).symm
      _ ≤ Real.exp (C₁ + (1 / 2 - s.re) * Real.log (1 + |s.im|) + π * |s.im| / 2) :=
          Real.exp_le_exp.2 hlog
      _ = Real.exp C₁ * (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by
          rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos (by positivity),
            mul_comm (Real.log _)]
      _ ≤ _ := by
          gcongr
          exact le_max_left _ _
  · -- Compact rectangle `|s.im| < T`: `Γ⁻¹` is continuous and bounded.
    have hsK : s ∈ φ '' (Icc a b ×ˢ Icc (-T) T) :=
      ⟨(s.re, s.im), ⟨hs, abs_le.1 hTs.le⟩, Complex.re_add_im s⟩
    have hrpow : m₀ ≤ (1 + |s.im|) ^ (1 / 2 - s.re) := by
      refine (le_of_le_of_eq ?_ rfl).trans
        (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im])
          (sub_le_sub_left hs.2 _))
      rcases le_total 0 (1 / 2 - b) with hp | hp
      · exact (min_le_left _ _).trans
          (by simpa using Real.rpow_le_rpow zero_le_one (by linarith [abs_nonneg s.im]) hp)
      · exact (min_le_right _ _).trans
          (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [hTs.le]) hp)
    have hexp : 1 ≤ Real.exp (π * |s.im| / 2) :=
      Real.one_le_exp (by positivity)
    have hm_le : m₀ ≤ (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by
      calc m₀ = m₀ * 1 := (mul_one m₀).symm
        _ ≤ (1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2) :=
            mul_le_mul hrpow hexp zero_le_one (by positivity)
    calc ‖(Complex.Gamma s)⁻¹‖ ≤ max M 0 := (hM s hsK).trans (le_max_left M 0)
      _ = max M 0 / m₀ * m₀ := (div_mul_cancel₀ _ hm₀.ne').symm
      _ ≤ max M 0 / m₀ * ((1 + |s.im|) ^ (1 / 2 - s.re) * Real.exp (π * |s.im| / 2)) :=
          mul_le_mul_of_nonneg_left hm_le (div_nonneg (le_max_right M 0) hm₀.le)
      _ ≤ _ := by
          rw [← mul_assoc]
          gcongr
          exact le_max_right _ _

/-- Growth bound for the derivative of the entire function `1 / Γ` on a vertical strip
`Re s ∈ [a, b]`:
`‖deriv (fun z ↦ Γ(z)⁻¹) s‖ ≤ C (1 + |Im s|)^{3/2 - Re s} exp (π |Im s| / 2)`. -/
theorem exists_norm_deriv_inv_Gamma_vertical_strip_le (a b : ℝ) :
    ∃ C : ℝ, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖deriv (fun z ↦ (Complex.Gamma z)⁻¹) s‖ ≤
        C * (1 + |s.im|) ^ (3 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by
  -- Apply Cauchy's derivative bound on unit spheres inside the widened strip `[a - 1, b + 1]`.
  obtain ⟨C₀, hC₀⟩ := exists_norm_inv_Gamma_vertical_strip_le (a - 1) (b + 1)
  set C₁ : ℝ := max C₀ 0
  set K : ℝ := max |3 / 2 - a| |3 / 2 - b|
  have hent : Differentiable ℂ (fun z : ℂ ↦ (Complex.Gamma z)⁻¹) := by
    simpa only [one_div] using Complex.differentiable_one_div_Gamma
  refine ⟨C₁ * (2 : ℝ) ^ K * Real.exp (π / 2), fun s hs ↦ ?_⟩
  have hbound : ∀ w ∈ Metric.sphere s 1, ‖(Complex.Gamma w)⁻¹‖ ≤
      (C₁ * (2 : ℝ) ^ K * Real.exp (π / 2)) *
        (1 + |s.im|) ^ (3 / 2 - s.re) * Real.exp (π * |s.im| / 2) := by
    intro w hw
    have hw1 : ‖w - s‖ = 1 := mem_sphere_iff_norm.1 hw
    have hre : |w.re - s.re| ≤ 1 := by simpa [← sub_re, hw1] using abs_re_le_norm (w - s)
    have him : |w.im - s.im| ≤ 1 := by simpa [← sub_im, hw1] using abs_im_le_norm (w - s)
    have hwre : w.re ∈ Icc (a - 1) (b + 1) := by
      obtain ⟨h1, h2⟩ := abs_le.1 hre
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have him_up : |w.im| ≤ |s.im| + 1 := by
      have := abs_sub_abs_le_abs_sub w.im s.im
      linarith
    have him_lo : |s.im| ≤ |w.im| + 1 := by
      have := abs_sub_abs_le_abs_sub s.im w.im
      rw [abs_sub_comm] at this
      linarith
    have hK_le : |3 / 2 - s.re| ≤ K := by
      dsimp only [K]
      rw [max_comm]
      exact abs_le_max_abs_abs (sub_le_sub_left hs.2 _) (sub_le_sub_left hs.1 _)
    have hrpow : (1 + |w.im|) ^ (1 / 2 - w.re) ≤
        (2 : ℝ) ^ K * (1 + |s.im|) ^ (3 / 2 - s.re) := by
      have hexp_le : 1 / 2 - w.re ≤ 3 / 2 - s.re := by linarith [(abs_le.1 hre).1]
      refine (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg w.im]) hexp_le).trans ?_
      rcases le_total 0 (3 / 2 - s.re) with hp | hp
      · calc (1 + |w.im|) ^ (3 / 2 - s.re)
            ≤ (2 * (1 + |s.im|)) ^ (3 / 2 - s.re) :=
              Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) hp
          _ = (2 : ℝ) ^ (3 / 2 - s.re) * (1 + |s.im|) ^ (3 / 2 - s.re) :=
              Real.mul_rpow zero_le_two (by positivity)
          _ ≤ (2 : ℝ) ^ K * (1 + |s.im|) ^ (3 / 2 - s.re) := by
              gcongr
              · norm_num
              · exact (le_abs_self _).trans hK_le
      · calc (1 + |w.im|) ^ (3 / 2 - s.re)
            ≤ ((2 : ℝ)⁻¹ * (1 + |s.im|)) ^ (3 / 2 - s.re) :=
              Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [abs_nonneg w.im]) hp
          _ = ((2 : ℝ)⁻¹) ^ (3 / 2 - s.re) * (1 + |s.im|) ^ (3 / 2 - s.re) :=
              Real.mul_rpow (by positivity) (by positivity)
          _ = (2 : ℝ) ^ (-(3 / 2 - s.re)) * (1 + |s.im|) ^ (3 / 2 - s.re) := by
              rw [Real.inv_rpow zero_le_two, ← Real.rpow_neg zero_le_two]
          _ ≤ (2 : ℝ) ^ K * (1 + |s.im|) ^ (3 / 2 - s.re) := by
              gcongr
              · norm_num
              · exact (neg_le_abs _).trans hK_le
    have hexp : Real.exp (π * |w.im| / 2) ≤ Real.exp (π / 2) * Real.exp (π * |s.im| / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    calc ‖(Complex.Gamma w)⁻¹‖
        ≤ C₁ * (1 + |w.im|) ^ (1 / 2 - w.re) * Real.exp (π * |w.im| / 2) := by
          refine (hC₀ w hwre).trans ?_
          gcongr
          exact le_max_left C₀ 0
      _ ≤ C₁ * ((2 : ℝ) ^ K * (1 + |s.im|) ^ (3 / 2 - s.re)) *
            (Real.exp (π / 2) * Real.exp (π * |s.im| / 2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hrpow (le_max_right C₀ 0)) hexp
            (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  simpa using Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hent.diffContOnCl hbound

end TauCeti
