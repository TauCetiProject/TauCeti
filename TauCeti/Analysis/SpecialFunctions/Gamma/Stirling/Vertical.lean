/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Stirling's formula on vertical strips

For every compact interval `[a, b]`,
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)`
uniformly for `σ ∈ [a, b]` as `|t| → ∞`, that is along `cocompact ℝ`
([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9), with the remainder of
[DLMF 5.11.1](https://dlmf.nist.gov/5.11.E1)). The statement is additive in `log ‖Γ‖`, so it adds
up over finite products of shifted Gamma factors. Exponentiating and combining with compactness on
bounded imaginary parts gives uniform norm bounds for `Γ` away from the real axis, on any
pole-free vertical line, and for the entire reciprocal `Γ⁻¹` and its derivative across the whole
strip.

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
* `TauCeti.exists_norm_Gamma_vertical_strip_le`: uniform upper bound
  `C (1 + |Im s|) ^ (b - 1/2) exp (-π |Im s| / 2)` on `Re s ∈ [a, b]` and `δ ≤ |Im s|`.
* `TauCeti.exists_norm_Gamma_vertical_line_le`: uniform upper bound
  `C (1 + |t|) ^ (σ - 1/2) exp (-π |t| / 2)` on any vertical line avoiding the poles of `Γ`.
* `TauCeti.exists_norm_inv_Gamma_vertical_strip_le`,
  `TauCeti.exists_norm_deriv_inv_Gamma_vertical_strip_le`: uniform upper bounds for `‖(Γ s)⁻¹‖`
  and `‖deriv (Γ ·)⁻¹ s‖` across the whole strip `Re s ∈ [a, b]`.
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

/-- For `t ≥ 1` and any real exponent `p`, replacing `log t` by `log (1 + t)` changes `p log t` by
at most `|p| log 2`. -/
private lemma mul_log_le_mul_log_one_add (p : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    p * Real.log t ≤ p * Real.log (1 + t) + |p| * Real.log 2 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlo : Real.log t ≤ Real.log (1 + t) := Real.log_le_log ht0 (by linarith)
  have hhi : Real.log (1 + t) - Real.log t ≤ Real.log 2 := by
    have h1 : Real.log (1 + t) ≤ Real.log (2 * t) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_mul two_ne_zero ht0.ne'] at h1
    linarith
  have habs : |Real.log t - Real.log (1 + t)| ≤ Real.log 2 := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hlo)]
    exact hhi
  have hmul : p * (Real.log t - Real.log (1 + t)) ≤ |p| * Real.log 2 :=
    (le_abs_self _).trans <| by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left habs (abs_nonneg p)
  linarith

/-- If `u, v ≥ 0` differ by at most `1`, then `(1 + u) ^ p ≤ 2 ^ |p| * (1 + v) ^ p` for every real
exponent `p`. -/
private lemma one_add_rpow_le_two_rpow_abs_mul (p : ℝ) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (huv : |u - v| ≤ 1) :
    (1 + u) ^ p ≤ 2 ^ |p| * (1 + v) ^ p := by
  obtain ⟨h1, h2⟩ := abs_le.mp huv
  rcases le_total 0 p with hp | hp
  · calc (1 + u) ^ p ≤ (2 * (1 + v)) ^ p :=
            Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ = 2 ^ |p| * (1 + v) ^ p := by
            rw [Real.mul_rpow zero_le_two (by positivity), abs_of_nonneg hp]
  · calc (1 + u) ^ p ≤ ((1 + v) * (2 : ℝ)⁻¹) ^ p :=
            Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hp
      _ = 2 ^ |p| * (1 + v) ^ p := by
            rw [Real.mul_rpow (by positivity) (by positivity),
              Real.inv_rpow zero_le_two, ← Real.rpow_neg zero_le_two, abs_of_nonpos hp, mul_comm]

/-- Uniform upper bound for `‖Γ(s)‖` on a vertical strip `a ≤ Re s ≤ b` away from the real axis:
for every `δ > 0`, `‖Γ(s)‖ ≤ C (1 + |Im s|) ^ (b - 1/2) exp (-π |Im s| / 2)` for all `s` with
`Re s ∈ [a, b]` and `δ ≤ |Im s|`. -/
theorem exists_norm_Gamma_vertical_strip_le (a b : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b → δ ≤ |s.im| →
      ‖Complex.Gamma s‖ ≤ C * (1 + |s.im|) ^ (b - 1 / 2) * Real.exp (-(π * |s.im| / 2)) := by
  obtain ⟨C₀, T₀, hS⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  set T : ℝ := max (max T₀ 1) δ
  have hT1 : 1 ≤ T := (le_max_right T₀ 1).trans (le_max_left _ δ)
  let w : ℂ → ℝ := fun s ↦ (1 + |s.im|) ^ (b - 1 / 2) * Real.exp (-(π * |s.im| / 2))
  have hw_pos (s : ℂ) : 0 < w s := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  -- Compactness handles the bounded band `δ ≤ |Im s| ≤ T`.
  let K : Set ℂ := ((fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * I) '' (Icc a b ×ˢ Icc (-T) T)) ∩
    {s : ℂ | δ ≤ |s.im|}
  have hK : IsCompact K := ((isCompact_Icc.prod isCompact_Icc).image (by fun_prop)).inter_right
    (isClosed_le continuous_const (continuous_abs.comp continuous_im))
  have hcont : ContinuousOn (fun s : ℂ ↦ Complex.Gamma s / (w s : ℂ)) K := by
    intro s hs
    have him0 : s.im ≠ 0 := abs_pos.mp (hδ.trans_le hs.2)
    have hΓ : ContinuousAt Complex.Gamma s :=
      (Complex.differentiableAt_Gamma s fun m hm ↦ him0 (by simp [hm])).continuousAt
    have hw_cont : Continuous fun z : ℂ ↦ (w z : ℂ) := by
      refine continuous_ofReal.comp ?_
      exact ((continuous_const.add (continuous_abs.comp continuous_im)).rpow_const fun z ↦
        Or.inl (add_pos_of_pos_of_nonneg one_pos (abs_nonneg z.im)).ne').mul (by fun_prop)
    exact (hΓ.div hw_cont.continuousAt (ofReal_ne_zero.mpr (hw_pos s).ne')).continuousWithinAt
  obtain ⟨C_mid, hC_mid⟩ := hK.exists_bound_of_continuousOn hcont
  set C₁ : ℝ := Real.exp (|b - 1 / 2| * Real.log 2 + Real.log (2 * π) / 2 + |C₀|)
  refine ⟨max (max C₁ C_mid) 1, by positivity, fun s hs him ↦ ?_⟩
  rcases le_or_gt |s.im| T with hle | hgt
  · have hsK : s ∈ K :=
      ⟨⟨(s.re, s.im), ⟨hs, abs_le.mp hle⟩, re_add_im s⟩, him⟩
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
    have hlog_im : 0 ≤ Real.log |s.im| := Real.log_nonneg ht1
    have hre_le : (s.re - 1 / 2) * Real.log |s.im| ≤ (b - 1 / 2) * Real.log |s.im| :=
      mul_le_mul_of_nonneg_right (by linarith [hs.2]) hlog_im
    have herr : C₀ / |s.im| ≤ |C₀| :=
      (div_le_div_of_nonneg_right (le_abs_self C₀) (by positivity)).trans
        (div_le_self (abs_nonneg C₀) ht1)
    have hexp_le : Real.log ‖Complex.Gamma s‖ ≤
        (|b - 1 / 2| * Real.log 2 + Real.log (2 * π) / 2 + |C₀|) +
          (b - 1 / 2) * Real.log (1 + |s.im|) + (-(π * |s.im| / 2)) := by
      linarith [mul_log_le_mul_log_one_add (b - 1 / 2) ht1]
    calc ‖Complex.Gamma s‖ = Real.exp (Real.log ‖Complex.Gamma s‖) := (Real.exp_log hΓ0).symm
      _ ≤ Real.exp ((|b - 1 / 2| * Real.log 2 + Real.log (2 * π) / 2 + |C₀|) +
            (b - 1 / 2) * Real.log (1 + |s.im|) + (-(π * |s.im| / 2))) :=
          Real.exp_le_exp.mpr hexp_le
      _ = C₁ * (1 + |s.im|) ^ (b - 1 / 2) * Real.exp (-(π * |s.im| / 2)) := by
          rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos (by positivity),
            mul_comm (Real.log _)]
      _ ≤ max (max C₁ C_mid) 1 * (1 + |s.im|) ^ (b - 1 / 2) * Real.exp (-(π * |s.im| / 2)) := by
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
  have hcont : ContinuousOn (fun t : ℝ ↦ Complex.Gamma (σ + t * I) / (w t : ℂ)) (Icc (-1) 1) := by
    intro t _
    have hΓ : ContinuousAt (fun t : ℝ ↦ Complex.Gamma (σ + t * I)) t := by
      refine (Complex.differentiableAt_Gamma _ fun m hm ↦ hσ m ?_).continuousAt.comp (by fun_prop)
      simpa using congrArg Complex.re hm
    have hw_cont : Continuous fun u : ℝ ↦ (w u : ℂ) := by
      refine continuous_ofReal.comp ?_
      exact ((continuous_const.add continuous_abs).rpow_const fun u ↦
        Or.inl (add_pos_of_pos_of_nonneg one_pos (abs_nonneg u)).ne').mul (by fun_prop)
    exact (hΓ.div hw_cont.continuousAt (ofReal_ne_zero.mpr (hw_pos t).ne')).continuousWithinAt
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), fun t ↦ ?_⟩
  rcases le_or_gt |t| 1 with ht | ht
  · have hbnd := hC₂ t (abs_le.mp ht)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hw_pos t).le,
      div_le_iff₀ (hw_pos t)] at hbnd
    simpa only [w, mul_assoc] using hbnd.trans
      (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (hw_pos t).le)
  · have hbnd := htail (σ + t * I) (by simp) (by simpa using ht.le)
    have him : ((σ : ℂ) + t * I).im = t := by simp
    rw [him] at hbnd
    exact hbnd.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (by positivity)) (Real.exp_pos _).le)

/-- Uniform upper bound for the reciprocal Gamma function across an entire vertical strip
`a ≤ Re s ≤ b` (including at poles, where `(Γ s)⁻¹ = 0`):
`‖(Γ s)⁻¹‖ ≤ C (1 + |Im s|) ^ (1/2 - a) exp (π |Im s| / 2)`. -/
theorem exists_norm_inv_Gamma_vertical_strip_le (a b : ℝ) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * (1 + |s.im|) ^ (1 / 2 - a) * Real.exp (π * |s.im| / 2) := by
  obtain ⟨C₀, T₀, hS⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  set T : ℝ := max T₀ 1
  have hT1 : 1 ≤ T := le_max_right T₀ 1
  let w : ℂ → ℝ := fun s ↦ (1 + |s.im|) ^ (1 / 2 - a) * Real.exp (π * |s.im| / 2)
  have hw_pos (s : ℂ) : 0 < w s := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  let K : Set ℂ := (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + p.2 * I) '' (Icc a b ×ˢ Icc (-T) T)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : ContinuousOn (fun s : ℂ ↦ (Complex.Gamma s)⁻¹ / (w s : ℂ)) K := by
    intro s _
    have hw_cont : Continuous fun z : ℂ ↦ (w z : ℂ) := by
      refine continuous_ofReal.comp ?_
      exact ((continuous_const.add (continuous_abs.comp continuous_im)).rpow_const fun z ↦
        Or.inl (add_pos_of_pos_of_nonneg one_pos (abs_nonneg z.im)).ne').mul (by fun_prop)
    exact (Complex.differentiable_one_div_Gamma.continuous.continuousAt.div hw_cont.continuousAt
      (ofReal_ne_zero.mpr (hw_pos s).ne')).continuousWithinAt
  obtain ⟨C_mid, hC_mid⟩ := hK.exists_bound_of_continuousOn hcont
  set C₁ : ℝ := Real.exp (|1 / 2 - a| * Real.log 2 - Real.log (2 * π) / 2 + |C₀|)
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
    have hlog_im : 0 ≤ Real.log |s.im| := Real.log_nonneg ht1
    have hre_ge : (a - 1 / 2) * Real.log |s.im| ≤ (s.re - 1 / 2) * Real.log |s.im| :=
      mul_le_mul_of_nonneg_right (by linarith [hs.1]) hlog_im
    have herr : C₀ / |s.im| ≤ |C₀| :=
      (div_le_div_of_nonneg_right (le_abs_self C₀) (by positivity)).trans
        (div_le_self (abs_nonneg C₀) ht1)
    have hexp_le : -Real.log ‖Complex.Gamma s‖ ≤
        (|1 / 2 - a| * Real.log 2 - Real.log (2 * π) / 2 + |C₀|) +
          (1 / 2 - a) * Real.log (1 + |s.im|) + π * |s.im| / 2 := by
      linarith [mul_log_le_mul_log_one_add (1 / 2 - a) ht1]
    calc ‖(Complex.Gamma s)⁻¹‖
        = Real.exp (-Real.log ‖Complex.Gamma s‖) := by
            rw [norm_inv, Real.exp_neg, Real.exp_log hΓ0]
      _ ≤ Real.exp ((|1 / 2 - a| * Real.log 2 - Real.log (2 * π) / 2 + |C₀|) +
            (1 / 2 - a) * Real.log (1 + |s.im|) + π * |s.im| / 2) :=
          Real.exp_le_exp.mpr hexp_le
      _ = C₁ * (1 + |s.im|) ^ (1 / 2 - a) * Real.exp (π * |s.im| / 2) := by
          rw [Real.exp_add, Real.exp_add, Real.rpow_def_of_pos (by positivity),
            mul_comm (Real.log _)]
      _ ≤ max (max C₁ C_mid) 1 * (1 + |s.im|) ^ (1 / 2 - a) * Real.exp (π * |s.im| / 2) := by
          gcongr
          exact (le_max_left C₁ C_mid).trans (le_max_left _ 1)

/-- Uniform upper bound for the derivative of the entire function `z ↦ (Γ z)⁻¹` across a vertical
strip `a ≤ Re s ≤ b`, deduced from `exists_norm_inv_Gamma_vertical_strip_le` on `[a - 1, b + 1]`
by Cauchy's estimate on unit circles:
`‖deriv (Γ ·)⁻¹ s‖ ≤ C (1 + |Im s|) ^ (3/2 - a) exp (π |Im s| / 2)`. -/
theorem exists_norm_deriv_inv_Gamma_vertical_strip_le (a b : ℝ) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖deriv (fun z : ℂ ↦ (Complex.Gamma z)⁻¹) s‖ ≤
        C * (1 + |s.im|) ^ (3 / 2 - a) * Real.exp (π * |s.im| / 2) := by
  obtain ⟨C₀, hC₀, hbnd⟩ := exists_norm_inv_Gamma_vertical_strip_le (a - 1) (b + 1)
  refine ⟨C₀ * 2 ^ |3 / 2 - a| * Real.exp (π / 2), by positivity, fun s hs ↦ ?_⟩
  have hdiff : DiffContOnCl ℂ (fun z : ℂ ↦ (Complex.Gamma z)⁻¹) (Metric.ball s 1) :=
    Complex.differentiable_one_div_Gamma.diffContOnCl
  have hsphere : ∀ z ∈ Metric.sphere s 1, ‖(Complex.Gamma z)⁻¹‖ ≤
      C₀ * 2 ^ |3 / 2 - a| * Real.exp (π / 2) * (1 + |s.im|) ^ (3 / 2 - a) *
        Real.exp (π * |s.im| / 2) := by
    intro z hz
    have hzs : ‖z - s‖ = 1 := mem_sphere_iff_norm.mp hz
    have hre_diff : |z.re - s.re| ≤ 1 := by
      simpa only [← sub_re, hzs] using abs_re_le_norm (z - s)
    have him_diff : |(|z.im| - |s.im|)| ≤ 1 :=
      (abs_abs_sub_abs_le_abs_sub z.im s.im).trans <| by
        simpa only [← sub_im, hzs] using abs_im_le_norm (z - s)
    have hz_re : z.re ∈ Icc (a - 1) (b + 1) := by
      obtain ⟨h1, h2⟩ := abs_le.mp hre_diff
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hz_bnd := hbnd z hz_re
    have hexp_eq : (1 : ℝ) / 2 - (a - 1) = 3 / 2 - a := by ring
    rw [hexp_eq] at hz_bnd
    have hrpow := one_add_rpow_le_two_rpow_abs_mul (3 / 2 - a) (abs_nonneg z.im) (abs_nonneg s.im)
      him_diff
    have hexp : Real.exp (π * |z.im| / 2) ≤ Real.exp (π / 2) * Real.exp (π * |s.im| / 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hz_im : |z.im| ≤ 1 + |s.im| := by linarith [(abs_le.mp him_diff).2]
      nlinarith [Real.pi_pos]
    calc ‖(Complex.Gamma z)⁻¹‖
        ≤ C₀ * (1 + |z.im|) ^ (3 / 2 - a) * Real.exp (π * |z.im| / 2) := hz_bnd
      _ ≤ C₀ * (2 ^ |3 / 2 - a| * (1 + |s.im|) ^ (3 / 2 - a)) *
            (Real.exp (π / 2) * Real.exp (π * |s.im| / 2)) := by
          gcongr
      _ = C₀ * 2 ^ |3 / 2 - a| * Real.exp (π / 2) * (1 + |s.im|) ^ (3 / 2 - a) *
            Real.exp (π * |s.im| / 2) := by ring
  simpa only [div_one] using
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le zero_lt_one hdiff hsphere

end TauCeti
