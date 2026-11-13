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

Exponentiating the logarithmic asymptotic and combining the tail with compactness near the real
axis gives global norm bounds for `Γ` on pole-free vertical lines and for the entire reciprocal
`1 / Γ` (together with its derivative, by Cauchy's estimate) on arbitrary closed vertical strips.

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
* `TauCeti.exists_norm_Gamma_vertical_strip_le`, `TauCeti.exists_norm_Gamma_vertical_line_le`,
  `TauCeti.exists_norm_Gamma_add_mul_I_le`, `TauCeti.exists_norm_Gamma_sub_mul_I_le`:
  exponential decay bounds `O((1 + |t|) ^ (σ - 1/2) e^{-π |t| / 2})` for `‖Γ‖` on vertical strips
  and pole-free vertical lines.
* `TauCeti.exists_norm_inv_Gamma_vertical_strip_le`,
  `TauCeti.exists_norm_inv_Gamma_add_mul_I_le`,
  `TauCeti.exists_norm_deriv_inv_Gamma_vertical_strip_le`: global exponential growth bounds
  `O((1 + |Im s|) ^ K e^{π |Im s| / 2})` for `‖(Γ s)⁻¹‖` and its derivative on vertical strips and
  lines.
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

/-- For `1 ≤ |t|` and any real exponent `r`, `|t| ^ r` is bounded by a constant multiple of
`(1 + |t|) ^ r`. -/
private theorem abs_rpow_le_mul_one_add_abs_rpow {t : ℝ} (ht : 1 ≤ |t|) (r : ℝ) :
    |t| ^ r ≤ max 1 (2 ^ (-r)) * (1 + |t|) ^ r := by
  have ht0 : 0 < |t| := zero_lt_one.trans_le ht
  have h1t : 0 < 1 + |t| := by linarith
  rcases le_or_gt 0 r with hr | hr
  · calc |t| ^ r ≤ (1 + |t|) ^ r := Real.rpow_le_rpow ht0.le (by linarith) hr
      _ ≤ max 1 (2 ^ (-r)) * (1 + |t|) ^ r :=
        le_mul_of_one_le_left (by positivity) (le_max_left _ _)
  · have hhalf : 2⁻¹ * (1 + |t|) ≤ |t| := by linarith
    calc |t| ^ r ≤ (2⁻¹ * (1 + |t|)) ^ r :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hhalf hr.le
      _ = 2 ^ (-r) * (1 + |t|) ^ r := by
          rw [Real.mul_rpow (by norm_num) h1t.le, Real.inv_rpow zero_le_two,
            ← Real.rpow_neg zero_le_two]
      _ ≤ max 1 (2 ^ (-r)) * (1 + |t|) ^ r := by
          gcongr
          exact le_max_right _ _

/-- Translating `y` by a constant `c` changes `(1 + |y|) ^ r` by at most a constant factor, for any
sign of the real exponent `r`. -/
private theorem one_add_abs_add_rpow_le (c y r : ℝ) :
    (1 + |c + y|) ^ r ≤ max ((1 + |c|) ^ r) ((1 + |c|) ^ (-r)) * (1 + |y|) ^ r := by
  have hc1 : 0 < 1 + |c| := by linarith [abs_nonneg c]
  have hy1 : 0 < 1 + |y| := by linarith [abs_nonneg y]
  have hcy1 : 0 < 1 + |c + y| := by linarith [abs_nonneg (c + y)]
  have hup : 1 + |c + y| ≤ (1 + |c|) * (1 + |y|) := by
    nlinarith [abs_add_le c y, abs_nonneg c, abs_nonneg y]
  have hlow : (1 + |c|)⁻¹ * (1 + |y|) ≤ 1 + |c + y| := by
    rw [inv_mul_le_iff₀ hc1]
    have htri : |y| ≤ |c + y| + |c| :=
      calc |y| = |(c + y) + (-c)| := by ring_nf
        _ ≤ |c + y| + |c| := by simpa only [abs_neg] using abs_add_le (c + y) (-c)
    nlinarith [abs_nonneg c, abs_nonneg (c + y)]
  rcases le_or_gt 0 r with hr | hr
  · calc (1 + |c + y|) ^ r ≤ ((1 + |c|) * (1 + |y|)) ^ r :=
          Real.rpow_le_rpow hcy1.le hup hr
      _ = (1 + |c|) ^ r * (1 + |y|) ^ r := Real.mul_rpow hc1.le hy1.le
      _ ≤ max ((1 + |c|) ^ r) ((1 + |c|) ^ (-r)) * (1 + |y|) ^ r := by
          gcongr
          exact le_max_left _ _
  · calc (1 + |c + y|) ^ r ≤ ((1 + |c|)⁻¹ * (1 + |y|)) ^ r :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlow hr.le
      _ = (1 + |c|) ^ (-r) * (1 + |y|) ^ r := by
          rw [Real.mul_rpow (by positivity) hy1.le, Real.inv_rpow hc1.le,
            ← Real.rpow_neg hc1.le]
      _ ≤ max ((1 + |c|) ^ r) ((1 + |c|) ^ (-r)) * (1 + |y|) ^ r := by
          gcongr
          exact le_max_right _ _

/-- Exponential decay of `‖Γ(s)‖` on a closed vertical strip `a ≤ Re s ≤ b` away from the real
axis: for `|Im s| ≥ T`, `‖Γ(s)‖ ≤ C |Im s| ^ (Re s - 1/2) e^{-π |Im s| / 2}`. -/
theorem exists_norm_Gamma_vertical_strip_le (a b : ℝ) :
    ∃ C > 0, ∃ T ≥ 1, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      ‖Complex.Gamma s‖ ≤ C * |s.im| ^ (s.re - 1 / 2) * Real.exp (-π * |s.im| / 2) := by
  obtain ⟨C₀, T₀, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  set C := max C₀ 0
  set T := max T₀ 1
  refine ⟨Real.exp (Real.log (2 * π) / 2 + C), Real.exp_pos _, T, le_max_right _ _,
    fun s hs ht ↦ ?_⟩
  have ht1 : 1 ≤ |s.im| := (le_max_right _ _).trans ht
  have ht0 : 0 < |s.im| := zero_lt_one.trans_le ht1
  have hs_ne : ∀ n : ℕ, s ≠ -n := fun n hn ↦ (abs_pos.1 ht0) (by simp [hn])
  have hΓ : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.2 (Complex.Gamma_ne_zero hs_ne)
  have hlog := (abs_le.1 (h s hs ((le_max_left _ _).trans ht))).2
  have hdiv : C₀ / |s.im| ≤ C := by
    calc C₀ / |s.im| ≤ C / |s.im| := div_le_div_of_nonneg_right (le_max_left _ _) ht0.le
      _ ≤ C / 1 := div_le_div_of_nonneg_left (le_max_right _ _) one_pos ht1
      _ = C := div_one C
  rw [← Real.exp_log hΓ, Real.rpow_def_of_pos ht0, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  linarith

/-- Global exponential decay of `‖Γ(σ + i t)‖` on any vertical line `Re s = σ` avoiding the
nonpositive integer poles of `Γ`:
`‖Γ(σ + i t)‖ ≤ C (1 + |t|) ^ (σ - 1/2) e^{-π |t| / 2}` for all `t : ℝ`. -/
theorem exists_norm_Gamma_vertical_line_le {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) :
    ∃ C > 0, ∀ t : ℝ,
      ‖Complex.Gamma (σ + t * I)‖ ≤
        C * (1 + |t|) ^ (σ - 1 / 2) * Real.exp (-π * |t| / 2) := by
  obtain ⟨C₁, hC₁, T, hT1, htail⟩ := exists_norm_Gamma_vertical_strip_le σ σ
  let w : ℝ → ℝ := fun t ↦ (1 + |t|) ^ (σ - 1 / 2) * Real.exp (-π * |t| / 2)
  have hw_pos (t : ℝ) : 0 < w t := by
    dsimp [w]
    positivity
  have hΓ_cont : Continuous fun t : ℝ ↦ Complex.Gamma (σ + t * I) :=
    continuous_iff_continuousAt.2 fun t ↦
      (Complex.differentiableAt_Gamma _ fun m hm ↦ hσ m (by simpa using congrArg re hm))
        |>.continuousAt.comp (by fun_prop)
  have hw_cont : Continuous w := by
    refine Continuous.mul ?_ (by fun_prop)
    exact Continuous.rpow_const (by fun_prop) fun t ↦
      Or.inl (show (0 : ℝ) < 1 + |t| by linarith [abs_nonneg t]).ne'
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-T) T) (hΓ_cont.norm.div hw_cont fun t ↦ (hw_pos t).ne').continuousOn
  set C₂ := C₁ * max 1 (2 ^ (-(σ - 1 / 2)))
  refine ⟨max (max M 0 + 1) C₂, lt_of_lt_of_le (by positivity) (le_max_left _ _), fun t ↦ ?_⟩
  rcases le_or_gt |t| T with ht | ht
  · have hMt := hM t (abs_le.1 ht)
    rw [Pi.div_apply, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos (hw_pos t),
      div_le_iff₀ (hw_pos t)] at hMt
    refine hMt.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right
      ((le_trans (le_max_left M 0) (by linarith)).trans (le_max_left _ _)) (hw_pos t).le
  · have hst := htail (σ + t * I) (by simp) (by simpa using ht.le)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at hst
    calc ‖Complex.Gamma (σ + t * I)‖
        ≤ C₁ * |t| ^ (σ - 1 / 2) * Real.exp (-π * |t| / 2) := hst
      _ ≤ C₁ * (max 1 (2 ^ (-(σ - 1 / 2))) * (1 + |t|) ^ (σ - 1 / 2)) *
            Real.exp (-π * |t| / 2) := by
          gcongr
          exact abs_rpow_le_mul_one_add_abs_rpow (hT1.trans ht.le) _
      _ = C₂ * w t := by dsimp [C₂, w]; ring
      _ ≤ max (max M 0 + 1) C₂ * w t :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (hw_pos t).le
      _ = max (max M 0 + 1) C₂ * (1 + |t|) ^ (σ - 1 / 2) * Real.exp (-π * |t| / 2) := by
          dsimp [w]; ring

/-- Global exponential decay of `‖Γ(z + i y)‖` along the vertical line through a complex shift `z`
whose real part avoids the nonpositive integers. -/
theorem exists_norm_Gamma_add_mul_I_le {z : ℂ} (hz : ∀ n : ℕ, z.re ≠ -n) :
    ∃ C > 0, ∀ y : ℝ,
      ‖Complex.Gamma (z + y * I)‖ ≤
        C * (1 + |y|) ^ (z.re - 1 / 2) * Real.exp (-π * |y| / 2) := by
  obtain ⟨C₀, hC₀, hline⟩ := exists_norm_Gamma_vertical_line_le hz
  set K := max ((1 + |z.im|) ^ (z.re - 1 / 2)) ((1 + |z.im|) ^ (-(z.re - 1 / 2)))
  have : 0 < K := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C₀ * K * Real.exp (π * |z.im| / 2), by positivity, fun y ↦ ?_⟩
  have hdecomp : z + y * I = (z.re : ℂ) + ((z.im + y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hexp : Real.exp (-π * |z.im + y| / 2) ≤
      Real.exp (π * |z.im| / 2) * Real.exp (-π * |y| / 2) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have htri : |y| ≤ |z.im + y| + |z.im| :=
      calc |y| = |(z.im + y) + (-z.im)| := by ring_nf
        _ ≤ |z.im + y| + |z.im| := by simpa only [abs_neg] using abs_add_le (z.im + y) (-z.im)
    nlinarith [Real.pi_pos]
  rw [hdecomp]
  calc ‖Complex.Gamma ((z.re : ℂ) + ((z.im + y : ℝ) : ℂ) * I)‖
      ≤ C₀ * (1 + |z.im + y|) ^ (z.re - 1 / 2) * Real.exp (-π * |z.im + y| / 2) :=
        hline (z.im + y)
    _ ≤ C₀ * (K * (1 + |y|) ^ (z.re - 1 / 2)) *
          (Real.exp (π * |z.im| / 2) * Real.exp (-π * |y| / 2)) := by
        refine mul_le_mul ?_ hexp (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left (one_add_abs_add_rpow_le z.im y (z.re - 1 / 2)) hC₀.le
    _ = C₀ * K * Real.exp (π * |z.im| / 2) *
          (1 + |y|) ^ (z.re - 1 / 2) * Real.exp (-π * |y| / 2) := by ring

/-- Global exponential decay of `‖Γ(z - i y)‖` along the vertical line through a complex shift `z`
whose real part avoids the nonpositive integers. -/
theorem exists_norm_Gamma_sub_mul_I_le {z : ℂ} (hz : ∀ n : ℕ, z.re ≠ -n) :
    ∃ C > 0, ∀ y : ℝ,
      ‖Complex.Gamma (z - y * I)‖ ≤
        C * (1 + |y|) ^ (z.re - 1 / 2) * Real.exp (-π * |y| / 2) := by
  obtain ⟨C, hC, h⟩ := exists_norm_Gamma_add_mul_I_le hz
  refine ⟨C, hC, fun y ↦ ?_⟩
  simpa [sub_eq_add_neg] using h (-y)

/-- Global vertical-strip bound for the entire reciprocal Gamma function: for every `a, b : ℝ`,
`‖(Γ(s))⁻¹‖ ≤ C (1 + |Im s|) ^ (1/2 - a) e^{π |Im s| / 2}` for all `s` with `Re s ∈ [a, b]`. -/
theorem exists_norm_inv_Gamma_vertical_strip_le (a b : ℝ) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * (1 + |s.im|) ^ (1 / 2 - a) * Real.exp (π * |s.im| / 2) := by
  obtain ⟨C₀, T₀, h⟩ := exists_abs_log_norm_Gamma_vertical_sub_le a b
  set C₁ := max C₀ 0
  set T := max T₀ 1
  let w : ℂ → ℝ := fun s ↦ (1 + |s.im|) ^ (1 / 2 - a) * Real.exp (π * |s.im| / 2)
  have hw_pos (s : ℂ) : 0 < w s := by
    dsimp [w]
    positivity
  have hinv_cont : Continuous fun s : ℂ ↦ (Complex.Gamma s)⁻¹ := by
    simpa only [one_div] using Complex.differentiable_one_div_Gamma.continuous
  have hw_cont : Continuous w := by
    refine Continuous.mul ?_ (by fun_prop)
    exact Continuous.rpow_const (by fun_prop) fun s ↦
      Or.inl (show (0 : ℝ) < 1 + |s.im| by linarith [abs_nonneg s.im]).ne'
  let K : Set ℂ := {s : ℂ | s.re ∈ Icc a b ∧ |s.im| ≤ T}
  have hK_compact : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_Icc.preimage continuous_re).inter
        (isClosed_le (continuous_abs.comp continuous_im) continuous_const)
    · refine isBounded_iff_forall_norm_le.2 ⟨max |a| |b| + T, fun s hs ↦ ?_⟩
      exact (norm_le_abs_re_add_abs_im s).trans
        (add_le_add (abs_le_max_abs_abs hs.1.1 hs.1.2) hs.2)
  obtain ⟨M, hM⟩ := hK_compact.exists_bound_of_continuousOn
    (hinv_cont.norm.div hw_cont fun s ↦ (hw_pos s).ne').continuousOn
  set C₂ := Real.exp (C₁ - Real.log (2 * π) / 2) * max 1 (2 ^ (-(1 / 2 - a)))
  refine ⟨max (max M 0 + 1) C₂, lt_of_lt_of_le (by positivity) (le_max_left _ _),
    fun s hs ↦ ?_⟩
  rcases le_or_gt |s.im| T with ht | ht
  · have hMs := hM s ⟨hs, ht⟩
    rw [Pi.div_apply, Real.norm_eq_abs, abs_div, abs_norm, abs_of_pos (hw_pos s),
      div_le_iff₀ (hw_pos s)] at hMs
    refine hMs.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right
      ((le_trans (le_max_left M 0) (by linarith)).trans (le_max_left _ _)) (hw_pos s).le
  · have ht1 : 1 ≤ |s.im| := (le_max_right _ _).trans ht.le
    have ht0 : 0 < |s.im| := zero_lt_one.trans_le ht1
    have hs_ne : ∀ n : ℕ, s ≠ -n := fun n hn ↦ (abs_pos.1 ht0) (by simp [hn])
    have hΓ : 0 < ‖Complex.Gamma s‖ := norm_pos_iff.2 (Complex.Gamma_ne_zero hs_ne)
    have hlog := (abs_le.1 (h s hs ((le_max_left _ _).trans ht.le))).1
    have hdiv : C₀ / |s.im| ≤ C₁ := by
      calc C₀ / |s.im| ≤ C₁ / |s.im| := div_le_div_of_nonneg_right (le_max_left _ _) ht0.le
        _ ≤ C₁ / 1 := div_le_div_of_nonneg_left (le_max_right _ _) one_pos ht1
        _ = C₁ := div_one C₁
    have hlog_ge : 0 ≤ Real.log |s.im| := Real.log_nonneg ht1
    have hre_le : (1 / 2 - s.re) * Real.log |s.im| ≤ (1 / 2 - a) * Real.log |s.im| :=
      mul_le_mul_of_nonneg_right (by linarith [hs.1]) hlog_ge
    have hexp_bound : ‖(Complex.Gamma s)⁻¹‖ ≤
        Real.exp (C₁ - Real.log (2 * π) / 2) * |s.im| ^ (1 / 2 - a) *
          Real.exp (π * |s.im| / 2) := by
      rw [norm_inv, ← Real.exp_log (inv_pos.2 hΓ), Real.log_inv, Real.rpow_def_of_pos ht0,
        ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      linarith
    calc ‖(Complex.Gamma s)⁻¹‖
        ≤ Real.exp (C₁ - Real.log (2 * π) / 2) * |s.im| ^ (1 / 2 - a) *
            Real.exp (π * |s.im| / 2) := hexp_bound
      _ ≤ Real.exp (C₁ - Real.log (2 * π) / 2) *
            (max 1 (2 ^ (-(1 / 2 - a))) * (1 + |s.im|) ^ (1 / 2 - a)) *
            Real.exp (π * |s.im| / 2) := by
          gcongr
          exact abs_rpow_le_mul_one_add_abs_rpow ht1 _
      _ = C₂ * w s := by dsimp [C₂, w]; ring
      _ ≤ max (max M 0 + 1) C₂ * w s :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (hw_pos s).le
      _ = max (max M 0 + 1) C₂ * (1 + |s.im|) ^ (1 / 2 - a) * Real.exp (π * |s.im| / 2) := by
          dsimp [w]; ring

/-- Global vertical-line bound for the entire reciprocal Gamma function at any complex shift
`z : ℂ`: `‖(Γ(z + i y))⁻¹‖ ≤ C (1 + |y|) ^ (1/2 - Re z) e^{π |y| / 2}` for all `y : ℝ`. -/
theorem exists_norm_inv_Gamma_add_mul_I_le (z : ℂ) :
    ∃ C > 0, ∀ y : ℝ,
      ‖(Complex.Gamma (z + y * I))⁻¹‖ ≤
        C * (1 + |y|) ^ (1 / 2 - z.re) * Real.exp (π * |y| / 2) := by
  obtain ⟨C₀, hC₀, hstrip⟩ := exists_norm_inv_Gamma_vertical_strip_le z.re z.re
  set r : ℝ := 1 / 2 - z.re
  set K : ℝ := max ((1 + |z.im|) ^ r) ((1 + |z.im|) ^ (-r))
  have : 0 < K := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C₀ * K * Real.exp (π * |z.im| / 2), by positivity, fun y ↦ ?_⟩
  have hre : (z + y * I).re ∈ Icc z.re z.re := by simp
  have him : (z + y * I).im = z.im + y := by simp
  have hexp : Real.exp (π * |z.im + y| / 2) ≤
      Real.exp (π * |z.im| / 2) * Real.exp (π * |y| / 2) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := abs_add_le z.im y
    nlinarith [Real.pi_pos]
  calc ‖(Complex.Gamma (z + y * I))⁻¹‖
      ≤ C₀ * (1 + |z.im + y|) ^ r * Real.exp (π * |z.im + y| / 2) := by
        simpa only [him] using hstrip (z + y * I) hre
    _ ≤ C₀ * (K * (1 + |y|) ^ r) * (Real.exp (π * |z.im| / 2) * Real.exp (π * |y| / 2)) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (one_add_abs_add_rpow_le z.im y r) hC₀.le)
          hexp (by positivity) (by positivity)
    _ = C₀ * K * Real.exp (π * |z.im| / 2) * (1 + |y|) ^ r * Real.exp (π * |y| / 2) := by ring

/-- Global vertical-strip bound for the derivative of the reciprocal Gamma function, deduced from
`TauCeti.exists_norm_inv_Gamma_vertical_strip_le` via Cauchy's estimate on unit disks. -/
theorem exists_norm_deriv_inv_Gamma_vertical_strip_le (a b : ℝ) :
    ∃ C > 0, ∀ s : ℂ, s.re ∈ Icc a b →
      ‖deriv (fun w : ℂ ↦ (Complex.Gamma w)⁻¹) s‖ ≤
        C * (1 + |s.im|) ^ (3 / 2 - a) * Real.exp (π * |s.im| / 2) := by
  obtain ⟨C₀, hC₀, hstrip⟩ := exists_norm_inv_Gamma_vertical_strip_le (a - 1) (b + 1)
  have hf : Differentiable ℂ fun w : ℂ ↦ (Complex.Gamma w)⁻¹ := by
    simpa only [one_div] using Complex.differentiable_one_div_Gamma
  set r : ℝ := 3 / 2 - a
  set K : ℝ := max (2 ^ r) (2 ^ (-r))
  have : 0 < K := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C₀ * K * Real.exp (π / 2), by positivity, fun s hs ↦ ?_⟩
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le one_pos hf.diffContOnCl
    (c := s)
    (C := C₀ * K * Real.exp (π / 2) * (1 + |s.im|) ^ r * Real.exp (π * |s.im| / 2))
    fun w hw ↦ ?_
  · simpa only [div_one] using hcauchy
  · rw [Metric.mem_sphere, dist_eq_norm] at hw
    have hw_re : |w.re - s.re| ≤ 1 := hw ▸ abs_re_le_norm (w - s)
    have hw_im : |w.im - s.im| ≤ 1 := hw ▸ abs_im_le_norm (w - s)
    have hre_mem : w.re ∈ Icc (a - 1) (b + 1) := by
      obtain ⟨h1, h2⟩ := abs_le.1 hw_re
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hr_eq : 1 / 2 - (a - 1) = r := by dsimp [r]; ring
    have h1 := hstrip w hre_mem
    rw [hr_eq] at h1
    have him_eq : w.im = (w.im - s.im) + s.im := by ring
    have hrpow : (1 + |w.im|) ^ r ≤ K * (1 + |s.im|) ^ r := by
      have h1s : 0 < 1 + |s.im| := by linarith [abs_nonneg s.im]
      have h1w : 0 < 1 + |w.im| := by linarith [abs_nonneg w.im]
      have hup : 1 + |w.im| ≤ 2 * (1 + |s.im|) := by
        have := abs_add_le (w.im - s.im) s.im
        rw [← him_eq] at this
        linarith [abs_nonneg s.im]
      have hlow : 2⁻¹ * (1 + |s.im|) ≤ 1 + |w.im| := by
        have htri : |s.im| ≤ |w.im| + |w.im - s.im| :=
          calc |s.im| = |w.im + (-(w.im - s.im))| := by ring_nf
            _ ≤ |w.im| + |w.im - s.im| := by
              simpa only [abs_neg] using abs_add_le w.im (-(w.im - s.im))
        linarith [abs_nonneg w.im]
      rcases le_or_gt 0 r with hr | hr
      · calc (1 + |w.im|) ^ r ≤ (2 * (1 + |s.im|)) ^ r := Real.rpow_le_rpow h1w.le hup hr
          _ = 2 ^ r * (1 + |s.im|) ^ r := Real.mul_rpow zero_le_two h1s.le
          _ ≤ K * (1 + |s.im|) ^ r := by gcongr; exact le_max_left _ _
      · calc (1 + |w.im|) ^ r ≤ (2⁻¹ * (1 + |s.im|)) ^ r :=
              Real.rpow_le_rpow_of_nonpos (by positivity) hlow hr.le
          _ = 2 ^ (-r) * (1 + |s.im|) ^ r := by
              rw [Real.mul_rpow (by norm_num) h1s.le, Real.inv_rpow zero_le_two,
                ← Real.rpow_neg zero_le_two]
          _ ≤ K * (1 + |s.im|) ^ r := by gcongr; exact le_max_right _ _
    have hexp : Real.exp (π * |w.im| / 2) ≤ Real.exp (π / 2) * Real.exp (π * |s.im| / 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have := abs_add_le (w.im - s.im) s.im
      rw [← him_eq] at this
      nlinarith [Real.pi_pos]
    calc ‖(Complex.Gamma w)⁻¹‖
        ≤ C₀ * (1 + |w.im|) ^ r * Real.exp (π * |w.im| / 2) := h1
      _ ≤ C₀ * (K * (1 + |s.im|) ^ r) * (Real.exp (π / 2) * Real.exp (π * |s.im| / 2)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hrpow hC₀.le) hexp (by positivity)
            (by positivity)
      _ = C₀ * K * Real.exp (π / 2) * (1 + |s.im|) ^ r * Real.exp (π * |s.im| / 2) := by ring

end TauCeti
