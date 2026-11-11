/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Stirling's formula on vertical strips

For every compact interval `[a, b]`,
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)`
uniformly for `σ ∈ [a, b]` as `|t| → ∞`, that is along `cocompact ℝ`
([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9), with the remainder of
[DLMF 5.11.1](https://dlmf.nist.gov/5.11.E1)). The statement is additive in `log ‖Γ‖`, so it adds
up over finite products of shifted Gamma factors.

The proof is the sector form `TauCeti.abs_log_norm_Gamma_sub_stirling_le` at the angle `π / 4`.
Once `|σ| ≤ |t|` the point `σ + i t` has `|arg| ≤ 3π/4`, and the sector main term
`(σ - 1/2) log ‖s‖ - t arg s - σ` differs from the vertical one by two terms of size `O(1 / |t|)`:

* `0 ≤ log ‖s‖ - log |t| ≤ |σ| / |t|`, since `|t| ≤ ‖s‖ ≤ |t| + |σ|`;
* for `t > 0`, `π / 2 - arg s = arctan (σ / t)`, and `|arctan x - x| ≤ |x| ^ 3`, so
  `t (π / 2 - arg s) - σ` is at most `σ ^ 2 / t` in absolute value.

Negative `t` reduces to positive `t` by `Γ(conj s) = conj (Γ s)`.

## Main declarations

* `TauCeti.abs_log_norm_Gamma_vertical_sub_le`: the explicit bound
  `(2 / (1 - cos (π / 4)) ^ 3 + |σ - 1/2| |σ| + σ ^ 2) / |t|` whenever `t ≠ 0` and `|σ| ≤ |t|`.
* `TauCeti.exists_abs_log_norm_Gamma_vertical_sub_le`: one constant and one threshold for all
  `σ ∈ [a, b]`.
* `TauCeti.isBigO_log_norm_Gamma_vertical`: the uniform `O(1 / |t|)` form along
  `𝓟 (Icc a b) ×ˢ cocompact ℝ`.
* `TauCeti.isBigO_log_norm_Gamma_vertical_line`: the same on a single vertical line, along
  `cocompact ℝ`.
-/

public section

open Complex Real Filter Set Asymptotics

namespace TauCeti

/-- `arctan x = x + O(|x| ^ 3)`, with constant `1`, from `|arctan' u - 1| ≤ u ^ 2`. -/
private theorem abs_arctan_sub_self_le (x : ℝ) : |Real.arctan x - x| ≤ |x| ^ 3 := by
  have hderiv : ∀ u ∈ Metric.closedBall (0 : ℝ) |x|, HasDerivWithinAt
      (fun u ↦ Real.arctan u - u) ((1 + u ^ 2)⁻¹ - 1) (Metric.closedBall 0 |x|) u :=
    fun u _ ↦ ((Real.hasDerivAt_arctan' u).sub (hasDerivAt_id u)).hasDerivWithinAt
  have hbound : ∀ u ∈ Metric.closedBall (0 : ℝ) |x|, ‖(1 + u ^ 2)⁻¹ - 1‖ ≤ |x| ^ 2 := by
    intro u hu
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hu
    have h1 : 0 < 1 + u ^ 2 := by positivity
    have heq : (1 + u ^ 2)⁻¹ - 1 = -(u ^ 2 / (1 + u ^ 2)) := by
      field_simp
      ring
    rw [heq, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
    calc u ^ 2 / (1 + u ^ 2) ≤ u ^ 2 := div_le_self (sq_nonneg u) (by nlinarith)
      _ = |u| ^ 2 := (sq_abs u).symm
      _ ≤ |x| ^ 2 := pow_le_pow_left₀ (abs_nonneg u) hu 2
  have h := (convex_closedBall (0 : ℝ) |x|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (x := 0) (y := x) hderiv hbound (Metric.mem_closedBall_self (abs_nonneg x)) (by simp)
  simpa [pow_succ] using h

/-- In the upper half-plane, `π / 2 - arg (σ + i t) = arctan (σ / t)`. -/
private theorem arctan_div_eq_pi_div_two_sub_arg {σ t : ℝ} (ht : 0 < t) :
    Real.arctan (σ / t) = π / 2 - arg (σ + t * I) := by
  have hre : ((σ : ℂ) + t * I).re = σ := by simp
  have him : ((σ : ℂ) + t * I).im = t := by simp
  have hpos : 0 < arg ((σ : ℂ) + t * I) := by
    refine (arg_nonneg_iff.mpr (by rw [him]; exact ht.le)).lt_of_ne (Ne.symm ?_)
    intro h
    rw [arg_eq_zero_iff, him] at h
    exact ht.ne' h.2
  have hlt : arg ((σ : ℂ) + t * I) < π := by
    refine (arg_le_pi _).lt_of_ne ?_
    intro h
    rw [arg_eq_pi_iff, him] at h
    exact ht.ne' h.2
  refine Real.arctan_eq_of_tan_eq ?_ ⟨by linarith, by linarith⟩
  rw [Real.tan_pi_div_two_sub, tan_arg, hre, him, inv_div]

/-- The explicit vertical bound in the upper half-plane. -/
private theorem abs_log_norm_Gamma_vertical_sub_le_of_pos {σ t : ℝ} (ht : 0 < t)
    (hσt : |σ| ≤ t) :
    |Real.log ‖Complex.Gamma (σ + t * I)‖ -
        ((σ - 1 / 2) * Real.log |t| - π * |t| / 2 + Real.log (2 * π) / 2)| ≤
      (2 / (1 - Real.cos (π / 4)) ^ 3 + |σ - 1 / 2| * |σ| + σ ^ 2) / |t| := by
  set s : ℂ := σ + t * I with hs_def
  set K : ℝ := 2 / (1 - Real.cos (π / 4)) ^ 3 with hK_def
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  rw [abs_of_pos ht]
  have hs0 : s ≠ 0 := fun h ↦ ht.ne' (by rw [← him, h, zero_im])
  have hts : t ≤ ‖s‖ := by simpa [him, abs_of_pos ht] using abs_im_le_norm s
  have hst : ‖s‖ ≤ |σ| + t := by simpa [hre, him, abs_of_pos ht] using norm_le_abs_re_add_abs_im s
  have hK : 0 ≤ K := div_nonneg zero_le_two (pow_nonneg (sub_nonneg.2 (Real.cos_le_one _)) 3)
  -- the angle
  set x : ℝ := σ / t with hx_def
  have hx1 : |x| ≤ 1 := by
    rw [hx_def, abs_div, abs_of_pos ht]
    exact div_le_one_of_le₀ hσt ht.le
  have harctan := arctan_div_eq_pi_div_two_sub_arg (σ := σ) ht
  have hatan_le : |Real.arctan x| ≤ π / 4 := by
    rw [← Real.arctan_one, abs_le, ← Real.arctan_neg]
    exact ⟨Real.arctan_mono (abs_le.1 hx1).1, Real.arctan_mono (abs_le.1 hx1).2⟩
  have harg : |s.arg| ≤ π - π / 4 := by
    have h : s.arg = π / 2 - Real.arctan x := by rw [harctan]; ring
    rw [h, abs_le]
    obtain ⟨h1, h2⟩ := abs_le.1 hatan_le
    constructor <;> linarith [Real.pi_pos]
  -- Stirling on the sector `|arg s| ≤ 3π/4`
  have hS := abs_log_norm_Gamma_sub_stirling_le (by positivity) (by linarith [Real.pi_pos])
    harg hs0
  rw [hre, him, ← div_div] at hS
  have hS' : K / ‖s‖ ≤ K / t := div_le_div_of_nonneg_left hK ht hts
  -- the modulus term
  have hlog0 : 0 ≤ Real.log ‖s‖ - Real.log t := sub_nonneg.2 (Real.log_le_log ht hts)
  have hlog1 : Real.log ‖s‖ - Real.log t ≤ |σ| / t := by
    rw [← Real.log_div (norm_ne_zero_iff.2 hs0) ht.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos (norm_pos_iff.2 hs0) ht)).trans ?_
    rw [div_sub_one ht.ne']
    exact div_le_div_of_nonneg_right (by linarith) ht.le
  have hA : |(σ - 1 / 2) * (Real.log ‖s‖ - Real.log t)| ≤ |σ - 1 / 2| * |σ| / t := by
    rw [abs_mul, abs_of_nonneg hlog0, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hlog1 (abs_nonneg _)
  -- the angle term
  have hB : |t * (Real.arctan x - x)| ≤ σ ^ 2 / t := by
    rw [abs_mul, abs_of_pos ht]
    have h3 : |x| ^ 3 ≤ |x| ^ 2 := pow_le_pow_of_le_one (abs_nonneg x) hx1 (by norm_num)
    have hx2 : t * |x| ^ 2 = σ ^ 2 / t := by
      rw [sq_abs, hx_def]
      field_simp
    calc t * |Real.arctan x - x| ≤ t * |x| ^ 2 :=
          mul_le_mul_of_nonneg_left ((abs_arctan_sub_self_le x).trans h3) ht.le
      _ = σ ^ 2 / t := hx2
  have hsplit : Real.log ‖Complex.Gamma s‖ -
      ((σ - 1 / 2) * Real.log t - π * t / 2 + Real.log (2 * π) / 2) =
      (Real.log ‖Complex.Gamma s‖ - ((σ - 1 / 2) * Real.log ‖s‖ - t * s.arg - σ +
        Real.log (2 * π) / 2)) + (σ - 1 / 2) * (Real.log ‖s‖ - Real.log t) +
      t * (Real.arctan x - x) := by
    have hσ : t * x = σ := by rw [hx_def]; field_simp
    have harg' : s.arg = π / 2 - Real.arctan x := by rw [harctan]; ring
    rw [harg']
    linear_combination hσ
  rw [hsplit, add_div, add_div]
  refine (abs_add_three _ _ _).trans ?_
  linarith [hS.trans hS']

/-- **Stirling's formula on vertical strips**, explicit form: for `t ≠ 0` and `|σ| ≤ |t|`,
`|log ‖Γ(σ + i t)‖ - ((σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2)| ≤
(2 / (1 - cos (π / 4)) ^ 3 + |σ - 1/2| |σ| + σ ^ 2) / |t|`. -/
theorem abs_log_norm_Gamma_vertical_sub_le {σ t : ℝ} (ht : t ≠ 0) (hσt : |σ| ≤ |t|) :
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

/-- Stirling's formula on vertical strips, with one constant and one threshold for the whole
strip `a ≤ σ ≤ b`: `|log ‖Γ(σ + i t)‖ - ((σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2)| ≤ C / |t|`
for `σ ∈ [a, b]` and `T ≤ |t|`. -/
theorem exists_abs_log_norm_Gamma_vertical_sub_le (a b : ℝ) :
    ∃ C T : ℝ, ∀ σ ∈ Icc a b, ∀ t : ℝ, T ≤ |t| →
      |Real.log ‖Complex.Gamma (σ + t * I)‖ -
          ((σ - 1 / 2) * Real.log |t| - π * |t| / 2 + Real.log (2 * π) / 2)| ≤ C / |t| := by
  set M := max |a| |b|
  refine ⟨2 / (1 - Real.cos (π / 4)) ^ 3 + (M + 1 / 2) * M + M ^ 2, M + 1,
    fun σ hσ t ht ↦ ?_⟩
  have hσM : |σ| ≤ M := abs_le_max_abs_abs hσ.1 hσ.2
  have hM : 0 ≤ M := (abs_nonneg σ).trans hσM
  have ht0 : 0 < |t| := by linarith
  refine (abs_log_norm_Gamma_vertical_sub_le (abs_pos.1 ht0) (by linarith)).trans ?_
  refine div_le_div_of_nonneg_right ?_ ht0.le
  have h1 : |σ - 1 / 2| ≤ M + 1 / 2 := by
    refine (abs_sub _ _).trans ?_
    norm_num
    linarith
  have h2 : |σ - 1 / 2| * |σ| ≤ (M + 1 / 2) * M :=
    mul_le_mul h1 hσM (abs_nonneg _) (by linarith)
  have h3 : σ ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg σ) hσM 2
  linarith

/-- **Stirling's formula on vertical strips** ([DLMF 5.11.9](https://dlmf.nist.gov/5.11.E9)):
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)` uniformly for
`σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gamma_vertical (a b : ℝ) :
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
  exact h p.1 hp.1 p.2 hp.2

/-- Stirling's formula on a single vertical line `Re s = σ`:
`log ‖Γ(σ + i t)‖ = (σ - 1/2) log |t| - π |t| / 2 + log (2π) / 2 + O(1 / |t|)` as `|t| → ∞`. -/
theorem isBigO_log_norm_Gamma_vertical_line (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gamma (σ + t * I)‖ -
        ((σ - 1 / 2) * Real.log |t| - π * |t| / 2 + Real.log (2 * π) / 2))
      =O[cocompact ℝ] fun t ↦ |t|⁻¹ :=
  (isBigO_log_norm_Gamma_vertical σ σ).comp_tendsto
    ((tendsto_principal.2 (Eventually.of_forall fun _ ↦ left_mem_Icc.2 le_rfl)).prodMk tendsto_id)

end TauCeti
