/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Basic
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
* `Complex.continuous_Gamma_add_mul_I`, `Complex.continuous_Gamma_sub_mul_I`,
  `Complex.exists_norm_Gamma_add_mul_I_le_mul_exp`,
  `Complex.exists_norm_Gamma_sub_mul_I_le_mul_exp`: continuity and `C exp (-c |t|)` bounds (for
  every `c < π / 2`) of `t ↦ Γ(w ± i t)` on any vertical line avoiding `-ℕ`.
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

end TauCeti

namespace Complex

/-- Along any vertical line avoiding `-ℕ`, `t ↦ Γ(w + i t)` is continuous. -/
theorem continuous_Gamma_add_mul_I {w : ℂ} (hw : ∀ n : ℕ, w.re ≠ -n) :
    Continuous fun t : ℝ ↦ Gamma (w + t * I) := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  refine (differentiableAt_Gamma _ fun m hm ↦ hw m ?_).continuousAt.comp (by fun_prop)
  simpa using congrArg re hm

/-- Along any vertical line avoiding `-ℕ`, `t ↦ Γ(w - i t)` is continuous. -/
theorem continuous_Gamma_sub_mul_I {w : ℂ} (hw : ∀ n : ℕ, w.re ≠ -n) :
    Continuous fun t : ℝ ↦ Gamma (w - t * I) := by
  have hsub : (fun t : ℝ ↦ Gamma (w - t * I)) = fun t : ℝ ↦ Gamma (w + ((-t : ℝ) : ℂ) * I) := by
    ext t; simp [sub_eq_add_neg]
  rw [hsub]
  exact (continuous_Gamma_add_mul_I hw).comp continuous_neg

/-- On a vertical line avoiding the poles of the Gamma function, `‖Γ(w + i t)‖` is bounded by a
constant multiple of `exp (-c |t|)` for every exponent `c < π / 2`: Stirling's vertical-strip
formula controls large `|Im (w + i t)|`, and continuity of `Γ` away from `-ℕ` controls the compact
middle interval. -/
theorem exists_norm_Gamma_add_mul_I_le_mul_exp {w : ℂ} (hw : ∀ n : ℕ, w.re ≠ -n)
    {c : ℝ} (hc : c < π / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖Gamma (w + t * I)‖ ≤ C * Real.exp (-c * |t|) := by
  obtain ⟨K, T₀, hSt⟩ := TauCeti.exists_abs_log_norm_Gamma_vertical_sub_le w.re w.re
  set T : ℝ := max T₀ 1
  set ε : ℝ := π / 2 - c
  have hε : 0 < ε := sub_pos.mpr hc
  set A : ℝ := |w.re - 1 / 2| + 1
  have hA : 0 < A := by positivity
  set δ : ℝ := ε / A
  have hδ : 0 < δ := div_pos hε hA
  set B : ℝ := -(A * Real.log δ) + Real.log (2 * π) / 2 + |K| + |c| * |w.im|
  -- Outside the compact interval `|w.im + t| ≤ T`, Stirling's bound absorbs
  -- `(w.re - 1/2) log |s.im|` into `ε |s.im|` using `log (δ u) ≤ δ u - 1`.
  have htail : ∀ t : ℝ, T ≤ |w.im + t| →
      ‖Gamma (w + t * I)‖ ≤ Real.exp B * Real.exp (-c * |t|) := by
    intro t ht
    set s : ℂ := w + t * I
    have hs_re : s.re = w.re := by simp [s]
    have hs_im : s.im = w.im + t := by simp [s]
    set u : ℝ := |s.im|
    have hTu : T ≤ u := by simpa [u, hs_im] using ht
    have hT₀u : T₀ ≤ u := (le_max_left T₀ 1).trans hTu
    have hu1 : 1 ≤ u := (le_max_right T₀ 1).trans hTu
    have hu0 : 0 < u := zero_lt_one.trans_le hu1
    rcases (norm_nonneg (Gamma s)).eq_or_lt with h0 | hpos
    · rw [← h0]
      positivity
    have hlogSt : Real.log ‖Gamma s‖ -
        ((w.re - 1 / 2) * Real.log u - π * u / 2 + Real.log (2 * π) / 2) ≤ K / u := by
      have h := (abs_le.mp (hSt s ⟨hs_re.ge, hs_re.le⟩ hT₀u)).2
      rwa [hs_re] at h
    have hKu : K / u ≤ |K| :=
      (div_le_div_of_nonneg_right (le_abs_self K) hu0.le).trans (div_le_self (abs_nonneg K) hu1)
    have hlog_u : Real.log u ≤ δ * u - Real.log δ := by
      have h1 := Real.log_le_sub_one_of_pos (mul_pos hδ hu0)
      rw [Real.log_mul hδ.ne' hu0.ne'] at h1
      linarith
    have hmod : (w.re - 1 / 2) * Real.log u ≤ ε * u - A * Real.log δ := by
      calc (w.re - 1 / 2) * Real.log u
          ≤ A * Real.log u :=
            mul_le_mul_of_nonneg_right (by linarith [le_abs_self (w.re - 1 / 2)])
              (Real.log_nonneg hu1)
        _ ≤ A * (δ * u - Real.log δ) := mul_le_mul_of_nonneg_left hlog_u hA.le
        _ = ε * u - A * Real.log δ := by
            have hAδ : A * δ = ε := mul_div_cancel₀ ε hA.ne'
            linear_combination u * hAδ
    have hshift : -c * u ≤ -c * |t| + |c| * |w.im| := by
      have habs : |(|t| - u)| ≤ |w.im| := by
        have h := abs_abs_sub_abs_le t (w.im + t)
        rwa [abs_sub_comm t (w.im + t), add_sub_cancel_right, ← hs_im] at h
      have hc_diff : c * (|t| - u) ≤ |c| * |w.im| :=
        (le_abs_self _).trans
          ((abs_mul c (|t| - u)).le.trans (mul_le_mul_of_nonneg_left habs (abs_nonneg c)))
      linarith
    have hlog_le : Real.log ‖Gamma s‖ ≤ B + (-c * |t|) := by
      have hεu : ε * u - π * u / 2 = -c * u := by dsimp [ε]; ring
      dsimp only [B]
      linarith
    rw [← Real.exp_log hpos, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hlog_le
  -- On the compact middle interval `|w.im + t| ≤ T`, `t ↦ ‖Γ(w + i t)‖ exp (c |t|)` is continuous.
  set g : ℝ → ℝ := fun t ↦ ‖Gamma (w + t * I)‖ * Real.exp (c * |t|)
  have hg_cont : Continuous g := (continuous_Gamma_add_mul_I hw).norm.mul (by fun_prop)
  obtain ⟨C₁, hC₁⟩ :=
    (isCompact_Icc (a := -w.im - T) (b := -w.im + T)).exists_bound_of_continuousOn
      hg_cont.continuousOn
  set C : ℝ := max (max C₁ 1) (Real.exp B)
  have hC : 0 < C := lt_of_lt_of_le one_pos ((le_max_right C₁ 1).trans (le_max_left _ _))
  refine ⟨C, hC, fun t ↦ ?_⟩
  rcases le_or_gt T |w.im + t| with ht | ht
  · exact (htail t ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  · have htJ : t ∈ Icc (-w.im - T) (-w.im + T) := by
      obtain ⟨h1, h2⟩ := abs_lt.mp ht
      exact ⟨by linarith, by linarith⟩
    have hg_le : g t ≤ C :=
      (le_abs_self (g t)).trans
        ((Real.norm_eq_abs (g t) ▸ hC₁ t htJ).trans ((le_max_left C₁ 1).trans (le_max_left _ _)))
    calc ‖Gamma (w + t * I)‖
        = g t * Real.exp (-c * |t|) := by
          simp [g, mul_assoc, ← Real.exp_add]
      _ ≤ C * Real.exp (-c * |t|) :=
          mul_le_mul_of_nonneg_right hg_le (Real.exp_pos _).le

/-- On a vertical line avoiding the poles of the Gamma function, `‖Γ(w - i t)‖` is bounded by a
constant multiple of `exp (-c |t|)` for every exponent `c < π / 2`. -/
theorem exists_norm_Gamma_sub_mul_I_le_mul_exp {w : ℂ} (hw : ∀ n : ℕ, w.re ≠ -n)
    {c : ℝ} (hc : c < π / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖Gamma (w - t * I)‖ ≤ C * Real.exp (-c * |t|) := by
  obtain ⟨C, hC, h⟩ := exists_norm_Gamma_add_mul_I_le_mul_exp hw hc
  refine ⟨C, hC, fun t ↦ ?_⟩
  have hsub : w - (t : ℂ) * I = w + ((-t : ℝ) : ℂ) * I := by push_cast; ring
  simpa [hsub] using h (-t)

end Complex
