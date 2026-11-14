/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean

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
replacing `|t + Im μ|` by `|t|` in the linear exponential term shifts it by at most `π |Im μ| / 4`,
while the `σ`-dependent constant is bounded on `[a, b]`. This yields the additive `O(1)` vertical
strip asymptotics
$$\log \|\Gamma_{\mathbb{R}}(\sigma + i t + \mu)\| =
  -\frac{\pi}{4} |t| + \frac{\sigma + \operatorname{Re}\mu - 1}{2} \log |t| + O(1),$$
$$\log \|\Gamma_{\mathbb{C}}(\sigma + i t + \nu)\| =
  -\frac{\pi}{2} |t| + \left(\sigma + \operatorname{Re}\nu - \frac{1}{2}\right) \log |t| + O(1),$$
with explicit error bounds and height thresholds depending only on `a`, `b`, and an upper bound `M`
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

/-! ### Auxiliary filter and logarithm bounds -/

/-- When `x, y ≥ 1` differ by at most `M`, their logarithms also differ by at most `M`. -/
private theorem abs_log_sub_log_le_of_one_le {x y M : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxy : |x - y| ≤ M) : |Real.log x - Real.log y| ≤ M := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hyp : 0 < y := zero_lt_one.trans_le hy
  have hM : 0 ≤ M := (abs_nonneg _).trans hxy
  rcases le_total y x with hyx | hxy'
  · rw [abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hyp hyx)), ← Real.log_div hxp.ne' hyp.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hxp hyp)).trans ?_
    rw [div_sub_one hyp.ne', div_le_iff₀ hyp]
    have hsub : x - y ≤ M := (le_abs_self _).trans hxy
    nlinarith
  · rw [← abs_neg, neg_sub, abs_of_nonneg (sub_nonneg.2 (Real.log_le_log hxp hxy')),
      ← Real.log_div hyp.ne' hxp.ne']
    refine (Real.log_le_sub_one_of_pos (div_pos hyp hxp)).trans ?_
    rw [div_sub_one hxp.ne', div_le_iff₀ hxp]
    have hsub : y - x ≤ M := (neg_le_abs _).trans_eq' (by ring) |>.trans hxy
    nlinarith

private theorem isBigO_inv_vertical_of_exists {a b : ℝ} {g : ℝ × ℝ → ℝ}
    (h : ∃ C T : ℝ, ∀ p : ℝ × ℝ, p.1 ∈ Icc a b → T ≤ |p.2| → |g p| ≤ C / |p.2|) :
    g =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun p ↦ |p.2|⁻¹ := by
  obtain ⟨C, T, hCT⟩ := h
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ t : ℝ in cocompact ℝ, T ≤ |t| := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop T] with t ht
    rwa [Real.norm_eq_abs] at ht
  filter_upwards [(eventually_principal.2 fun _ hσ ↦ hσ).prod_mk hT] with p hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_abs, ← div_eq_mul_inv]
  exact hCT p hp.1 hp.2

private theorem isBigO_inv_vertical_strip_of_exists {a b : ℝ} {f : ℂ → ℝ}
    (h : ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| → |f s| ≤ C / |s.im|) :
    f =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun s ↦ |s.im|⁻¹ := by
  obtain ⟨C, T, hCT⟩ := h
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ s : ℂ in cocompact ℂ, T + max |a| |b| ≤ ‖s‖ :=
    (tendsto_norm_cocompact_atTop (E := ℂ)).eventually_ge_atTop _
  filter_upwards [hT.filter_mono inf_le_left,
    (eventually_principal.2 fun _ hs ↦ hs).filter_mono inf_le_right] with s hs hre
  have hM : |s.re| ≤ max |a| |b| := abs_le_max_abs_abs hre.1 hre.2
  have hnorm := norm_le_abs_re_add_abs_im s
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_abs, ← div_eq_mul_inv]
  exact hCT s hre (by linarith)

/-- Package a uniform vertical-strip bound `|g p| ≤ C` into
`=O[𝓟 (Icc a b) ×ˢ cocompact ℝ] 1`. -/
theorem isBigO_one_vertical_of_exists {a b : ℝ} {g : ℝ × ℝ → ℝ}
    (h : ∃ C T : ℝ, ∀ p : ℝ × ℝ, p.1 ∈ Icc a b → T ≤ |p.2| → |g p| ≤ C) :
    g =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, T, hCT⟩ := h
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ t : ℝ in cocompact ℝ, T ≤ |t| := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop T] with t ht
    rwa [Real.norm_eq_abs] at ht
  filter_upwards [(eventually_principal.2 fun _ hσ ↦ hσ).prod_mk hT] with p hp
  simpa using hCT p hp.1 hp.2

/-- Package a uniform vertical-strip bound `|f s| ≤ C` into
`=O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] 1`. -/
theorem isBigO_one_vertical_strip_of_exists {a b : ℝ} {f : ℂ → ℝ}
    (h : ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| → |f s| ≤ C) :
    f =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, T, hCT⟩ := h
  refine IsBigO.of_bound C ?_
  have hT : ∀ᶠ s : ℂ in cocompact ℂ, T + max |a| |b| ≤ ‖s‖ :=
    (tendsto_norm_cocompact_atTop (E := ℂ)).eventually_ge_atTop _
  filter_upwards [hT.filter_mono inf_le_left,
    (eventually_principal.2 fun _ hs ↦ hs).filter_mono inf_le_right] with s hs hre
  have hM : |s.re| ≤ max |a| |b| := abs_le_max_abs_abs hre.1 hre.2
  have hnorm := norm_le_abs_re_add_abs_im s
  simpa using hCT s hre (by linarith)

/-- Restrict a vertical-strip asymptotic along `𝓟 (Icc σ σ) ×ˢ cocompact ℝ` to the vertical line
`Re s = σ` along `cocompact ℝ`. -/
theorem isBigO_cocompact_of_vertical {σ : ℝ} {g h : ℝ × ℝ → ℝ}
    (hg : g =O[𝓟 (Icc σ σ) ×ˢ cocompact ℝ] h) :
    (fun t : ℝ ↦ g (σ, t)) =O[cocompact ℝ] fun t ↦ h (σ, t) := by
  have hσ : Tendsto (fun _ : ℝ ↦ σ) (cocompact ℝ) (𝓟 (Icc σ σ)) :=
    tendsto_principal.2 (Eventually.of_forall fun _ ↦ left_mem_Icc.2 le_rfl)
  exact hg.comp_tendsto (hσ.prodMk tendsto_id)

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
    rw [show s.re / 2 - 1 / 2 = (s.re - 1) / 2 by ring, abs_div, abs_two]
  have hrhs : (2 / (1 - Real.cos (π / 4)) ^ 3 + |s.re / 2 - 1 / 2| * (|s.re| / 2) +
        (s.re / 2) ^ 2) / (|s.im| / 2) =
      (4 / (1 - Real.cos (π / 4)) ^ 3 + |s.re - 1| * |s.re| / 2 + s.re ^ 2 / 2) / |s.im| := by
    rw [hsub_abs]
    field_simp
    ring
  rw [hdiff, ← hrhs]
  exact hS

/-- Uniform `O(1 / |Im s|)` bound for `log ‖Gammaℝ s‖` on a compact vertical strip `[a, b]`. -/
theorem exists_abs_log_norm_Gammaℝ_vertical_sub_le (a b : ℝ) :
    ∃ C T : ℝ, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Complex.Gammaℝ s‖ -
          (-π * |s.im| / 4 + (s.re - 1) / 2 * Real.log |s.im| +
            (Real.log 2 - (s.re - 1) * Real.log (2 * π)) / 2)| ≤
        C / |s.im| := by
  set B := max |a| |b|
  refine ⟨4 / (1 - Real.cos (π / 4)) ^ 3 + (B + 1) * B / 2 + B ^ 2 / 2, B + 1, fun s hs ht ↦ ?_⟩
  have hσB : |s.re| ≤ B := abs_le_max_abs_abs hs.1 hs.2
  have hB : 0 ≤ B := (abs_nonneg _).trans hσB
  have ht0 : 0 < |s.im| := by linarith
  refine (abs_log_norm_Gammaℝ_vertical_sub_le (abs_pos.1 ht0) (by linarith)).trans ?_
  refine div_le_div_of_nonneg_right ?_ ht0.le
  have h1 : |s.re - 1| ≤ B + 1 := by
    obtain ⟨hl, hu⟩ := abs_le.1 hσB
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have h2 : |s.re - 1| * |s.re| ≤ (B + 1) * B :=
    mul_le_mul h1 hσB (abs_nonneg _) (by linarith)
  have h3 : s.re ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hσB 2
  linarith

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
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun s ↦ |s.im|⁻¹ :=
  isBigO_inv_vertical_strip_of_exists (exists_abs_log_norm_Gammaℝ_vertical_sub_le a b)

/-- Stirling's formula for `Gammaℝ` on a single vertical line `Re s = σ`. -/
theorem isBigO_log_norm_Gammaℝ_vertical_line_sub (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gammaℝ (σ + t * I)‖ -
        (-π * |t| / 4 + (σ - 1) / 2 * Real.log |t| +
          (Real.log 2 - (σ - 1) * Real.log (2 * π)) / 2))
      =O[cocompact ℝ] fun t ↦ |t|⁻¹ :=
  isBigO_cocompact_of_vertical (isBigO_log_norm_Gammaℝ_vertical_sub σ σ)

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

/-- Uniform `O(1 / |Im s|)` bound for `log ‖Gammaℂ s‖` on a compact vertical strip `[a, b]`. -/
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
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun s ↦ |s.im|⁻¹ :=
  isBigO_inv_vertical_strip_of_exists (exists_abs_log_norm_Gammaℂ_vertical_sub_le a b)

/-- Stirling's formula for `Gammaℂ` on a single vertical line `Re s = σ`. -/
theorem isBigO_log_norm_Gammaℂ_vertical_line_sub (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gammaℂ (σ + t * I)‖ -
        (-π * |t| / 2 + (σ - 1 / 2) * Real.log |t| +
          Real.log 2 - (σ - 1 / 2) * Real.log (2 * π)))
      =O[cocompact ℝ] fun t ↦ |t|⁻¹ :=
  isBigO_cocompact_of_vertical (isBigO_log_norm_Gammaℂ_vertical_sub σ σ)

/-! ### Complex-shifted `Gammaℝ` and `Gammaℂ` on vertical strips (`O(1)` form) -/

/-- Bound the perturbation when replacing `w = s + μ` by `s` in the main Stirling terms of
`Gammaℝ` and dropping the bounded constant term `(log 2 - (w.re - 1) log (2π)) / 2`. -/
private theorem abs_Gammaℝ_shift_perturbation_le {s w : ℂ} {R M : ℝ} (hR : 0 ≤ R)
    (hwre1 : |w.re - 1| ≤ R + 1) (hwim1 : 1 ≤ |w.im|) (hsim1 : 1 ≤ |s.im|)
    (him_diff : |(|w.im| - |s.im|)| ≤ M) :
    |(-π * |w.im| / 4 - (-π * |s.im| / 4)) +
        ((w.re - 1) / 2 * (Real.log |w.im| - Real.log |s.im|) +
          (Real.log 2 - (w.re - 1) * Real.log (2 * π)) / 2)| ≤
      π * M / 4 + (R + 1) / 2 * M + (Real.log 2 + (R + 1) * Real.log (2 * π)) / 2 := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hlog2pi : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.two_le_pi])
  have hexp_diff : |-π * |w.im| / 4 - (-π * |s.im| / 4)| ≤ π * M / 4 := by
    rw [show -π * |w.im| / 4 - (-π * |s.im| / 4) = -(π / 4) * (|w.im| - |s.im|) by ring,
      abs_mul, abs_neg, abs_of_nonneg (by positivity)]
    nlinarith [Real.pi_pos]
  have hlog_diff : |(w.re - 1) / 2 * (Real.log |w.im| - Real.log |s.im|)| ≤ (R + 1) / 2 * M := by
    rw [abs_mul, abs_div, abs_two]
    exact mul_le_mul (div_le_div_of_nonneg_right hwre1 zero_le_two)
      (abs_log_sub_log_le_of_one_le hwim1 hsim1 him_diff) (abs_nonneg _) (by positivity)
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

private theorem abs_log_norm_Gammaℝ_vertical_sub_le_of_re_le {w : ℂ} {R : ℝ}
    (hwre : |w.re| ≤ R) (hwim : R + 1 ≤ |w.im|) :
    |Real.log ‖Complex.Gammaℝ w‖ -
        (-π * |w.im| / 4 + (w.re - 1) / 2 * Real.log |w.im| +
          (Real.log 2 - (w.re - 1) * Real.log (2 * π)) / 2)| ≤
      4 / (1 - Real.cos (π / 4)) ^ 3 + (R + 1) * R / 2 + R ^ 2 / 2 := by
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hwre
  have hwim_pos : 0 < |w.im| := by linarith
  have hwre1 : |w.re - 1| ≤ R + 1 := abs_le.2
    ⟨by linarith [(abs_le.1 hwre).1], by linarith [(abs_le.1 hwre).2]⟩
  have hS := abs_log_norm_Gammaℝ_vertical_sub_le (s := w) (abs_pos.1 hwim_pos) (by linarith)
  refine hS.trans ((div_le_iff₀ hwim_pos).2 ?_)
  have h2 : |w.re - 1| * |w.re| ≤ (R + 1) * R :=
    mul_le_mul hwre1 hwre (abs_nonneg _) (by positivity)
  have h3 : w.re ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hwre 2
  have hK_le : 4 / (1 - Real.cos (π / 4)) ^ 3 + |w.re - 1| * |w.re| / 2 + w.re ^ 2 / 2 ≤
      4 / (1 - Real.cos (π / 4)) ^ 3 + (R + 1) * R / 2 + R ^ 2 / 2 := by linarith
  have : 0 ≤ 4 / (1 - Real.cos (π / 4)) ^ 3 + (R + 1) * R / 2 + R ^ 2 / 2 := by
    have : 0 ≤ 1 - Real.cos (π / 4) := sub_nonneg.2 (Real.cos_le_one _)
    positivity
  exact hK_le.trans (le_mul_of_one_le_right this (by linarith))

/-- Uniform `O(1)` vertical-strip bound for `log ‖Gammaℝ (s + μ)‖` across all shifts `μ` with
`‖μ‖ ≤ M`: the constant `C` and threshold `T` depend only on `a`, `b`, and `M`. -/
theorem exists_abs_log_norm_Gammaℝ_add_vertical_sub_le (a b : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∃ T > 0, ∀ μ : ℂ, ‖μ‖ ≤ M → ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      |Real.log ‖Complex.Gammaℝ (s + μ)‖ -
          (-π * |s.im| / 4 + (s.re + μ.re - 1) / 2 * Real.log |s.im|)| ≤ C := by
  set B := max |a| |b|
  have : 0 ≤ B := (abs_nonneg a).trans (le_max_left _ _)
  set R := B + M
  set K := 4 / (1 - Real.cos (π / 4)) ^ 3 + (R + 1) * R / 2 + R ^ 2 / 2
  have : 0 ≤ K := by
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
    abs_log_norm_Gammaℝ_vertical_sub_le_of_re_le hwre (by linarith)
  have htail := abs_Gammaℝ_shift_perturbation_le (by positivity) hwre1 (by linarith)
    (by linarith) ((abs_abs_sub_abs_le_abs_sub w.im s.im).trans (by simpa [w] using hμim))
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

/-- Uniform `O(1)` vertical-strip bound for `log ‖Gammaℂ (s + ν)‖` across all shifts `ν` with
`‖ν‖ ≤ M`: the constant `C` and threshold `T` depend only on `a`, `b`, and `M`. -/
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
  exact isBigO_one_vertical_strip_of_exists ⟨C, T, h μ le_rfl⟩

/-- `O(1)` vertical-line asymptotic for `t ↦ log ‖Gammaℝ (σ + i t + μ)‖`. -/
theorem isBigO_log_norm_Gammaℝ_add_vertical_line_sub (σ : ℝ) (μ : ℂ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gammaℝ (σ + t * I + μ)‖ -
        (-π * |t| / 4 + (σ + μ.re - 1) / 2 * Real.log |t|))
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) :=
  isBigO_cocompact_of_vertical (isBigO_log_norm_Gammaℝ_add_vertical_sub σ σ μ)

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
  exact isBigO_one_vertical_strip_of_exists ⟨C, T, h ν le_rfl⟩

/-- `O(1)` vertical-line asymptotic for `t ↦ log ‖Gammaℂ (σ + i t + ν)‖`. -/
theorem isBigO_log_norm_Gammaℂ_add_vertical_line_sub (σ : ℝ) (ν : ℂ) :
    (fun t : ℝ ↦ Real.log ‖Complex.Gammaℂ (σ + t * I + ν)‖ -
        (-π * |t| / 2 + (σ + ν.re - 1 / 2) * Real.log |t|))
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) :=
  isBigO_cocompact_of_vertical (isBigO_log_norm_Gammaℂ_add_vertical_sub σ σ ν)

private theorem tendsto_log_norm_Gammaℝ_add_I_atTop :
    Tendsto (fun t : ℝ ↦ Real.log ‖Complex.Gammaℝ ((0 : ℝ) + t * I + I)‖ -
        (-π * |t| / 4 + (0 + I.re - 1) / 2 * Real.log |t|))
      atTop (𝓝 (-π / 4 + (Real.log 2 + Real.log (2 * π)) / 2)) := by
  set c : ℝ := -π / 4 + (Real.log 2 + Real.log (2 * π)) / 2
  obtain ⟨C, T, hS⟩ := exists_abs_log_norm_Gammaℝ_vertical_sub_le 0 0
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (tendsto_const_nhds (x := |C| + 1).div_atTop tendsto_id)
  filter_upwards [eventually_ge_atTop (max T 2)] with t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_two ((le_max_right _ _).trans ht)
  have ht1 : 0 < t + 1 := by linarith
  set z : ℂ := ((t + 1 : ℝ) : ℂ) * I
  have hzre : z.re = 0 := by simp [z]
  have hzim : z.im = t + 1 := by simp [z]
  have harg : ((0 : ℝ) : ℂ) + t * I + I = z := by simp [z]; ring
  have hmain := hS z (by simp [hzre])
    (by rw [hzim, abs_of_pos ht1]; linarith [le_max_left T 2])
  rw [hzre, hzim, abs_of_pos ht1] at hmain
  have hlog : |(-1 / 2 : ℝ) * (Real.log (t + 1) - Real.log t)| ≤ 1 / t := by
    rw [abs_mul, show |(-1 / 2 : ℝ)| = 1 / 2 by norm_num,
      abs_of_nonneg (sub_nonneg.2 (Real.log_le_log ht0 (by linarith))),
      ← Real.log_div ht1.ne' ht0.ne']
    have hle : Real.log ((t + 1) / t) ≤ 1 / t :=
      (Real.log_le_sub_one_of_pos (div_pos ht1 ht0)).trans_eq (by field_simp; ring)
    linarith [hle, div_pos one_pos ht0]
  have hC_le : C / (t + 1) ≤ |C| / t :=
    (div_le_div_of_nonneg_right (le_abs_self C) ht1.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg C) ht0 (by linarith))
  rw [Real.norm_eq_abs, harg, abs_of_pos ht0]
  have hrew : Real.log ‖Complex.Gammaℝ z‖ -
      (-π * t / 4 + (0 + I.re - 1) / 2 * Real.log t) - c =
      (Real.log ‖Complex.Gammaℝ z‖ -
        (-π * (t + 1) / 4 + (0 - 1) / 2 * Real.log (t + 1) +
          (Real.log 2 - (0 - 1) * Real.log (2 * π)) / 2)) +
      (-1 / 2 : ℝ) * (Real.log (t + 1) - Real.log t) := by simp only [I_re, c]; ring
  rw [hrew, add_div]
  exact (abs_add_le _ _).trans (add_le_add (hmain.trans hC_le) hlog)

private theorem tendsto_log_norm_Gammaℝ_add_I_atBot :
    Tendsto (fun t : ℝ ↦ Real.log ‖Complex.Gammaℝ ((0 : ℝ) + t * I + I)‖ -
        (-π * |t| / 4 + (0 + I.re - 1) / 2 * Real.log |t|))
      atBot (𝓝 (π / 4 + (Real.log 2 + Real.log (2 * π)) / 2)) := by
  set c' : ℝ := π / 4 + (Real.log 2 + Real.log (2 * π)) / 2
  obtain ⟨C, T, hS⟩ := exists_abs_log_norm_Gammaℝ_vertical_sub_le 0 0
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_ (tendsto_const_nhds (x := |C| + 1).div_atTop
    (tendsto_atTop_add_const_right atBot (-1) tendsto_neg_atBot_atTop))
  filter_upwards [eventually_le_atBot (-(max T 2 + 2))] with t ht
  have htm1 : 0 < -t - 1 := by linarith [le_max_right T 2]
  have hmt : 0 < -t := by linarith
  have ht1_neg : t + 1 < 0 := by linarith
  have ht_neg : t < 0 := by linarith
  set z : ℂ := ((t + 1 : ℝ) : ℂ) * I
  have hzre : z.re = 0 := by simp [z]
  have hzim_abs : |z.im| = -t - 1 := by
    have hzim : z.im = t + 1 := by simp [z]
    rw [hzim, abs_of_neg ht1_neg]; ring
  have harg : ((0 : ℝ) : ℂ) + t * I + I = z := by simp [z]; ring
  have hmain := hS z (by simp [hzre]) (by linarith [hzim_abs, le_max_left T 2])
  rw [hzre, hzim_abs] at hmain
  have hlog : |(-1 / 2 : ℝ) * (Real.log (-t - 1) - Real.log (-t))| ≤ 1 / (-t - 1) := by
    rw [abs_mul, show |(-1 / 2 : ℝ)| = 1 / 2 by norm_num, ← abs_neg, neg_sub,
      abs_of_nonneg (sub_nonneg.2 (Real.log_le_log htm1 (by linarith))),
      ← Real.log_div hmt.ne' htm1.ne']
    have hle : Real.log (-t / (-t - 1)) ≤ 1 / (-t - 1) :=
      (Real.log_le_sub_one_of_pos (div_pos hmt htm1)).trans_eq (by field_simp; ring)
    linarith [hle, div_pos one_pos htm1]
  have hC_le : C / (-t - 1) ≤ |C| / (-t - 1) :=
    div_le_div_of_nonneg_right (le_abs_self C) htm1.le
  rw [Real.norm_eq_abs, harg, abs_of_neg ht_neg]
  have hrew : Real.log ‖Complex.Gammaℝ z‖ -
      (-π * -t / 4 + (0 + I.re - 1) / 2 * Real.log (-t)) - c' =
      (Real.log ‖Complex.Gammaℝ z‖ -
        (-π * (-t - 1) / 4 + (0 - 1) / 2 * Real.log (-t - 1) +
          (Real.log 2 - (0 - 1) * Real.log (2 * π)) / 2)) +
      (-1 / 2 : ℝ) * (Real.log (-t - 1) - Real.log (-t)) := by simp only [I_re, c']; ring
  rw [hrew, add_div]
  exact (abs_add_le _ _).trans (add_le_add (hmain.trans hC_le) hlog)

-- Non-real shift check: for `μ = I` along `s = t * I`, `|t + 1|` shifts the linear exponential
-- term by `-π / 4` as `t → +∞` and by `+π / 4` as `t → -∞`, so the difference between the two
-- asymptotic constants is `π / 2 > 0` and the `O(1)` error cannot be improved to `o(1)`.
example : ¬ ((fun t : ℝ ↦ Real.log ‖Complex.Gammaℝ ((0 : ℝ) + t * I + I)‖ -
    (-π * |t| / 4 + (0 + I.re - 1) / 2 * Real.log |t|)) =o[cocompact ℝ] fun _ ↦ (1 : ℝ)) := by
  intro ho
  have hlim : Tendsto (fun t : ℝ ↦ Real.log ‖Complex.Gammaℝ ((0 : ℝ) + t * I + I)‖ -
      (-π * |t| / 4 + (0 + I.re - 1) / 2 * Real.log |t|)) (cocompact ℝ) (𝓝 0) := by
    simpa using ho.tendsto_div_nhds_zero
  have hatTop : (atTop : Filter ℝ) ≤ cocompact ℝ :=
    le_sup_right.trans_eq _root_.cocompact_eq_atBot_atTop.symm
  have hatBot : (atBot : Filter ℝ) ≤ cocompact ℝ :=
    le_sup_left.trans_eq _root_.cocompact_eq_atBot_atTop.symm
  have hc0 := tendsto_nhds_unique tendsto_log_norm_Gammaℝ_add_I_atTop (hlim.mono_left hatTop)
  have hc'0 := tendsto_nhds_unique tendsto_log_norm_Gammaℝ_add_I_atBot (hlim.mono_left hatBot)
  linarith [Real.pi_pos, hc0, hc'0]

end TauCeti
