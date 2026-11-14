/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Archimedean
public import TauCeti.NumberTheory.LFunctions.GammaFactor.Basic
public import TauCeti.NumberTheory.LFunctions.Data.AnalyticConductor.Basic
import TauCeti.Algebra.Order.BigOperators.Group.Multiset
import TauCeti.Analysis.Normed.Ring.Multiset

/-!
# Vertical-strip asymptotics of archimedean gamma factors and dual gamma quotients

For an analytic L-function record `d : AnalyticLFunctionData` of degree `n = d.degree` with gamma
factor
$$\gamma(s) = \prod_{\mu \in \mathrm{gammaR}} \Gamma_{\mathbb{R}}(s + \mu)
  \prod_{\nu \in \mathrm{gammaC}} \Gamma_{\mathbb{C}}(s + \nu),$$
summing the complex-shifted vertical-strip Stirling estimates of
`TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Archimedean` over the multisets `d.gammaR` and
`d.gammaC` yields, uniformly for `σ ∈ [a, b]` as `|t| → ∞`,
$$\log \|\gamma(\sigma + i t)\| = -\frac{\pi n}{4} |t| + A(\sigma) \log |t| + O(1),$$
where the logarithmic height exponent is
$$A(\sigma) = \sum_{\mu \in \mathrm{gammaR}} \frac{\sigma + \operatorname{Re}\mu - 1}{2}
  + \sum_{\nu \in \mathrm{gammaC}} \left(\sigma + \operatorname{Re}\nu - \frac{1}{2}\right).$$
The implied constant and height threshold can be chosen uniformly across all records of fixed
degree `n` whose spectral shifts are bounded in norm by `M`, independently of the arithmetic
conductor.

For the reflected dual quotient `d.dual.gammaFactor (1 - s) / d.gammaFactor s` governing the
functional equation of the uncompleted L-function, two cancellations occur simultaneously:

* the linear exponential terms `-(π n / 4) |t|` of `d.dual.gammaFactor (1 - s)` and
  `d.gammaFactor s` agree and cancel;
* conjugating the gamma shifts in `d.dual` leaves their real parts unchanged, and those real parts
  enter `1 - s + conj μ` and `s + μ` with the same sign, so `d.dual.gammaLogExponent (1 - σ) -
  d.gammaLogExponent σ = (n / 2) (1 - 2 σ)` depends only on the degree and `σ`.

Consequently, uniformly on every vertical strip `Re s ∈ [a, b]`,
$$\log \left\|\frac{\gamma^{\vee}(1 - s)}{\gamma(s)}\right\| =
  \frac{n}{2} (1 - 2 \operatorname{Re} s) \log |\operatorname{Im} s| + O(1),$$
and along `Re s = -δ` this specializes to `(n / 2) (1 + 2 δ) log |t| + O(1)`. Combining the
resulting polynomial height bound with the strip comparison
`AnalyticLFunctionData.exists_analyticConductorAt_strip_bounds` bounds the conductor-weighted
archimedean functional-equation factor `‖N ^ (1 / 2 - s) (γ^∨(1 - s) / γ(s))‖` by a constant
multiple of `d.analyticConductorAt s ^ (1 / 2 - s.re)` uniformly in `d.conductor` — both at large
height on arbitrary strips `Re s ∈ [a, b]` and for all heights on `Re s ∈ [a, b]` (in particular
along any vertical line `Re s = -δ`) whenever all reflected shifted arguments satisfy the right
half-plane margin `ε ≤ 1 - b + Re μ` and `ε ≤ 1 - b + Re ν` (`ε ≤ 1 + δ + Re μ` and
`ε ≤ 1 + δ + Re ν` on `Re s = -δ`) for some `ε > 0`.

## Main declarations

* `AnalyticLFunctionData.gammaLogExponent`: the exponent `A(σ)` of `log |t|`, with
  `gammaLogExponent_add`, `gammaLogExponent_sub`, `gammaLogExponent_sub_gammaLogExponent`,
  `gammaLogExponent_dual`, and `gammaLogExponent_one_sub_sub`.
* `exists_abs_log_norm_gammaFactor_vertical_sub_le_of_norm_le`,
  `exists_norm_gammaFactor_vertical_bounds_of_norm_le`,
  `isBigO_log_norm_gammaFactor_vertical_sub` (and strip / line / single-record variants):
  vertical-strip asymptotics of `d.gammaFactor`.
* `exists_abs_log_norm_dual_gammaFactor_div_vertical_sub_le_of_norm_le`,
  `isBigO_log_norm_dual_gammaFactor_div_vertical_sub`,
  `isBigO_log_norm_dual_gammaFactor_div_neg_line_sub`: exponential cancellation in
  `log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖`.
* `exists_norm_conductor_cpow_mul_dual_gammaFactor_div_le_analyticConductorAt_rpow`,
  `exists_norm_conductor_cpow_mul_dual_gammaFactor_div_strip_le_analyticConductorAt_rpow`,
  `exists_norm_conductor_cpow_mul_dual_gammaFactor_div_neg_line_le_analyticConductorAt_rpow`:
  conductor-uniform upper bounds in terms of `d.analyticConductorAt`.

## References

* [NIST Digital Library of Mathematical Functions, 5.11.9](https://dlmf.nist.gov/5.11.E9).
* P. Deligne, *Valeurs de fonctions L et périodes d'intégrales*, Proc. Symp. Pure Math. 33 (1979),
  Part 2, §5.3.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §§5.1–5.2.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (1986), §§4.12 and 5.1.
-/

public section

open Complex ComplexConjugate Real Filter Set Asymptotics

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-! ### The logarithmic height exponent `A(σ)` -/

/-- The exponent `A(σ) = ∑_{μ ∈ gammaR} (σ + Re μ - 1)/2 + ∑_{ν ∈ gammaC} (σ + Re ν - 1/2)` of
`log |Im s|` in the vertical-strip asymptotic of `log ‖d.gammaFactor s‖`. -/
noncomputable def gammaLogExponent (d : AnalyticLFunctionData) (σ : ℝ) : ℝ :=
  (d.gammaR.map fun μ ↦ (σ + μ.re - 1) / 2).sum +
    (d.gammaC.map fun ν ↦ σ + ν.re - 1 / 2).sum

theorem gammaLogExponent_def (d : AnalyticLFunctionData) (σ : ℝ) :
    d.gammaLogExponent σ =
      (d.gammaR.map fun μ ↦ (σ + μ.re - 1) / 2).sum +
        (d.gammaC.map fun ν ↦ σ + ν.re - 1 / 2).sum :=
  (rfl)

/-- `d.gammaLogExponent` is affine in `σ` with slope `d.degree / 2`. -/
theorem gammaLogExponent_eq (d : AnalyticLFunctionData) (σ : ℝ) :
    d.gammaLogExponent σ = (d.degree : ℝ) / 2 * σ +
      ((d.gammaR.map fun μ ↦ (μ.re - 1) / 2).sum +
        (d.gammaC.map fun ν ↦ ν.re - 1 / 2).sum) := by
  have hR : (d.gammaR.map fun μ ↦ (σ + μ.re - 1) / 2).sum =
      (d.gammaR.map fun μ ↦ σ / 2 + (μ.re - 1) / 2).sum :=
    congrArg Multiset.sum (Multiset.map_congr rfl fun _ _ ↦ by ring)
  have hC : (d.gammaC.map fun ν ↦ σ + ν.re - 1 / 2).sum =
      (d.gammaC.map fun ν ↦ σ + (ν.re - 1 / 2)).sum :=
    congrArg Multiset.sum (Multiset.map_congr rfl fun _ _ ↦ by ring)
  rw [gammaLogExponent_def, hR, hC, Multiset.sum_map_add, Multiset.sum_map_add,
    Multiset.map_const', Multiset.sum_replicate, Multiset.map_const', Multiset.sum_replicate,
    degree_def]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- Shifting the real part by `τ` shifts `gammaLogExponent` by `(d.degree / 2) * τ`. -/
theorem gammaLogExponent_add (d : AnalyticLFunctionData) (σ τ : ℝ) :
    d.gammaLogExponent (σ + τ) = d.gammaLogExponent σ + (d.degree : ℝ) / 2 * τ := by
  rw [d.gammaLogExponent_eq (σ + τ), d.gammaLogExponent_eq σ]
  ring

/-- Subtracting `τ` from the real part shifts `gammaLogExponent` by `-(d.degree / 2) * τ`. -/
theorem gammaLogExponent_sub (d : AnalyticLFunctionData) (σ τ : ℝ) :
    d.gammaLogExponent (σ - τ) = d.gammaLogExponent σ - (d.degree : ℝ) / 2 * τ := by
  rw [d.gammaLogExponent_eq (σ - τ), d.gammaLogExponent_eq σ]
  ring

/-- Difference of `gammaLogExponent` across two real parts: all shift real parts cancel, leaving
`(d.degree / 2) * (σ - τ)`. -/
theorem gammaLogExponent_sub_gammaLogExponent (d : AnalyticLFunctionData) (σ τ : ℝ) :
    d.gammaLogExponent σ - d.gammaLogExponent τ = (d.degree : ℝ) / 2 * (σ - τ) := by
  rw [d.gammaLogExponent_eq σ, d.gammaLogExponent_eq τ]
  ring

/-- A degree-zero record has vanishing logarithmic gamma exponent. -/
theorem gammaLogExponent_eq_zero_of_degree_eq_zero (d : AnalyticLFunctionData)
    (hd : d.degree = 0) (σ : ℝ) : d.gammaLogExponent σ = 0 := by
  have hR : d.gammaR = 0 := Multiset.card_eq_zero.mp (by rw [degree_def] at hd; omega)
  have hC : d.gammaC = 0 := Multiset.card_eq_zero.mp (by rw [degree_def] at hd; omega)
  simp [gammaLogExponent_def, hR, hC]

/-- Conjugating the shifts in `d.dual` preserves their real parts, leaving `gammaLogExponent`
unchanged. -/
@[simp]
theorem gammaLogExponent_dual (d : AnalyticLFunctionData) (σ : ℝ) :
    d.dual.gammaLogExponent σ = d.gammaLogExponent σ := by
  simp [gammaLogExponent_def, Multiset.map_map]

/-- The reflected exponent difference `A(1 - σ) - A(σ)` cancels all shift real parts, leaving
`(d.degree / 2) * (1 - 2 σ)`. -/
@[simp]
theorem gammaLogExponent_one_sub_sub (d : AnalyticLFunctionData) (σ : ℝ) :
    d.gammaLogExponent (1 - σ) - d.gammaLogExponent σ = (d.degree : ℝ) / 2 * (1 - 2 * σ) := by
  rw [d.gammaLogExponent_sub_gammaLogExponent]
  ring

/-! ### Vertical-strip Stirling asymptotics for `d.gammaFactor` -/

private theorem gammaFactor_stirling_main_sum (d : AnalyticLFunctionData) (s : ℂ) :
    (d.gammaR.map fun μ ↦ -Real.pi * |s.im| / 4 + (s.re + μ.re - 1) / 2 * Real.log |s.im|).sum +
    (d.gammaC.map fun ν ↦ -Real.pi * |s.im| / 2 + (s.re + ν.re - 1 / 2) * Real.log |s.im|).sum =
      -(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent s.re * Real.log |s.im| := by
  rw [Multiset.sum_map_add, Multiset.sum_map_add,
    Multiset.map_const', Multiset.sum_replicate, Multiset.map_const', Multiset.sum_replicate,
    Multiset.sum_map_mul_right, Multiset.sum_map_mul_right, gammaLogExponent_def,
    degree_def]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- **Uniform vertical-strip asymptotic for `d.gammaFactor`** across all records of degree `n` with
shifts bounded in norm by `M`: the constant `C` and height threshold `T` depend only on `a`, `b`,
`n`, and `M`, not on `d` or `d.conductor`. -/
theorem exists_abs_log_norm_gammaFactor_vertical_sub_le_of_norm_le (a b : ℝ) (n : ℕ) {M : ℝ}
    (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∃ T > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) → (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) →
      ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
        d.gammaFactor s ≠ 0 ∧
        |Real.log ‖d.gammaFactor s‖ -
            (-(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent s.re * Real.log |s.im|)| ≤
          C := by
  obtain ⟨CR, hCR0, TR, hTR0, hR_est⟩ :=
    TauCeti.exists_abs_log_norm_Gammaℝ_add_vertical_sub_le a b hM
  obtain ⟨CC, _, TC, _, hC_est⟩ :=
    TauCeti.exists_abs_log_norm_Gammaℂ_add_vertical_sub_le a b hM
  set K := max CR CC
  have hK0 : 0 ≤ K := hCR0.trans (le_max_left _ _)
  refine ⟨(n : ℝ) * K, by positivity, max (max TR TC) (M + 1), by positivity,
    fun d hd hR hC s hs ht ↦ ?_⟩
  have htTR : TR ≤ |s.im| := ((le_max_left _ _).trans (le_max_left _ _)).trans ht
  have htTC : TC ≤ |s.im| := ((le_max_right _ _).trans (le_max_left _ _)).trans ht
  have htM : M + 1 ≤ |s.im| := (le_max_right _ _).trans ht
  have hne : d.gammaFactor s ≠ 0 := d.gammaFactor_ne_zero_of_im_gt
    (fun μ hμ ↦ ((abs_im_le_norm μ).trans (hR μ hμ)).trans_lt (by linarith))
    (fun ν hν ↦ ((abs_im_le_norm ν).trans (hC ν hν)).trans_lt (by linarith))
  refine ⟨hne, ?_⟩
  set mR : ℂ → ℝ := fun μ ↦ -Real.pi * |s.im| / 4 + (s.re + μ.re - 1) / 2 * Real.log |s.im|
  set mC : ℂ → ℝ := fun ν ↦ -Real.pi * |s.im| / 2 + (s.re + ν.re - 1 / 2) * Real.log |s.im|
  have hsumR : |(d.gammaR.map fun μ ↦ Real.log ‖Gammaℝ (s + μ)‖).sum -
      (d.gammaR.map mR).sum| ≤ (d.gammaR.card : ℝ) * K := by
    rw [← Multiset.sum_map_sub, ← nsmul_eq_mul]
    exact d.gammaR.abs_sum_map_le_card_nsmul _ fun μ hμ ↦
      (hR_est μ (hR μ hμ) s hs htTR).trans (le_max_left _ _)
  have hsumC : |(d.gammaC.map fun ν ↦ Real.log ‖Gammaℂ (s + ν)‖).sum -
      (d.gammaC.map mC).sum| ≤ (d.gammaC.card : ℝ) * K := by
    rw [← Multiset.sum_map_sub, ← nsmul_eq_mul]
    exact d.gammaC.abs_sum_map_le_card_nsmul _ fun ν hν ↦
      (hC_est ν (hC ν hν) s hs htTC).trans (le_max_right _ _)
  rw [d.log_norm_gammaFactor hne, ← d.gammaFactor_stirling_main_sum s]
  have hsplit : (d.gammaR.map fun μ ↦ Real.log ‖Gammaℝ (s + μ)‖).sum +
        (d.gammaC.map fun ν ↦ Real.log ‖Gammaℂ (s + ν)‖).sum -
        ((d.gammaR.map mR).sum + (d.gammaC.map mC).sum) =
      ((d.gammaR.map fun μ ↦ Real.log ‖Gammaℝ (s + μ)‖).sum - (d.gammaR.map mR).sum) +
      ((d.gammaC.map fun ν ↦ Real.log ‖Gammaℂ (s + ν)‖).sum - (d.gammaC.map mC).sum) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ((add_le_add hsumR hsumC).trans ?_)
  have hcard : (d.gammaR.card : ℝ) + d.gammaC.card ≤ n := by
    have : d.gammaR.card + d.gammaC.card ≤ n := by rw [← hd, degree_def]; omega
    exact_mod_cast this
  nlinarith

/-- Uniform vertical-strip bound for the Stirling remainder of `log ‖d.gammaFactor s‖` on
`Re s ∈ [a, b]`. -/
theorem exists_abs_log_norm_gammaFactor_vertical_sub_le (d : AnalyticLFunctionData) (a b : ℝ) :
    ∃ C ≥ 0, ∃ T > 0, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      d.gammaFactor s ≠ 0 ∧
      |Real.log ‖d.gammaFactor s‖ -
          (-(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent s.re * Real.log |s.im|)| ≤
        C := by
  obtain ⟨M, hM0, hR, hC⟩ := d.exists_shift_norm_le
  obtain ⟨C, hC0, T, hT0, h⟩ :=
    exists_abs_log_norm_gammaFactor_vertical_sub_le_of_norm_le a b d.degree hM0
  exact ⟨C, hC0, T, hT0, h d rfl hR hC⟩

/-- **Vertical-strip asymptotic of `d.gammaFactor`**:
`log ‖d.gammaFactor(σ + i t)‖ = -(π d.degree / 4) |t| + d.gammaLogExponent σ * log |t| + O(1)`
uniformly for `σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_gammaFactor_vertical_sub (d : AnalyticLFunctionData) (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖d.gammaFactor (p.1 + p.2 * I)‖ -
        (-(Real.pi * d.degree / 4) * |p.2| + d.gammaLogExponent p.1 * Real.log |p.2|))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := d.exists_abs_log_norm_gammaFactor_vertical_sub_le a b
  refine isBigO_one_vertical_of_exists ⟨C, T, fun p hσ ht ↦ ?_⟩
  simpa using (h (p.1 + p.2 * I) (by simpa using hσ) (by simpa using ht)).2

/-- **Vertical-strip asymptotic of `d.gammaFactor`** as a function of `s` on `Re s ∈ [a, b]`. -/
theorem isBigO_log_norm_gammaFactor_vertical_strip_sub (d : AnalyticLFunctionData) (a b : ℝ) :
    (fun s : ℂ ↦ Real.log ‖d.gammaFactor s‖ -
        (-(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent s.re * Real.log |s.im|))
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := d.exists_abs_log_norm_gammaFactor_vertical_sub_le a b
  exact isBigO_one_vertical_strip_of_exists ⟨C, T, fun s hs ht ↦ by simpa using (h s hs ht).2⟩

/-- Vertical-line asymptotic of `t ↦ log ‖d.gammaFactor (σ + i t)‖` along `cocompact ℝ`. -/
theorem isBigO_log_norm_gammaFactor_vertical_line_sub (d : AnalyticLFunctionData) (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖d.gammaFactor (σ + t * I)‖ -
        (-(Real.pi * d.degree / 4) * |t| + d.gammaLogExponent σ * Real.log |t|))
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) :=
  (d.isBigO_log_norm_gammaFactor_vertical_sub σ σ).cocompact_of_vertical (left_mem_Icc.2 le_rfl)

private theorem exp_neg_mul_le_and_le_exp_mul_of_abs_log_sub_le {x t C E e : ℝ}
    (hx : 0 < x) (ht : 0 < t) (hlog : |Real.log x - (E + e * Real.log t)| ≤ C) :
    Real.exp (-C) * Real.exp E * t ^ e ≤ x ∧
      x ≤ Real.exp C * Real.exp E * t ^ e := by
  obtain ⟨hl, hu⟩ := abs_le.1 hlog
  have hexp_e : Real.exp (e * Real.log t) = t ^ e := by
    rw [Real.rpow_def_of_pos ht, mul_comm]
  constructor
  · calc Real.exp (-C) * Real.exp E * t ^ e
        = Real.exp (-C + E + e * Real.log t) := by rw [← hexp_e, ← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (Real.log x) := Real.exp_le_exp.2 (by linarith)
      _ = x := Real.exp_log hx
  · calc x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ ≤ Real.exp (C + E + e * Real.log t) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp C * Real.exp E * t ^ e := by rw [← hexp_e, ← Real.exp_add, ← Real.exp_add]

/-- Two-sided norm bounds for `‖d.gammaFactor s‖` on `Re s ∈ [a, b]` above the pole heights,
uniform across all records of degree `n` with shifts bounded in norm by `M`:
`C₁ exp(-(π n / 4) |t|) |t| ^ A(σ) ≤ ‖γ(s)‖ ≤ C₂ exp(-(π n / 4) |t|) |t| ^ A(σ)`. -/
theorem exists_norm_gammaFactor_vertical_bounds_of_norm_le (a b : ℝ) (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ T > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) → (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) →
      ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
        C₁ * Real.exp (-(Real.pi * d.degree / 4) * |s.im|) * |s.im| ^ d.gammaLogExponent s.re ≤
          ‖d.gammaFactor s‖ ∧
        ‖d.gammaFactor s‖ ≤
          C₂ * Real.exp (-(Real.pi * d.degree / 4) * |s.im|) *
            |s.im| ^ d.gammaLogExponent s.re := by
  obtain ⟨C, -, T, hT0, h⟩ :=
    exists_abs_log_norm_gammaFactor_vertical_sub_le_of_norm_le a b n hM
  refine ⟨Real.exp (-C), Real.exp_pos _, Real.exp C, Real.exp_pos _, T, hT0,
    fun d hd hR hC s hs ht ↦ ?_⟩
  obtain ⟨hne, hlog⟩ := h d hd hR hC s hs ht
  exact exp_neg_mul_le_and_le_exp_mul_of_abs_log_sub_le (norm_pos_iff.2 hne) (hT0.trans_le ht) hlog

/-- Single-record two-sided norm bounds for `‖d.gammaFactor s‖` on `Re s ∈ [a, b]` above the pole
heights:
`C₁ exp(-(π n / 4) |t|) |t| ^ A(σ) ≤ ‖γ(s)‖ ≤ C₂ exp(-(π n / 4) |t|) |t| ^ A(σ)`. -/
theorem exists_norm_gammaFactor_vertical_bounds (d : AnalyticLFunctionData) (a b : ℝ) :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ T > 0, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      C₁ * Real.exp (-(Real.pi * d.degree / 4) * |s.im|) * |s.im| ^ d.gammaLogExponent s.re ≤
        ‖d.gammaFactor s‖ ∧
      ‖d.gammaFactor s‖ ≤
        C₂ * Real.exp (-(Real.pi * d.degree / 4) * |s.im|) * |s.im| ^ d.gammaLogExponent s.re := by
  obtain ⟨M, hM0, hR, hC⟩ := d.exists_shift_norm_le
  obtain ⟨C₁, hC₁, C₂, hC₂, T, hT0, h⟩ :=
    exists_norm_gammaFactor_vertical_bounds_of_norm_le a b d.degree hM0
  exact ⟨C₁, hC₁, C₂, hC₂, T, hT0, h d rfl hR hC⟩

/-! ### Exponential cancellation in the dual gamma quotient -/

/-- **Exponential cancellation in the dual gamma quotient**, uniform across all records of degree
`n` with shifts bounded in norm by `M`: the linear exponential terms `-(π n / 4) |Im s|` and all
shift real parts cancel between `d.dual.gammaFactor (1 - s)` and `d.gammaFactor s`, leaving
`(n / 2) * (1 - 2 * s.re) * log |s.im| + O(1)` with constants independent of `d` and
`d.conductor`. -/
theorem exists_abs_log_norm_dual_gammaFactor_div_vertical_sub_le_of_norm_le (a b : ℝ) (n : ℕ)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∃ T > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) → (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) →
      ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
        d.gammaFactor s ≠ 0 ∧ d.dual.gammaFactor (1 - s) ≠ 0 ∧
        |Real.log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ -
            ((d.degree : ℝ) / 2 * (1 - 2 * s.re) * Real.log |s.im|)| ≤ C := by
  obtain ⟨C₁, hC₁, T₁, hT₁, h₁⟩ :=
    exists_abs_log_norm_gammaFactor_vertical_sub_le_of_norm_le a b n hM
  obtain ⟨C₂, hC₂, T₂, _, h₂⟩ :=
    exists_abs_log_norm_gammaFactor_vertical_sub_le_of_norm_le (1 - b) (1 - a) n hM
  refine ⟨C₁ + C₂, by positivity, max T₁ T₂, by positivity,
    fun d hd hR hC s hs ht ↦ ?_⟩
  have hR_dual : ∀ μ' ∈ d.dual.gammaR, ‖μ'‖ ≤ M := by
    intro μ' hμ'
    rw [dual_gammaR] at hμ'
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hμ'
    simpa using hR μ hμ
  have hC_dual : ∀ ν' ∈ d.dual.gammaC, ‖ν'‖ ≤ M := by
    intro ν' hν'
    rw [dual_gammaC] at hν'
    obtain ⟨ν, hν, rfl⟩ := Multiset.mem_map.mp hν'
    simpa using hC ν hν
  have hs1 : (1 - s).re ∈ Icc (1 - b) (1 - a) :=
    ⟨by simp; linarith [hs.2], by simp; linarith [hs.1]⟩
  have him1 : |(1 - s).im| = |s.im| := by simp
  obtain ⟨hne₁, hb₁⟩ := h₁ d hd hR hC s hs ((le_max_left _ _).trans ht)
  obtain ⟨hne₂, hb₂⟩ := h₂ d.dual (by simpa using hd) hR_dual hC_dual (1 - s) hs1
    (by rw [him1]; exact (le_max_right _ _).trans ht)
  refine ⟨hne₁, hne₂, ?_⟩
  rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hne₂) (norm_ne_zero_iff.2 hne₁)]
  simp only [degree_dual, sub_re, one_re, him1, gammaLogExponent_dual] at hb₂
  have hexp_cancel :
      Real.log ‖d.dual.gammaFactor (1 - s)‖ - Real.log ‖d.gammaFactor s‖ -
        ((d.degree : ℝ) / 2 * (1 - 2 * s.re) * Real.log |s.im|) =
      (Real.log ‖d.dual.gammaFactor (1 - s)‖ -
        (-(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent (1 - s.re) * Real.log |s.im|)) -
      (Real.log ‖d.gammaFactor s‖ -
        (-(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent s.re * Real.log |s.im|)) := by
    rw [← d.gammaLogExponent_one_sub_sub s.re]
    ring
  rw [hexp_cancel]
  exact (abs_sub _ _).trans (by linarith)

/-- Uniform vertical-strip bound for the Stirling remainder of
`log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖` on `Re s ∈ [a, b]`. -/
theorem exists_abs_log_norm_dual_gammaFactor_div_vertical_sub_le (d : AnalyticLFunctionData)
    (a b : ℝ) :
    ∃ C ≥ 0, ∃ T > 0, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      d.gammaFactor s ≠ 0 ∧ d.dual.gammaFactor (1 - s) ≠ 0 ∧
      |Real.log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ -
          ((d.degree : ℝ) / 2 * (1 - 2 * s.re) * Real.log |s.im|)| ≤ C := by
  obtain ⟨M, hM0, hR, hC⟩ := d.exists_shift_norm_le
  obtain ⟨C, hC0, T, hT0, h⟩ :=
    exists_abs_log_norm_dual_gammaFactor_div_vertical_sub_le_of_norm_le a b d.degree hM0
  exact ⟨C, hC0, T, hT0, h d rfl hR hC⟩

/-- **Dual gamma-quotient asymptotic on vertical strips**:
`log ‖d.dual.gammaFactor (1 - (σ + i t)) / d.gammaFactor (σ + i t)‖ =
  (d.degree / 2) * (1 - 2 σ) * log |t| + O(1)` uniformly for `σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_dual_gammaFactor_div_vertical_sub (d : AnalyticLFunctionData) (a b : ℝ) :
    (fun p : ℝ × ℝ ↦
        Real.log ‖d.dual.gammaFactor (1 - (p.1 + p.2 * I)) / d.gammaFactor (p.1 + p.2 * I)‖ -
          (d.degree : ℝ) / 2 * (1 - 2 * p.1) * Real.log |p.2|)
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := d.exists_abs_log_norm_dual_gammaFactor_div_vertical_sub_le a b
  refine isBigO_one_vertical_of_exists ⟨C, T, fun p hσ ht ↦ ?_⟩
  simpa using (h (p.1 + p.2 * I) (by simpa using hσ) (by simpa using ht)).2.2

/-- **Dual gamma-quotient asymptotic** as a function of `s` on `Re s ∈ [a, b]`. -/
theorem isBigO_log_norm_dual_gammaFactor_div_vertical_strip_sub (d : AnalyticLFunctionData)
    (a b : ℝ) :
    (fun s : ℂ ↦ Real.log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ -
        (d.degree : ℝ) / 2 * (1 - 2 * s.re) * Real.log |s.im|)
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := d.exists_abs_log_norm_dual_gammaFactor_div_vertical_sub_le a b
  exact isBigO_one_vertical_strip_of_exists ⟨C, T, fun s hs ht ↦ by simpa using (h s hs ht).2.2⟩

/-- Dual gamma-quotient asymptotic on a vertical line `Re s = σ`. -/
theorem isBigO_log_norm_dual_gammaFactor_div_vertical_line_sub (d : AnalyticLFunctionData)
    (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖d.dual.gammaFactor (1 - (σ + t * I)) / d.gammaFactor (σ + t * I)‖ -
        (d.degree : ℝ) / 2 * (1 - 2 * σ) * Real.log |t|)
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) :=
  (d.isBigO_log_norm_dual_gammaFactor_div_vertical_sub σ σ).cocompact_of_vertical
    (left_mem_Icc.2 le_rfl)

/-- **Dual gamma-quotient asymptotic on `Re s = -δ`**:
`log ‖d.dual.gammaFactor (1 - (-δ + i t)) / d.gammaFactor (-δ + i t)‖ =
  (d.degree / 2) * (1 + 2 δ) * log |t| + O(1)` as `|t| → ∞`. -/
theorem isBigO_log_norm_dual_gammaFactor_div_neg_line_sub (d : AnalyticLFunctionData) (δ : ℝ) :
    (fun t : ℝ ↦
        Real.log ‖d.dual.gammaFactor (1 - ((-δ : ℝ) + t * I)) /
            d.gammaFactor ((-δ : ℝ) + t * I)‖ -
          (d.degree : ℝ) / 2 * (1 + 2 * δ) * Real.log |t|)
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  simpa only [sub_neg_eq_add, mul_neg] using
    d.isBigO_log_norm_dual_gammaFactor_div_vertical_line_sub (-δ)

/-! ### Polynomial norm bounds and comparison with `analyticConductorAt` -/

/-- Two-sided polynomial norm bounds for `‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖` on
`Re s ∈ [a, b]` above the pole heights, uniform across all records of degree `n` with shifts
bounded in norm by `M`. -/
theorem exists_norm_dual_gammaFactor_div_bounds_of_norm_le (a b : ℝ) (n : ℕ) {M : ℝ}
    (hM : 0 ≤ M) :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ T > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) → (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) →
      ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
        C₁ * |s.im| ^ ((d.degree : ℝ) / 2 * (1 - 2 * s.re)) ≤
          ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ ∧
        ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ ≤
          C₂ * |s.im| ^ ((d.degree : ℝ) / 2 * (1 - 2 * s.re)) := by
  obtain ⟨C, -, T, hT0, h⟩ :=
    exists_abs_log_norm_dual_gammaFactor_div_vertical_sub_le_of_norm_le a b n hM
  refine ⟨Real.exp (-C), Real.exp_pos _, Real.exp C, Real.exp_pos _, T, hT0,
    fun d hd hR hC s hs ht ↦ ?_⟩
  obtain ⟨hne₁, hne₂, hlog⟩ := h d hd hR hC s hs ht
  simpa using exp_neg_mul_le_and_le_exp_mul_of_abs_log_sub_le
    (norm_pos_iff.2 (div_ne_zero hne₂ hne₁)) (hT0.trans_le ht) (E := 0) (by simpa using hlog)

/-- Single-record two-sided polynomial norm bounds for
`‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖` on `Re s ∈ [a, b]`. -/
theorem exists_norm_dual_gammaFactor_div_bounds (d : AnalyticLFunctionData) (a b : ℝ) :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ T > 0, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      C₁ * |s.im| ^ ((d.degree : ℝ) / 2 * (1 - 2 * s.re)) ≤
        ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ ∧
      ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ ≤
        C₂ * |s.im| ^ ((d.degree : ℝ) / 2 * (1 - 2 * s.re)) := by
  obtain ⟨M, hM0, hR, hC⟩ := d.exists_shift_norm_le
  obtain ⟨C₁, hC₁, C₂, hC₂, T, hT, h⟩ :=
    exists_norm_dual_gammaFactor_div_bounds_of_norm_le a b d.degree hM0
  exact ⟨C₁, hC₁, C₂, hC₂, T, hT, h d rfl hR hC⟩

/-- **Conductor-uniform functional-equation factor bound on vertical strips**: for `a b : ℝ`,
degree `n`, and shift norm bound `M`, there exist `C > 0` and `T > 0` (independent of `d` and
`d.conductor`) such that for every `s` with `s.re ∈ [a, b]` and `T ≤ |s.im|`,
`‖N ^ (1 / 2 - s) (γ^∨(1 - s) / γ(s))‖ ≤ C * d.analyticConductorAt s ^ (1 / 2 - s.re)`. -/
theorem exists_norm_conductor_cpow_mul_dual_gammaFactor_div_le_analyticConductorAt_rpow (a b : ℝ)
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∃ T > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) → (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) →
      ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
        ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
            (d.dual.gammaFactor (1 - s) / d.gammaFactor s)‖ ≤
          C * d.analyticConductorAt s ^ (1 / 2 - s.re) := by
  obtain ⟨_, _, C_q, hC_q, T_q, hT_q, hbounds⟩ :=
    exists_norm_dual_gammaFactor_div_bounds_of_norm_le a b n hM
  obtain ⟨C₁, hC₁, C₂, hC₂, hstrip⟩ := exists_analyticConductorAt_strip_bounds a b n hM
  set K := max 1 (max C₁⁻¹ (C₂ * 4 ^ n))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK_pos : 0 < K := zero_lt_one.trans_le hK1
  set E := max |1 / 2 - a| |1 / 2 - b|
  refine ⟨C_q * K ^ E, by positivity, max T_q 1, by positivity,
    fun d hd hR hC s hs ht ↦ ?_⟩
  have ht_q : T_q ≤ |s.im| := (le_max_left _ _).trans ht
  have ht1 : 1 ≤ |s.im| := (le_max_right _ _).trans ht
  have ht_pos : 0 < |s.im| := zero_lt_one.trans_le ht1
  set e : ℝ := 1 / 2 - s.re
  have he_abs : |e| ≤ E := (abs_le_max_abs_abs (sub_le_sub_left hs.2 (1 / 2))
    (sub_le_sub_left hs.1 (1 / 2))).trans_eq (max_comm _ _)
  have hcond_norm : ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)‖ = (d.conductor : ℝ) ^ e := by
    rw [Complex.norm_natCast_cpow_of_pos d.conductor.pos]
    congr 1
    simp [e]
  have hq := (hbounds d hd hR hC s hs ht_q).2
  have hexp_eq : (d.degree : ℝ) / 2 * (1 - 2 * s.re) = (n : ℝ) * e := by
    rw [hd]; dsimp only [e]; ring
  rw [hexp_eq, Real.rpow_mul ht_pos.le, Real.rpow_natCast] at hq
  obtain ⟨hcond_lo, hcond_hi⟩ := hstrip d hd hR hC s hs
  have hcond_pos : 0 < d.analyticConductorAt s := d.analyticConductorAt_pos s
  have hN_pos : 0 < (d.conductor : ℝ) := Nat.cast_pos.2 d.conductor.pos
  have hrpow_cond : (d.conductor : ℝ) ^ e * (|s.im| ^ n) ^ e ≤
      K ^ E * d.analyticConductorAt s ^ e := by
    rw [← Real.mul_rpow hN_pos.le (by positivity)]
    rcases le_total 0 e with he0 | he0
    · have hbase_up : (d.conductor : ℝ) * |s.im| ^ n ≤ K * d.analyticConductorAt s := by
        have h1 : (d.conductor : ℝ) * |s.im| ^ n ≤ C₁⁻¹ * d.analyticConductorAt s := by
          rw [le_inv_mul_iff₀ hC₁, ← mul_assoc]
          exact (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ ht_pos.le (by linarith) n) (by positivity)).trans hcond_lo
        exact h1.trans (mul_le_mul_of_nonneg_right
          ((le_max_left _ _).trans (le_max_right _ _)) hcond_pos.le)
      calc ((d.conductor : ℝ) * |s.im| ^ n) ^ e
          ≤ (K * d.analyticConductorAt s) ^ e :=
            Real.rpow_le_rpow (by positivity) hbase_up he0
        _ = K ^ e * d.analyticConductorAt s ^ e := Real.mul_rpow hK_pos.le hcond_pos.le
        _ ≤ K ^ E * d.analyticConductorAt s ^ e :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_le hK1 ((le_abs_self e).trans he_abs))
              (Real.rpow_nonneg hcond_pos.le e)
    · have hbase_lo : d.analyticConductorAt s / K ≤ (d.conductor : ℝ) * |s.im| ^ n := by
        rw [div_le_iff₀ hK_pos]
        have h4 : (|s.im| + 3) ^ n ≤ 4 ^ n * |s.im| ^ n := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) (by linarith) n
        calc d.analyticConductorAt s
            ≤ C₂ * (d.conductor : ℝ) * (4 ^ n * |s.im| ^ n) :=
              hcond_hi.trans (mul_le_mul_of_nonneg_left h4 (by positivity))
          _ = ((d.conductor : ℝ) * |s.im| ^ n) * (C₂ * 4 ^ n) := by ring
          _ ≤ ((d.conductor : ℝ) * |s.im| ^ n) * K :=
              mul_le_mul_of_nonneg_left
                ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)
      calc ((d.conductor : ℝ) * |s.im| ^ n) ^ e
          ≤ (d.analyticConductorAt s / K) ^ e :=
            Real.rpow_le_rpow_of_nonpos (div_pos hcond_pos hK_pos) hbase_lo he0
        _ = K ^ (-e) * d.analyticConductorAt s ^ e := by
            rw [Real.div_rpow hcond_pos.le hK_pos.le, div_eq_mul_inv, Real.rpow_neg hK_pos.le,
              mul_comm]
        _ ≤ K ^ E * d.analyticConductorAt s ^ e :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_exponent_le hK1 ((neg_le_abs e).trans he_abs))
              (Real.rpow_nonneg hcond_pos.le e)
  rw [norm_mul, hcond_norm]
  calc (d.conductor : ℝ) ^ e * ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖
      ≤ (d.conductor : ℝ) ^ e * (C_q * (|s.im| ^ n) ^ e) :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = C_q * ((d.conductor : ℝ) ^ e * (|s.im| ^ n) ^ e) := by ring
    _ ≤ C_q * (K ^ E * d.analyticConductorAt s ^ e) :=
        mul_le_mul_of_nonneg_left hrpow_cond hC_q.le
    _ = C_q * K ^ E * d.analyticConductorAt s ^ e := by ring

/-- Bound a shifted real-and-complex gamma-type product on a compact set `K` when `fR` and `fC`
are continuous on `K`. -/
private theorem exists_norm_gammaShiftProd_le_of_continuousOn {K : Set ℂ} (hK : IsCompact K)
    {fR fC : ℂ → ℂ} (hfR : ContinuousOn fR K) (hfC : ContinuousOn fC K) (n : ℕ) :
    ∃ B > 0, ∀ d : AnalyticLFunctionData, d.degree = n → ∀ z : ℂ,
      (∀ μ ∈ d.gammaR, z + μ ∈ K) → (∀ ν ∈ d.gammaC, z + ν ∈ K) →
        ‖(d.gammaR.map fun μ ↦ fR (z + μ)).prod *
            (d.gammaC.map fun ν ↦ fC (z + ν)).prod‖ ≤ B := by
  obtain ⟨bR, hbR⟩ := hK.exists_bound_of_continuousOn hfR
  obtain ⟨bC, hbC⟩ := hK.exists_bound_of_continuousOn hfC
  set U := max 1 (max bR bC)
  have hU1 : 1 ≤ U := le_max_left _ _
  refine ⟨U ^ n, by positivity, fun d hd z hR hC ↦ ?_⟩
  rw [norm_mul]
  have hpR := d.gammaR.norm_prod_map_le_pow_card (fun μ ↦ fR (z + μ)) (B := U) fun μ hμ ↦
    (hbR _ (hR μ hμ)).trans ((le_max_left bR bC).trans (le_max_right _ _))
  have hpC := d.gammaC.norm_prod_map_le_pow_card (fun ν ↦ fC (z + ν)) (B := U) fun ν hν ↦
    (hbC _ (hC ν hν)).trans ((le_max_right bR bC).trans (le_max_right _ _))
  have hcard : d.gammaR.card + d.gammaC.card ≤ n := by rw [← hd, degree_def]; omega
  exact (mul_le_mul hpR hpC (norm_nonneg _) (by positivity)).trans
    ((pow_add U d.gammaR.card d.gammaC.card).symm.le.trans (pow_le_pow_right₀ hU1 hcard))

/-- Uniform bound on `‖d.invGammaFactor s‖` when `‖s + μ‖ ≤ R` and `‖s + ν‖ ≤ R` for all shifts. -/
private theorem exists_norm_invGammaFactor_le_of_norm_le (n : ℕ) (R : ℝ) :
    ∃ B > 0, ∀ d : AnalyticLFunctionData, d.degree = n → ∀ s : ℂ,
      (∀ μ ∈ d.gammaR, ‖s + μ‖ ≤ R) → (∀ ν ∈ d.gammaC, ‖s + ν‖ ≤ R) →
        ‖d.invGammaFactor s‖ ≤ B := by
  obtain ⟨B, hB, h⟩ := exists_norm_gammaShiftProd_le_of_continuousOn
    (isCompact_closedBall (0 : ℂ) R) differentiable_Gammaℝ_inv.continuous.continuousOn
    differentiable_Gammaℂ_inv.continuous.continuousOn n
  refine ⟨B, hB, fun d hd s hR hC ↦ ?_⟩
  rw [d.invGammaFactor_eq_prod]
  exact h d hd s (fun μ hμ ↦ by simpa using hR μ hμ) (fun ν hν ↦ by simpa using hC ν hν)

/-- Uniform bound on `‖d.gammaFactor w‖` when all shifted arguments lie in
`Metric.closedBall 0 R ∩ {z | ε ≤ z.re}` (`ε > 0`). -/
private theorem exists_norm_gammaFactor_le_of_re_ge {ε : ℝ} (hε : 0 < ε) (n : ℕ) (R : ℝ) :
    ∃ B > 0, ∀ d : AnalyticLFunctionData, d.degree = n → ∀ w : ℂ,
      (∀ μ ∈ d.gammaR, ‖w + μ‖ ≤ R ∧ ε ≤ (w + μ).re) →
      (∀ ν ∈ d.gammaC, ‖w + ν‖ ≤ R ∧ ε ≤ (w + ν).re) →
        ‖d.gammaFactor w‖ ≤ B := by
  have hK : IsCompact (Metric.closedBall (0 : ℂ) R ∩ {z : ℂ | ε ≤ z.re}) :=
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const Complex.continuous_re)
  obtain ⟨B, hB, h⟩ := exists_norm_gammaShiftProd_le_of_continuousOn hK
    (fun z hz ↦
      (continuousAt_Gammaℝ (Gammaℝ_ne_zero_of_re_pos (hε.trans_le hz.2))).continuousWithinAt)
    (fun z hz ↦
      (continuousAt_Gammaℂ (Gammaℂ_ne_zero_of_re_pos (hε.trans_le hz.2))).continuousWithinAt)
    n
  refine ⟨B, hB, fun d hd w hR hC ↦ ?_⟩
  rw [gammaFactor_def]
  exact h d hd w
    (fun μ hμ ↦ ⟨by simpa using (hR μ hμ).1, (hR μ hμ).2⟩)
    (fun ν hν ↦ ⟨by simpa using (hC ν hν).1, (hC ν hν).2⟩)

/-- Compact-height strip helper: on `s.re ∈ [a, b]` with `|s.im| ≤ T`, if every shifted parameter
satisfies `ε ≤ 1 - b + Re μ` (`ε > 0`), then `‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖` is
bounded by a constant depending only on `a`, `b`, `ε`, `n`, `M`, and `T`. -/
private theorem exists_compact_dual_gammaFactor_div_strip_bound (a b : ℝ) {ε : ℝ} (hε : 0 < ε)
    (n : ℕ) (M T : ℝ) :
    ∃ B > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ ε ≤ 1 - b + μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ ε ≤ 1 - b + ν.re) →
      ∀ s : ℂ, s.re ∈ Icc a b → |s.im| ≤ T →
        ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ ≤ B := by
  set S := max |a| |b| + max T 0
  obtain ⟨B₁, hB₁, hinv⟩ := exists_norm_invGammaFactor_le_of_norm_le n (S + M)
  obtain ⟨B₂, hB₂, hgam⟩ := exists_norm_gammaFactor_le_of_re_ge hε n (1 + S + M)
  refine ⟨B₂ * B₁, mul_pos hB₂ hB₁, fun d hd hR hC s hs ht ↦ ?_⟩
  have hs_norm : ‖s‖ ≤ S := (norm_le_abs_re_add_abs_im s).trans
    (add_le_add (abs_le_max_abs_abs hs.1 hs.2) (ht.trans (le_max_left T 0)))
  have h1s_norm : ‖1 - s‖ ≤ 1 + S := (norm_sub_le 1 s).trans (by rw [norm_one]; linarith)
  have hinv_s := hinv d hd s
    (fun μ hμ ↦ (norm_add_le s μ).trans (add_le_add hs_norm (hR μ hμ).1))
    (fun ν hν ↦ (norm_add_le s ν).trans (add_le_add hs_norm (hC ν hν).1))
  have hdual_mem {μ : ℂ} (h : ‖μ‖ ≤ M ∧ ε ≤ 1 - b + μ.re) :
      ‖1 - s + conj μ‖ ≤ 1 + S + M ∧ ε ≤ (1 - s + conj μ).re :=
    ⟨(norm_add_le (1 - s) (conj μ)).trans (add_le_add h1s_norm (by simpa using h.1)),
      by simp only [add_re, sub_re, one_re, conj_re]; linarith [hs.2, h.2]⟩
  have hgam_s := hgam d.dual (by simpa using hd) (1 - s)
    (fun μ' hμ' ↦ by
      rw [dual_gammaR] at hμ'
      obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hμ'
      exact hdual_mem (hR μ hμ))
    (fun ν' hν' ↦ by
      rw [dual_gammaC] at hν'
      obtain ⟨ν, hν, rfl⟩ := Multiset.mem_map.mp hν'
      exact hdual_mem (hC ν hν))
  rw [div_eq_mul_inv, ← d.invGammaFactor_def, norm_mul]
  exact mul_le_mul hgam_s hinv_s (norm_nonneg _) hB₂.le

/-- **All-height conductor-uniform strip bound**: when the reflected shifts stay at least `ε > 0`
inside the open right half-plane throughout `Re s ∈ [a, b]` (`ε ≤ 1 - b + Re μ` and
`ε ≤ 1 - b + Re ν`), there is a single constant `C > 0` depending only on `a`, `b`, `ε`, `n`, and
`M` (independent of `d` and `d.conductor`) such that for **every** `s` with `s.re ∈ [a, b]`,
`‖N ^ (1 / 2 - s) (γ^∨(1 - s) / γ(s))‖ ≤ C * d.analyticConductorAt s ^ (1 / 2 - s.re)`. -/
theorem exists_norm_conductor_cpow_mul_dual_gammaFactor_div_strip_le_analyticConductorAt_rpow
    (a b : ℝ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ ε ≤ 1 - b + μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ ε ≤ 1 - b + ν.re) →
      ∀ s : ℂ, s.re ∈ Icc a b →
        ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
            (d.dual.gammaFactor (1 - s) / d.gammaFactor s)‖ ≤
          C * d.analyticConductorAt s ^ (1 / 2 - s.re) := by
  obtain ⟨C_tail, hCt, T, _, htail⟩ :=
    exists_norm_conductor_cpow_mul_dual_gammaFactor_div_le_analyticConductorAt_rpow a b n hM
  obtain ⟨B, _, hcomp⟩ := exists_compact_dual_gammaFactor_div_strip_bound a b hε n M T
  obtain ⟨_, _, C₂, hC₂, hstrip⟩ := exists_analyticConductorAt_strip_bounds a b n hM
  set L := max 1 (C₂ * (T + 3) ^ n)
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL_pos : 0 < L := zero_lt_one.trans_le hL1
  set E := max |1 / 2 - a| |1 / 2 - b|
  have hE0 : 0 ≤ E := (abs_nonneg _).trans (le_max_left _ _)
  refine ⟨max C_tail (B * L ^ E), lt_of_lt_of_le hCt (le_max_left _ _), fun d hd hR hC s hs ↦ ?_⟩
  have hcond_pos : 0 < d.analyticConductorAt s := d.analyticConductorAt_pos s
  rcases le_total T |s.im| with ht | ht
  · exact (htail d hd (fun μ hμ ↦ (hR μ hμ).1) (fun ν hν ↦ (hC ν hν).1) s hs ht).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · set e : ℝ := 1 / 2 - s.re
    have he_abs : |e| ≤ E := (abs_le_max_abs_abs (sub_le_sub_left hs.2 (1 / 2))
      (sub_le_sub_left hs.1 (1 / 2))).trans_eq (max_comm _ _)
    have hq := hcomp d hd hR hC s hs ht
    have hcond_norm : ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)‖ = (d.conductor : ℝ) ^ e := by
      rw [Complex.norm_natCast_cpow_of_pos d.conductor.pos]
      congr 1
      simp [e]
    have hcond_le : (d.conductor : ℝ) ^ e ≤ L ^ E * d.analyticConductorAt s ^ e := by
      rcases le_total 0 e with he0 | he0
      · have h1 : (1 : ℝ) ≤ 3 ^ d.degree := one_le_pow₀ (by norm_num)
        have hN_le : (d.conductor : ℝ) ≤ d.analyticConductorAt s :=
          (le_mul_of_one_le_right (Nat.cast_nonneg _) h1).trans
            (d.conductor_mul_three_pow_degree_le s)
        calc (d.conductor : ℝ) ^ e
            ≤ d.analyticConductorAt s ^ e := Real.rpow_le_rpow (Nat.cast_nonneg _) hN_le he0
          _ ≤ L ^ E * d.analyticConductorAt s ^ e :=
              le_mul_of_one_le_left (Real.rpow_nonneg hcond_pos.le e) (Real.one_le_rpow hL1 hE0)
      · have hhi := (hstrip d hd (fun μ hμ ↦ (hR μ hμ).1) (fun ν hν ↦ (hC ν hν).1) s hs).2
        have hdiv_le : d.analyticConductorAt s / L ≤ (d.conductor : ℝ) := by
          rw [div_le_iff₀ hL_pos]
          calc d.analyticConductorAt s
              ≤ C₂ * (d.conductor : ℝ) * (T + 3) ^ n :=
                hhi.trans (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (by positivity) (by linarith) n) (by positivity))
            _ = (d.conductor : ℝ) * (C₂ * (T + 3) ^ n) := by ring
            _ ≤ (d.conductor : ℝ) * L :=
                mul_le_mul_of_nonneg_left (le_max_right _ _) (Nat.cast_nonneg _)
        calc (d.conductor : ℝ) ^ e
            ≤ (d.analyticConductorAt s / L) ^ e :=
              Real.rpow_le_rpow_of_nonpos (div_pos hcond_pos hL_pos) hdiv_le he0
          _ = L ^ (-e) * d.analyticConductorAt s ^ e := by
              rw [Real.div_rpow hcond_pos.le hL_pos.le, div_eq_mul_inv, Real.rpow_neg hL_pos.le,
                mul_comm]
          _ ≤ L ^ E * d.analyticConductorAt s ^ e :=
              mul_le_mul_of_nonneg_right
                (Real.rpow_le_rpow_of_exponent_le hL1 ((neg_le_abs e).trans he_abs))
                (Real.rpow_nonneg hcond_pos.le e)
    rw [norm_mul, hcond_norm]
    calc (d.conductor : ℝ) ^ e * ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖
        ≤ (L ^ E * d.analyticConductorAt s ^ e) * B :=
          mul_le_mul hcond_le hq (norm_nonneg _) (by positivity)
      _ = (B * L ^ E) * d.analyticConductorAt s ^ e := by ring
      _ ≤ max C_tail (B * L ^ E) * d.analyticConductorAt s ^ e :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Specialization of
`exists_norm_conductor_cpow_mul_dual_gammaFactor_div_strip_le_analyticConductorAt_rpow` to strips
`Re s ∈ [a, b]` with `b < 1` and records whose gamma shifts have nonnegative real parts (`0 ≤ Re μ`,
`0 ≤ Re ν`). -/
theorem
  exists_norm_conductor_cpow_mul_dual_gammaFactor_div_strip_le_analyticConductorAt_rpow_of_re_nonneg
    (a : ℝ) {b : ℝ} (hb : b < 1) (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ 0 ≤ μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ 0 ≤ ν.re) →
      ∀ s : ℂ, s.re ∈ Icc a b →
        ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
            (d.dual.gammaFactor (1 - s) / d.gammaFactor s)‖ ≤
          C * d.analyticConductorAt s ^ (1 / 2 - s.re) := by
  obtain ⟨C, hC, h⟩ :=
    exists_norm_conductor_cpow_mul_dual_gammaFactor_div_strip_le_analyticConductorAt_rpow a b
      (sub_pos.2 hb) n hM
  exact ⟨C, hC, fun d hd hR hC' s hs ↦ h d hd
    (fun μ hμ ↦ ⟨(hR μ hμ).1, by linarith [(hR μ hμ).2]⟩)
    (fun ν hν ↦ ⟨(hC' ν hν).1, by linarith [(hC' ν hν).2]⟩) s hs⟩

/-- **All-height conductor-uniform edge bound on `Re s = -δ`** (for arbitrary `δ : ℝ`): when the
reflected shifts stay a positive distance `ε` inside the right half-plane (`ε ≤ 1 + δ + Re μ` and
`ε ≤ 1 + δ + Re ν`), there is a single constant `C > 0` depending only on `δ`, `ε`, `n`, and `M`
(independent of `d` and `d.conductor`) such that for **every** `t : ℝ`,
`‖N ^ (1 / 2 - (-δ + i t)) (γ^∨(1 - (-δ + i t)) / γ(-δ + i t))‖ ≤
  C * d.analyticConductorAt (-δ + i t) ^ (1 / 2 + δ)`. -/
theorem exists_norm_conductor_cpow_mul_dual_gammaFactor_div_neg_line_le_analyticConductorAt_rpow
    (δ : ℝ) {ε : ℝ} (hε : 0 < ε) (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ ε ≤ 1 + δ + μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ ε ≤ 1 + δ + ν.re) →
      ∀ t : ℝ,
        ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - ((-δ : ℝ) + t * I)) *
            (d.dual.gammaFactor (1 - ((-δ : ℝ) + t * I)) /
              d.gammaFactor ((-δ : ℝ) + t * I))‖ ≤
          C * d.analyticConductorAt ((-δ : ℝ) + t * I) ^ (1 / 2 + δ) := by
  obtain ⟨C, hC, h⟩ :=
    exists_norm_conductor_cpow_mul_dual_gammaFactor_div_strip_le_analyticConductorAt_rpow
      (-δ) (-δ) hε n hM
  refine ⟨C, hC, fun d hd hR hC' t ↦ ?_⟩
  simpa [sub_neg_eq_add] using h d hd
    (fun μ hμ ↦ ⟨(hR μ hμ).1, by linarith [(hR μ hμ).2]⟩)
    (fun ν hν ↦ ⟨(hC' ν hν).1, by linarith [(hC' ν hν).2]⟩)
    ((-δ : ℝ) + t * I) (by simp)

/-- All-height conductor-uniform vertical-line bound on `Re s = σ` (`σ < 1`, e.g. `σ = -δ` for any
`δ > -1`) for records whose gamma shifts have nonnegative real parts (`0 ≤ Re μ`, `0 ≤ Re ν`),
covering Riemann zeta, Dirichlet characters, Dedekind zeta, unitary Hecke characters, and
holomorphic newforms. -/
theorem
  exists_norm_conductor_cpow_mul_dual_gammaFactor_div_line_le_analyticConductorAt_rpow_of_re_nonneg
    {σ : ℝ} (hσ : σ < 1) (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ 0 ≤ μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ 0 ≤ ν.re) →
      ∀ t : ℝ,
        ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - (σ + t * I)) *
            (d.dual.gammaFactor (1 - (σ + t * I)) / d.gammaFactor (σ + t * I))‖ ≤
          C * d.analyticConductorAt (σ + t * I) ^ (1 / 2 - σ) := by
  obtain ⟨C, hC, h⟩ :=
  exists_norm_conductor_cpow_mul_dual_gammaFactor_div_strip_le_analyticConductorAt_rpow_of_re_nonneg
      σ hσ n hM
  refine ⟨C, hC, fun d hd hR hC' t ↦ ?_⟩
  simpa using h d hd hR hC' (σ + t * I) (by simp)

end TauCeti.LFunctions.AnalyticLFunctionData
