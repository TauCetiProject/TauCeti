/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.SpecialFunctions.Gamma.Barnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# The Mellin–Barnes integral of the Gauss hypergeometric function in `1 - z`

Along any vertical line `Re s = σ` avoiding the poles of all four Gamma factors, Stirling's
vertical-line bound gives `O(exp (-r |y|))` decay for every `r < 2π` of the four-Gamma weight

`Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s),    s = σ + i y`.

Because the principal branch satisfies `|(1 - z).arg| ≤ π < 2π` for every `z : ℂ`, the
Mellin–Barnes integrand

`y ↦ Γ(a + (σ + i y)) Γ(b + (σ + i y)) Γ(c - a - b - (σ + i y)) Γ(-(σ + i y)) (1 - z)^{σ + i y}`

is Bochner integrable on `ℝ` at *every* complex `z` (`integrable_...`), and on the cut plane
`{z : ℂ | 1 - z ∈ Complex.slitPlane}` where `z ↦ (1 - z)^s` avoids the branch cut of the principal
logarithm, the vertical integral is complex differentiable with explicit derivative under the
integral sign (`hasDerivAt_integral_...`, `differentiableOn_integral_...`) and hence holomorphic
(`analyticOnNhd_integral_...`). Notice that all four regularity statements hold on *any* pole-free
vertical line `Re s = σ`, not only on lines that separate the left- and right-half-plane poles, so
they apply unchanged to contours shifted across finitely many poles.

When `Re s = σ` does separate the poles of `Γ(a + s) Γ(b + s)` from those of
`Γ(c - a - b - s) Γ(-s)`, namely

`max (-Re a, -Re b) < σ < min (0, Re (c - a - b))`,

and `‖z‖ < 1`, expanding `(1 - z)^s = ∑_{n = 0}^∞ multichoose (-s) n z^n`, writing
`Γ(-s) multichoose (-s) n = Γ(n - s) / n!`, dominating `‖Γ(n - s)‖ ≤ Γ(-σ + n)` uniformly in `y`
via `Complex.norm_Gamma_le_Gamma_re`, and integrating term-by-term with Barnes's first lemma
(`Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`) yields the Mellin–Barnes
representation ([DLMF 15.6.7](https://dlmf.nist.gov/15.6.E7)) of Olver's regularized Gauss function
`Complex.regularizedGaussHGFun a b c z` and of `₂F₁ a b c z` on the open unit disk. Note that no
non-integrality hypothesis on `c` is required even in the `₂F₁` form, since adding the four
separating-strip inequalities already forces `0 < Re c`.

## Main results

* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow`: Bochner integrability
  on `ℝ` for every `z : ℂ` along any pole-free vertical line `Re s = σ`.
* `Complex.hasDerivAt_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow`,
  `Complex.differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow`,
  `Complex.analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow`:
  differentiation under the integral sign and holomorphy on `{z : ℂ | 1 - z ∈ slitPlane}` along
  any pole-free vertical line `Re s = σ`.
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow`,
  `Complex.regularizedGaussHGFun_eq_integral_one_sub_cpow`: **DLMF 15.6.7** on `‖z‖ < 1` for the
  regularized Gauss hypergeometric function.
* `Complex.ordinaryHypergeometric_eq_integral_one_sub_cpow`: **DLMF 15.6.7** on `‖z‖ < 1` for the
  ordinary Gauss hypergeometric function `₂F₁ a b c z`.

## References

* [NIST Digital Library of Mathematical Functions, 15.6.7](https://dlmf.nist.gov/15.6.E7).
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.51–14.52.
-/

public section

open Real Set MeasureTheory Filter
open scoped Nat Topology

namespace Complex

/-- Along any vertical line `Re s = σ` avoiding the poles of all four factors, the four-Gamma
weight of the `1 - z` Mellin–Barnes integral is continuous. -/
private lemma continuous_mellinBarnesOneSubWeight {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) := by
  have ha' : ∀ n : ℕ, (a + σ).re ≠ -n := by simpa using ha
  have hb' : ∀ n : ℕ, (b + σ).re ≠ -n := by simpa using hb
  have hc' : ∀ n : ℕ, (c - a - b - σ).re ≠ -n := by simpa using hc
  have hd' : ∀ n : ℕ, (-(σ : ℂ)).re ≠ -n := fun n h ↦
    hσ n (neg_inj.mp (by simpa using h))
  have heq : (fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))) =
      fun y : ℝ ↦
        Gamma ((a + σ) + y * I) * Gamma ((b + σ) + y * I) *
          Gamma ((c - a - b - σ) - y * I) * Gamma (-(σ : ℂ) - y * I) := by
    ext y
    have e1 : a + ((σ : ℂ) + y * I) = (a + σ) + y * I := by ring
    have e2 : b + ((σ : ℂ) + y * I) = (b + σ) + y * I := by ring
    have e3 : c - a - b - ((σ : ℂ) + y * I) = (c - a - b - σ) - y * I := by ring
    have e4 : -((σ : ℂ) + y * I) = -(σ : ℂ) - y * I := by ring
    rw [e1, e2, e3, e4]
  rw [heq]
  exact (((continuous_Gamma_add_mul_I ha').mul (continuous_Gamma_add_mul_I hb')).mul
    (continuous_Gamma_sub_mul_I hc')).mul (continuous_Gamma_sub_mul_I hd')

/-- Along any vertical line `Re s = σ` avoiding the poles of all four factors, the four-Gamma
weight of the `1 - z` Mellin–Barnes integral decays as `O(exp (-r |y|))` for every `r < 2π`. -/
private lemma exists_norm_mellinBarnesOneSubWeight_le_mul_exp {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n)
    {r : ℝ} (hr : r < 2 * Real.pi) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
        C * Real.exp (-r * |y|) := by
  have ha' : ∀ n : ℕ, (a + σ).re ≠ -n := by simpa using ha
  have hb' : ∀ n : ℕ, (b + σ).re ≠ -n := by simpa using hb
  have hc' : ∀ n : ℕ, (c - a - b - σ).re ≠ -n := by simpa using hc
  have hd' : ∀ n : ℕ, (-(σ : ℂ)).re ≠ -n := fun n h ↦
    hσ n (neg_inj.mp (by simpa using h))
  obtain ⟨C, hC0, hC⟩ :=
    exists_norm_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_le_mul_exp ha' hb' hc' hd' hr
  refine ⟨C, hC0, fun y ↦ ?_⟩
  have e1 : a + ((σ : ℂ) + y * I) = (a + σ) + y * I := by ring
  have e2 : b + ((σ : ℂ) + y * I) = (b + σ) + y * I := by ring
  have e3 : c - a - b - ((σ : ℂ) + y * I) = (c - a - b - σ) - y * I := by ring
  have e4 : -((σ : ℂ) + y * I) = -(σ : ℂ) - y * I := by ring
  rw [e1, e2, e3, e4]
  exact hC y

/-- Along any vertical line `Re s = σ` avoiding the poles of all four Gamma factors, the `1 - z`
Mellin–Barnes integrand is Bochner integrable on `ℝ` for *every* `z : ℂ` (including on the branch
cut `[1, ∞)`, since the four-Gamma weight decays at rate `< 2π` while `|(1 - z).arg| ≤ π`). -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) (z : ℂ) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) := by
  obtain ⟨C, _, hC⟩ := exists_norm_mellinBarnesOneSubWeight_le_mul_exp ha hb hc hσ
    (r := 3 * Real.pi / 2) (by linarith [Real.pi_pos])
  have harg : |(1 - z).arg| < 3 * Real.pi / 2 :=
    (abs_arg_le_pi (1 - z)).trans_lt (by linarith [Real.pi_pos])
  exact TauCeti.integrable_mul_cpow_add_mul_I_of_norm_le_exp
    (continuous_mellinBarnesOneSubWeight ha hb hc hσ).aestronglyMeasurable harg hC

/-- **Differentiation under the `1 - z` Mellin–Barnes integral.** Along any pole-free vertical line
`Re s = σ` and at any `z : ℂ` off the branch cut `[1, ∞)` (`1 - z ∈ slitPlane`), the vertical
integral has complex derivative obtained by differentiating `(1 - z)^s` under the integral sign. -/
theorem hasDerivAt_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow
    {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n)
    {z : ℂ} (hz : 1 - z ∈ slitPlane) :
    HasDerivAt
      (fun w : ℂ ↦ ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - w) ^ (σ + y * I))
      (-(∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          ((σ + y * I) * (1 - z) ^ (σ + y * I - 1))))
      z := by
  obtain ⟨C, _, hC⟩ := exists_norm_mellinBarnesOneSubWeight_le_mul_exp ha hb hc hσ
    (r := 3 * Real.pi / 2) (by linarith [Real.pi_pos])
  have harg : |(1 - z).arg| < 3 * Real.pi / 2 :=
    (abs_arg_le_pi (1 - z)).trans_lt (by linarith [Real.pi_pos])
  have hF := TauCeti.hasDerivAt_integral_mul_cpow_add_mul_I_of_norm_le_exp (σ := σ)
    (continuous_mellinBarnesOneSubWeight ha hb hc hσ).aestronglyMeasurable hz harg hC
  have hsub : HasDerivAt (fun w : ℂ ↦ 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  exact (hF.comp z hsub).congr_deriv (mul_neg_one _)

/-- Along any pole-free vertical line `Re s = σ`, the `1 - z` Mellin–Barnes integral is complex
differentiable on the cut plane `{z : ℂ | 1 - z ∈ slitPlane}`. -/
theorem differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow
    {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    DifferentiableOn ℂ
      (fun z : ℂ ↦ ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I))
      {z : ℂ | 1 - z ∈ slitPlane} :=
  fun _ hz ↦
    (hasDerivAt_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow ha hb hc hσ
      hz).differentiableAt.differentiableWithinAt

/-- Along any pole-free vertical line `Re s = σ`, the `1 - z` Mellin–Barnes integral is holomorphic
on the cut plane `{z : ℂ | 1 - z ∈ slitPlane}`. -/
theorem analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow
    {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    AnalyticOnNhd ℂ
      (fun z : ℂ ↦ ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I))
      {z : ℂ | 1 - z ∈ slitPlane} :=
  (differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow ha hb hc
    hσ).analyticOnNhd (isOpen_slitPlane.preimage (by fun_prop))

/-- **Mellin–Barnes integral of the regularized Gauss hypergeometric function in `1 - z`**
([DLMF 15.6.7](https://dlmf.nist.gov/15.6.E7), unnormalized form). When `Re s = σ` separates the
poles of `Γ(a + s) Γ(b + s)` from those of `Γ(c - a - b - s) Γ(-s)` and `‖z‖ < 1`,
`(1 / 2π) ∫ Γ(a + (σ + i y)) Γ(b + (σ + i y)) Γ(c - a - b - (σ + i y)) Γ(-(σ + i y))
  (1 - z)^{σ + i y} dy = Γ(a) Γ(b) Γ(c - a) Γ(c - b) regularizedGaussHGFun a b c z`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow
    {a b c : ℂ} {σ : ℝ}
    (haσ : -a.re < σ) (hbσ : -b.re < σ) (hσ0 : σ < 0) (hσc : σ < (c - a - b).re)
    {z : ℂ} (hz : ‖z‖ < 1) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) =
      Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b) * regularizedGaussHGFun a b c z := by
  have ha_pos : 0 < a.re := by linarith
  have hb_pos : 0 < b.re := by linarith
  have ha_ne : ∀ k : ℕ, a ≠ -k := ne_neg_natCast_of_re_pos ha_pos
  have hb_ne : ∀ k : ℕ, b ≠ -k := ne_neg_natCast_of_re_pos hb_pos
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha_pos
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb_pos
  let s : ℝ → ℂ := fun y ↦ (σ : ℂ) + y * I
  let W : ℝ → ℂ := fun y ↦ Gamma (a + s y) * Gamma (b + s y) * Gamma (c - a - b - s y)
  let F : ℕ → ℝ → ℂ := fun n y ↦ (z ^ n / (n ! : ℂ)) * (W y * Gamma ((n : ℂ) - s y))
  -- Rewrite `F n y` in terms of `Ring.multichoose (-(s y)) n` to sum the binomial series in `n`.
  have hF_eq (n : ℕ) (y : ℝ) :
      F n y = W y * Gamma (-(s y)) * (Ring.multichoose (-(s y)) n * z ^ n) := by
    have hs_pos : 0 < (-(s y)).re := by simp [s]; linarith
    have hs_ne : ∀ k : ℕ, -(s y) ≠ -k := ne_neg_natCast_of_re_pos hs_pos
    have hΓs : Gamma (-(s y)) ≠ 0 := Gamma_ne_zero_of_re_pos hs_pos
    have hpoch := Gamma_add_nat_div_Gamma_eq (n := n) (-(s y)) hs_ne
    rw [div_eq_iff hΓs, show -(s y) + (n : ℂ) = (n : ℂ) - s y by ring] at hpoch
    have hmc := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (-(s y)) n
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at hmc
    have hfac : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    dsimp only [F]
    rw [hpoch, ← hmc]
    field_simp [hfac]
  -- Pointwise in `y`, `∑' n, F n y` sums to the `1 - z` Mellin–Barnes integrand.
  have htsum_pt (y : ℝ) : (∑' n : ℕ, F n y) =
      W y * Gamma (-(s y)) * (1 - z) ^ (s y) := by
    simp_rw [hF_eq]
    have hsum := (TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one
      (r := -(s y)) hz).mul_left (W y * Gamma (-(s y)))
    rw [hsum.tsum_eq, one_div, cpow_neg, inv_inv]
  -- Integrability of each term `F n` and of the three-Gamma envelope `‖W y‖`.
  have haσ_ne : ∀ k : ℕ, (a + σ).re ≠ -k := fun k h ↦ by
    simp only [add_re, ofReal_re] at h; linarith [k.cast_nonneg' (α := ℝ)]
  have hbσ_ne : ∀ k : ℕ, (b + σ).re ≠ -k := fun k h ↦ by
    simp only [add_re, ofReal_re] at h; linarith [k.cast_nonneg' (α := ℝ)]
  have hcσ_ne : ∀ k : ℕ, (c - a - b - σ).re ≠ -k := fun k h ↦ by
    simp only [sub_re, ofReal_re] at h hσc; linarith [k.cast_nonneg' (α := ℝ)]
  have hF_int (n : ℕ) : Integrable (F n) volume := by
    have hnσ_ne : ∀ k : ℕ, ((n : ℂ) - σ).re ≠ -k := fun k h ↦ by
      simp only [sub_re, natCast_re, ofReal_re] at h
      linarith [n.cast_nonneg' (α := ℝ), k.cast_nonneg' (α := ℝ)]
    have hint := (integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma
      haσ_ne hbσ_ne hcσ_ne hnσ_ne).const_mul (z ^ n / (n ! : ℂ))
    refine hint.congr (Eventually.of_forall fun y ↦ ?_)
    dsimp only [F, W, s]
    have e1 : a + (σ : ℂ) + y * I = a + ((σ : ℂ) + y * I) := by ring
    have e2 : b + (σ : ℂ) + y * I = b + ((σ : ℂ) + y * I) := by ring
    have e3 : c - a - b - (σ : ℂ) - y * I = c - a - b - ((σ : ℂ) + y * I) := by ring
    have e4 : (n : ℂ) - (σ : ℂ) - y * I = (n : ℂ) - ((σ : ℂ) + y * I) := by ring
    rw [e1, e2, e3, e4]
  have hW_int : Integrable (fun y : ℝ ↦ ‖W y‖) volume := by
    have hcont : Continuous fun y : ℝ ↦ W y := by
      have heq : (fun y : ℝ ↦ W y) = fun y : ℝ ↦
          Gamma ((a + σ) + y * I) * Gamma ((b + σ) + y * I) *
            Gamma ((c - a - b - σ) - y * I) := by
        ext y; dsimp only [W, s]
        have e1 : a + ((σ : ℂ) + y * I) = (a + σ) + y * I := by ring
        have e2 : b + ((σ : ℂ) + y * I) = (b + σ) + y * I := by ring
        have e3 : c - a - b - ((σ : ℂ) + y * I) = (c - a - b - σ) - y * I := by ring
        rw [e1, e2, e3]
      rw [heq]
      exact ((continuous_Gamma_add_mul_I haσ_ne).mul (continuous_Gamma_add_mul_I hbσ_ne)).mul
        (continuous_Gamma_sub_mul_I hcσ_ne)
    obtain ⟨C₁, _, h₁⟩ := exists_norm_Gamma_add_mul_I_le_mul_exp haσ_ne
      (c := Real.pi / 4) (by linarith [Real.pi_pos])
    obtain ⟨C₂, _, h₂⟩ := exists_norm_Gamma_add_mul_I_le_mul_exp hbσ_ne
      (c := 0) (by positivity)
    obtain ⟨C₃, _, h₃⟩ := exists_norm_Gamma_sub_mul_I_le_mul_exp hcσ_ne
      (c := 0) (by positivity)
    have hpi4 : 0 < Real.pi / 4 := by positivity
    refine ((TauCeti.integrable_exp_neg_mul_abs hpi4).const_mul
      (C₁ * C₂ * C₃)).mono' hcont.norm.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    dsimp only [W, s]
    have e1 : a + ((σ : ℂ) + y * I) = (a + σ) + y * I := by ring
    have e2 : b + ((σ : ℂ) + y * I) = (b + σ) + y * I := by ring
    have e3 : c - a - b - ((σ : ℂ) + y * I) = (c - a - b - σ) - y * I := by ring
    rw [e1, e2, e3, norm_mul, norm_mul]
    have h12 : ‖Gamma ((a + σ) + y * I)‖ * ‖Gamma ((b + σ) + y * I)‖ ≤
        (C₁ * Real.exp (-(Real.pi / 4) * |y|)) * (C₂ * Real.exp (-0 * |y|)) :=
      mul_le_mul (h₁ y) (h₂ y) (norm_nonneg _) (by positivity)
    calc ‖Gamma ((a + σ) + y * I)‖ * ‖Gamma ((b + σ) + y * I)‖ *
          ‖Gamma ((c - a - b - σ) - y * I)‖
        ≤ (C₁ * Real.exp (-(Real.pi / 4) * |y|)) * (C₂ * Real.exp (-0 * |y|)) *
            (C₃ * Real.exp (-0 * |y|)) :=
          mul_le_mul h12 (h₃ y) (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * C₃ * Real.exp (-(Real.pi / 4 * |y|)) := by
          simp only [neg_zero, zero_mul, Real.exp_zero, mul_one, neg_mul]
          ring
  -- Dominate `∫ y, ‖F n y‖` uniformly by the real binomial series at `r = -σ > 0`.
  have hF_sum : Summable fun n : ℕ ↦ ∫ y : ℝ, ‖F n y‖ := by
    have hσ_pos : 0 < -σ := neg_pos.mpr hσ0
    have hσ_ne_real : ∀ k : ℕ, -σ ≠ -(k : ℝ) := fun k h ↦ by linarith [k.cast_nonneg' (α := ℝ)]
    have hΓσ_pos : 0 < Real.Gamma (-σ) := Real.Gamma_pos_of_pos hσ_pos
    have hbin_sum : Summable fun n : ℕ ↦
        (Real.Gamma (-σ) * ∫ y : ℝ, ‖W y‖) * (Ring.multichoose (-σ) n * ‖z‖ ^ n) :=
      (TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (r := -σ)
        (by rwa [abs_norm])).summable.mul_left _
    refine Summable.of_nonneg_of_le (fun n ↦ integral_nonneg fun y ↦ norm_nonneg _)
      (fun n ↦ ?_) hbin_sum
    have hGamma_real : Real.Gamma (-σ + n) / (n ! : ℝ) =
        Real.Gamma (-σ) * Ring.multichoose (-σ) n := by
      have hp := Real.Gamma_add_nat_div_Gamma_eq (n := n) (-σ) hσ_ne_real
      rw [div_eq_iff hΓσ_pos.ne'] at hp
      have hmc := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (-σ) n
      rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at hmc
      have hfac : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
      rw [hp, ← hmc]
      field_simp [hfac]
    have hpt (y : ℝ) : ‖F n y‖ ≤
        (Real.Gamma (-σ) * (Ring.multichoose (-σ) n * ‖z‖ ^ n)) * ‖W y‖ := by
      have hre : ((n : ℂ) - s y).re = -σ + n := by simp [s]; ring
      have hΓle : ‖Gamma ((n : ℂ) - s y)‖ ≤ Real.Gamma (-σ + n) := by
        rw [← hre]
        exact norm_Gamma_le_Gamma_re (by rw [hre]; linarith [n.cast_nonneg' (α := ℝ)])
      dsimp only [F]
      rw [norm_mul, norm_div, norm_pow, norm_natCast, norm_mul]
      calc (‖z‖ ^ n / (n ! : ℝ)) * (‖W y‖ * ‖Gamma ((n : ℂ) - s y)‖)
          ≤ (‖z‖ ^ n / (n ! : ℝ)) * (‖W y‖ * Real.Gamma (-σ + n)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hΓle (norm_nonneg _)) (by positivity)
        _ = (Real.Gamma (-σ + n) / (n ! : ℝ)) * ‖z‖ ^ n * ‖W y‖ := by ring
        _ = (Real.Gamma (-σ) * (Ring.multichoose (-σ) n * ‖z‖ ^ n)) * ‖W y‖ := by
            rw [hGamma_real]; ring
    calc (∫ y : ℝ, ‖F n y‖)
        ≤ ∫ y : ℝ, (Real.Gamma (-σ) * (Ring.multichoose (-σ) n * ‖z‖ ^ n)) * ‖W y‖ :=
          integral_mono (hF_int n).norm (hW_int.const_mul _) hpt
      _ = (Real.Gamma (-σ) * ∫ y : ℝ, ‖W y‖) * (Ring.multichoose (-σ) n * ‖z‖ ^ n) := by
          rw [integral_const_mul]; ring
  -- Swap `∫` and `∑'`, then evaluate each `n`-th integral by Barnes's first lemma.
  have hint_eq : (∫ y : ℝ,
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I)) =
      ∑' n : ℕ, ∫ y : ℝ, F n y := by
    rw [integral_tsum_of_summable_integral_norm hF_int hF_sum]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    exact (htsum_pt y).symm
  rw [hint_eq, ← tsum_mul_left]
  have hterm (n : ℕ) : (2 * π : ℂ)⁻¹ * (∫ y : ℝ, F n y) =
      (Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b)) *
        ((a.regularizedGaussHGFunSeries b c).coeff n • z ^ n) := by
    dsimp only [F, W, s]
    rw [integral_const_mul, ← mul_assoc, mul_comm ((2 * π : ℂ)⁻¹), mul_assoc]
    have hbarnes := integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub
      (a := a) (b := b) (c := c - a - b) (d := (n : ℂ)) (σ := σ)
      haσ hbσ hσc (by simp; linarith [n.cast_nonneg' (α := ℝ)])
    rw [hbarnes]
    have hpa := Gamma_add_nat_div_Gamma_eq (n := n) a ha_ne
    rw [div_eq_iff hΓa] at hpa
    have hpb := Gamma_add_nat_div_Gamma_eq (n := n) b hb_ne
    rw [div_eq_iff hΓb] at hpb
    have hc1 : a + (c - a - b) = c - b := by ring
    have hc2 : b + (c - a - b) = c - a := by ring
    have hc3 : a + b + (c - a - b) + (n : ℂ) = c + n := by ring
    rw [hc1, hc2, hc3, hpa, hpb, coeff_regularizedGaussHGFunSeries, smul_eq_mul]
    ring
  simp_rw [hterm, tsum_mul_left]
  congr 1
  rw [regularizedGaussHGFun, regularizedGaussHGFunSeries, regularizedHGFunSeries,
    ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq]
  refine tsum_congr fun n ↦ ?_
  simp

/-- **Mellin–Barnes integral representation of `Complex.regularizedGaussHGFun` in `1 - z`**
([DLMF 15.6.7](https://dlmf.nist.gov/15.6.E7)). When `Re s = σ` separates the poles of
`Γ(a + s) Γ(b + s)` from those of `Γ(c - a - b - s) Γ(-s)` and `‖z‖ < 1`,
`regularizedGaussHGFun a b c z` equals `(2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹` times the vertical
integral of `Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s) (1 - z)^s`. -/
theorem regularizedGaussHGFun_eq_integral_one_sub_cpow
    {a b c : ℂ} {σ : ℝ}
    (haσ : -a.re < σ) (hbσ : -b.re < σ) (hσ0 : σ < 0) (hσc : σ < (c - a - b).re)
    {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ * ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) := by
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hΓca : Gamma (c - a) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp only [sub_re] at hσc ⊢; linarith)
  have hΓcb : Gamma (c - b) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp only [sub_re] at hσc ⊢; linarith)
  have h2pi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have h := integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow haσ hbσ hσ0 hσc hz
  generalize (∫ y : ℝ,
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I)) = J at h ⊢
  have hprod : Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hΓa hΓb) hΓca) hΓcb
  apply mul_left_cancel₀ hprod
  rw [← h]
  field_simp [h2pi, hΓa, hΓb, hΓca, hΓcb]

/-- **Mellin–Barnes integral representation of `₂F₁` in `1 - z`**
([DLMF 15.6.7](https://dlmf.nist.gov/15.6.E7), ordinary Gauss form). When `Re s = σ` separates the
poles of `Γ(a + s) Γ(b + s)` from those of `Γ(c - a - b - s) Γ(-s)` and `‖z‖ < 1`,
`₂F₁ a b c z = Γ(c) / (2π Γ(a) Γ(b) Γ(c - a) Γ(c - b)) * ∫ Γ(a + s) Γ(b + s) Γ(c - a - b - s)
  Γ(-s) (1 - z)^s dy`. Note that no extra `c ∉ -ℕ` assumption is needed, since the four separating
inequalities automatically force `0 < Re c`. -/
theorem ordinaryHypergeometric_eq_integral_one_sub_cpow
    {a b c : ℂ} {σ : ℝ}
    (haσ : -a.re < σ) (hbσ : -b.re < σ) (hσ0 : σ < 0) (hσc : σ < (c - a - b).re)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ a b c z =
      Gamma c / (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b)) * ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) := by
  have hc_pos : 0 < c.re := by simp only [sub_re] at hσc; linarith
  have hc_ne : ∀ k : ℕ, c ≠ -k := ne_neg_natCast_of_re_pos hc_pos
  have hΓc : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc_pos
  have hdiv := ordinaryHypergeometric_div_Gamma_eq (a := a) (b := b) (z := z) hc_ne
  rw [div_eq_iff hΓc, regularizedGaussHGFun_eq_integral_one_sub_cpow haσ hbσ hσ0 hσc hz] at hdiv
  rw [hdiv]
  ring

-- Normalization check at `a = b = 1`, `c = 3`, `σ = -1 / 2`, `z = 0`: `₂F₁ 1 1 3 0 = 1`, so the
-- normalized Mellin–Barnes integral equals `1`.
example :
    Gamma 3 / (2 * π * Gamma 1 * Gamma 1 * Gamma (3 - 1) * Gamma (3 - 1)) * ∫ y : ℝ,
        Gamma (1 + ((-1 / 2 : ℝ) + y * I)) * Gamma (1 + ((-1 / 2 : ℝ) + y * I)) *
          Gamma (3 - 1 - 1 - ((-1 / 2 : ℝ) + y * I)) * Gamma (-((-1 / 2 : ℝ) + y * I)) *
          (1 - (0 : ℂ)) ^ ((-1 / 2 : ℝ) + y * I) = 1 := by
  have h := ordinaryHypergeometric_eq_integral_one_sub_cpow
    (a := 1) (b := 1) (c := 3) (σ := -1 / 2) (z := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [← h, ordinaryHypergeometric_zero]

end Complex
