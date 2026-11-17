/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.RingTheory.Binomial
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.MellinInversion
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Mellin–Barnes integrals for the Gauss hypergeometric function

The Gauss hypergeometric function admits two classical Mellin–Barnes contour representations along
vertical lines `s = σ + i y` separating left-opening and right-opening Gamma pole sequences
([DLMF 15.6.6](https://dlmf.nist.gov/15.6.E6) and [DLMF 15.6.7](https://dlmf.nist.gov/15.6.E7)):

* In powers of `-z` on `{z : ℂ | -z ∈ Complex.slitPlane}` (`ℂ \ [0, ∞)`), with `-Re a < σ < 0` and
  `-Re b < σ`, the Gamma kernel `Γ(a + s) Γ(b + s) Γ(-s) (Γ(c + s))⁻¹` combines three decaying
  Gamma factors (`e^{-3π |y| / 2}`) with one entire reciprocal Gamma factor (`e^{π |y| / 2}`),
  giving net vertical decay `O((1 + |y|) ^ R e^{-π |y|})`, which dominates the `e^{|arg (-z)| |y|}`
  growth of `(-z) ^ s` on `{z | -z ∈ Complex.slitPlane}`. Its integral defines a function
  holomorphic in `z` on `{z | -z ∈ Complex.slitPlane}` and entire in `c` on `ℂ`, and its normalized
  integral `(2π Γ(a) Γ(b))⁻¹ ∫_ℝ Γ(a + s) Γ(b + s) Γ(-s) (Γ(c + s))⁻¹ (-z) ^ s dy` equals
  `Complex.eulerIntegral a b c z` whenever `Re b < Re c`.
* In powers of `1 - z` on `{z : ℂ | 1 - z ∈ Complex.slitPlane}` (`ℂ \ [1, ∞)`), with
  `-Re a < σ < 0`, `-Re b < σ`, and `σ < Re(c - a - b)`, the four-Gamma kernel
  `Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s)` decays like `O((1 + |y|) ^ R e^{-2π |y|})`, which
  dominates the `e^{|arg (1 - z)| |y|}` growth of `(1 - z) ^ s` for every `z : ℂ`. Its normalized
  integral is holomorphic on the entire cut plane `{z | 1 - z ∈ Complex.slitPlane}`, equals
  `Complex.eulerIntegral a b c z` throughout that cut plane, and equals Mathlib's
  `Complex.regularizedGaussHGFun a b c z` (hence also `(Γ c)⁻¹ ₂F₁(a, b; c; z)`) on the open unit
  disk `‖z‖ < 1`.

On the cut plane, both representations of `Complex.eulerIntegral` follow by inserting the
slit-plane Mellin–Barnes integral of `(1 + w) ^ (-a)` into Euler's integral (directly with
`w = t (-z)` for DLMF 15.6.6, and after factoring `1 - z t = (1 - t) (1 + t (1 - t)⁻¹ (1 - z))`
for DLMF 15.6.7) and exchanging the `0..1` and `ℝ` integrals via Fubini's theorem. On the unit
disk, `Complex.regularizedGaussHGFun_eq_mellinBarnes_one_sub` expands `(1 - w) ^ s` on
`‖w‖ < 1 / 2` in its multichoose binomial series, interchanges summation and integration using the
`e^{-2π |y|}` decay against `2 ^ ‖s‖ ≤ 2 ^ |σ| e^{(log 2) |y|}`, evaluates each term by Barnes's
first lemma (`Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`), and extends
from `‖w‖ < 1 / 2` to `‖w‖ < 1` by analytic continuation.

## Main results

* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow`,
  `Complex.differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow`,
  `Complex.analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow`,
  `Complex.differentiable_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow_denom`:
  integrability, holomorphy in `z` on `{z | -z ∈ Complex.slitPlane}`, and entirety in `c : ℂ` of
  the Mellin–Barnes integral in `-z`.
* `Complex.eulerIntegral_eq_mellinBarnes`: DLMF 15.6.6 for `Complex.eulerIntegral` on
  `{z | -z ∈ Complex.slitPlane}` when `Re b < Re c` and `-min(Re a, Re b) < σ < 0`.
* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow`,
  `Complex.differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow`,
  `Complex.analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow`:
  integrability for every `z : ℂ` and holomorphy in `z` on `{z | 1 - z ∈ Complex.slitPlane}` of
  the Mellin–Barnes integral in `1 - z`.
* `Complex.eulerIntegral_eq_mellinBarnes_one_sub`: DLMF 15.6.7 for `Complex.eulerIntegral` on the
  entire cut plane `{z | 1 - z ∈ Complex.slitPlane}`.
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_multichoose`: Barnes-lemma
  evaluation of the `n`-th multichoose moment of the DLMF 15.6.7 four-Gamma kernel.
* `Complex.regularizedGaussHGFun_eq_mellinBarnes_one_sub`,
  `Complex.ordinaryHypergeometric_eq_mellinBarnes_one_sub`: DLMF 15.6.7 on the open unit disk
  `‖z‖ < 1` for `Complex.regularizedGaussHGFun` and `Complex.ordinaryHypergeometric`.

## References

* [NIST Digital Library of Mathematical Functions, §15.6(ii)](https://dlmf.nist.gov/15.6.ii),
  equations 15.6.6 and 15.6.7.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.5–14.52.
-/

public section

noncomputable section

open Complex Filter Function MeasureTheory Set
open scoped Nat Real Topology

namespace Complex

/-! ### Shared private helpers for vertical Gamma bounds and Fubini integrability -/

/-- Continuity and `O((1 + |y|)^{Re a + Re b + σ - 3/2} e^{-3π |y| / 2})` vertical decay for the
common three-Gamma factor `y ↦ Γ(a + s) Γ(b + s) Γ(-s)` along `s = σ + i y`. -/
private theorem continuous_and_norm_threeGamma_le {a b : ℂ} {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Continuous (fun y : ℝ ↦
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))) ∧
      ∃ C > 0, ∀ y : ℝ,
        ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
          C * (1 + |y|) ^ (a.re + b.re + σ - 3 / 2) * Real.exp (-(3 * π / 2) * |y|) := by
  have ha' : ∀ n : ℕ, (a + σ).re ≠ -n := by simpa [add_re] using haσ
  have hb' : ∀ n : ℕ, (b + σ).re ≠ -n := by simpa [add_re] using hbσ
  have hσ' : ∀ n : ℕ, ((-σ : ℝ) : ℂ).re ≠ -n := by simpa using hσ
  have e1 (y : ℝ) : a + ((σ : ℂ) + y * I) = (a + σ) + y * I := by ring
  have e2 (y : ℝ) : b + ((σ : ℂ) + y * I) = (b + σ) + y * I := by ring
  have e3 (y : ℝ) : -((σ : ℂ) + y * I) = ((-σ : ℝ) : ℂ) - y * I := by push_cast; ring
  have hcont : Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) := by
    simp only [e1, e2, e3]
    exact ((continuous_Gamma_add_mul_I ha').mul (continuous_Gamma_add_mul_I hb')).mul
      (continuous_Gamma_sub_mul_I hσ')
  obtain ⟨C₁, hC₁, h₁⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le ha'
  obtain ⟨C₂, hC₂, h₂⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le hb'
  obtain ⟨C₃, _, h₃⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hσ'
  refine ⟨hcont, C₁ * C₂ * C₃, by positivity, fun y ↦ ?_⟩
  have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
  have b1 := h₁ y; simp only [add_re, ofReal_re, ← e1] at b1
  have b2 := h₂ y; simp only [add_re, ofReal_re, ← e2] at b2
  have b3 := h₃ y; simp only [ofReal_re, ← e3] at b3
  rw [norm_mul, norm_mul]
  calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ * ‖Gamma (-(σ + y * I))‖
      ≤ (C₁ * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₂ * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₃ * (1 + |y|) ^ (-σ - 1 / 2) * Real.exp (-π * |y| / 2)) :=
        mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) (by positivity)) b3
          (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * C₃ * ((1 + |y|) ^ (a.re + σ - 1 / 2) * (1 + |y|) ^ (b.re + σ - 1 / 2) *
          (1 + |y|) ^ (-σ - 1 / 2)) *
        (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2)) := by ring
    _ = _ := by
        rw [← Real.rpow_add h1y, ← Real.rpow_add h1y, ← Real.exp_add, ← Real.exp_add]; ring_nf

/-- Shared Fubini integrability on `(0, 1] × ℝ` for Beta-times-Mellin–Barnes integrands whose
exponents `u y` and `v y` have constant positive real parts `u₀` and `v₀`. -/
private theorem integrable_uncurry_beta_mul_mellinBarnes {a w : ℂ} {σ u₀ v₀ : ℝ}
    {u v : ℝ → ℂ} (hu_cont : Continuous u) (hv_cont : Continuous v)
    (hu_re : ∀ y, (u y).re = u₀) (hv_re : ∀ y, (v y).re = v₀)
    (hu₀ : 0 < u₀) (hv₀ : 0 < v₀) (hσ_ne : ∀ n : ℕ, -σ ≠ -n)
    (haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n) (hw : w ∈ slitPlane) :
    Integrable (uncurry fun t y : ℝ ↦ (t : ℂ) ^ (u y - 1) * (1 - (t : ℂ)) ^ (v y - 1) *
        (Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * w ^ ((σ : ℂ) + y * I)))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) := by
  have hmeas_oo : (volume.restrict (uIoc (0 : ℝ) 1)).prod (volume : Measure ℝ) =
      ((volume : Measure ℝ).prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ univ) := by
    rw [uIoc_of_le zero_le_one, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    simpa only [Measure.restrict_univ] using
      Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (Ioo 0 1) univ
  have hφ : Integrable (fun t : ℝ ↦
      ‖(t : ℂ) ^ ((u₀ : ℂ) - 1) * (1 - (t : ℂ)) ^ ((v₀ : ℂ) - 1)‖)
      (volume.restrict (uIoc 0 1)) :=
    (intervalIntegrable_iff.1 (betaIntegral_convergent (u := u₀) (v := v₀)
      (by simpa using hu₀) (by simpa using hv₀))).norm
  have hψ : Integrable (fun y : ℝ ↦
      ‖Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * w ^ ((σ : ℂ) + y * I)‖) volume :=
    (integrable_Gamma_add_mul_Gamma_neg_mul_cpow hσ_ne haσ_ne hw).norm
  have hF_meas : AEStronglyMeasurable
      (uncurry fun t y : ℝ ↦ (t : ℂ) ^ (u y - 1) * (1 - (t : ℂ)) ^ (v y - 1) *
        (Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * w ^ ((σ : ℂ) + y * I)))
      ((volume.restrict (uIoc 0 1)).prod volume) := by
    rw [hmeas_oo]
    refine ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ).prod volume)
      (fun ⟨t, y⟩ ⟨⟨ht0, ht1⟩, _⟩ ↦ ?_) (measurableSet_Ioo.prod MeasurableSet.univ)
    have h1t_slit : 1 - (t : ℂ) ∈ slitPlane := by
      rw [← ofReal_one, ← ofReal_sub]; exact ofReal_mem_slitPlane.2 (sub_pos.2 ht1)
    have hG1 : Continuous fun y : ℝ ↦ Gamma (a + ((σ : ℂ) + y * I)) := by
      simpa only [show ∀ y : ℝ, a + ((σ : ℂ) + y * I) = (a + σ) + y * I by intro; ring] using
        continuous_Gamma_add_mul_I (a := a + σ) (by simpa [add_re] using haσ_ne)
    have hG2 : Continuous fun y : ℝ ↦ Gamma (-((σ : ℂ) + y * I)) := by
      simpa only [show ∀ y : ℝ, -((σ : ℂ) + y * I) = ((-σ : ℝ) : ℂ) - y * I by
        intro; push_cast; ring] using
        continuous_Gamma_sub_mul_I (a := (-σ : ℝ)) (by simpa using hσ_ne)
    refine (((ContinuousAt.cpow (by fun_prop) ((hu_cont.sub continuous_const).continuousAt.comp
        continuousAt_snd) (ofReal_mem_slitPlane.2 ht0)).mul
      (ContinuousAt.cpow (by fun_prop) ((hv_cont.sub continuous_const).continuousAt.comp
        continuousAt_snd) h1t_slit)).mul
      (((hG1.continuousAt.comp continuousAt_snd).mul (hG2.continuousAt.comp continuousAt_snd)).mul
        (ContinuousAt.cpow continuousAt_const (by fun_prop) hw))).continuousWithinAt
  refine (hφ.mul_prod hψ).mono' hF_meas ?_
  rw [hmeas_oo]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with
    ⟨t, y⟩ ⟨⟨ht0, ht1⟩, _⟩
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  dsimp only [uncurry]
  rw [← ofReal_one, ← ofReal_sub]
  simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos h1t,
    sub_re, ofReal_re, hu_re, hv_re]
  exact le_rfl

/-! ### Mellin–Barnes integral in `-z` (DLMF 15.6.6) -/

/-- Continuity and `O((1 + |y|) ^ (Re a + Re b - Re c - 1) e^{-π |y|})` vertical bound for the
Gamma kernel `y ↦ Γ(a + s) Γ(b + s) Γ(-s) (Γ(c + s))⁻¹` on `s = σ + i y`. -/
private theorem continuous_and_norm_mellinBarnesNegKernel_le (c : ℂ) {a b : ℂ} {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Continuous (fun y : ℝ ↦
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹) ∧
      ∃ C > 0, ∀ y : ℝ,
        ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
            Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹‖ ≤
          C * (1 + |y|) ^ (a.re + b.re - c.re - 1) * Real.exp (-π * |y|) := by
  obtain ⟨h3_cont, C₃, hC₃, h3⟩ := continuous_and_norm_threeGamma_le haσ hbσ hσ
  obtain ⟨C₄, _, h₄⟩ := TauCeti.exists_norm_inv_Gamma_add_mul_I_le (c + σ)
  have hinv_cont : Continuous fun w : ℂ ↦ (Gamma w)⁻¹ := by
    simpa only [one_div] using differentiable_one_div_Gamma.continuous
  refine ⟨h3_cont.mul (hinv_cont.comp (by fun_prop)), C₃ * C₄, by positivity, fun y ↦ ?_⟩
  have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
  have b4 := h₄ y
  simp only [show c + (σ : ℂ) + y * I = c + ((σ : ℂ) + y * I) by ring, add_re, ofReal_re] at b4
  rw [norm_mul]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
        ‖(Gamma (c + (σ + y * I)))⁻¹‖
      ≤ (C₃ * (1 + |y|) ^ (a.re + b.re + σ - 3 / 2) * Real.exp (-(3 * π / 2) * |y|)) *
          (C₄ * (1 + |y|) ^ (1 / 2 - (c.re + σ)) * Real.exp (π * |y| / 2)) :=
        mul_le_mul (h3 y) b4 (norm_nonneg _) (by positivity)
    _ = C₃ * C₄ * ((1 + |y|) ^ (a.re + b.re + σ - 3 / 2) * (1 + |y|) ^ (1 / 2 - (c.re + σ))) *
          (Real.exp (-(3 * π / 2) * |y|) * Real.exp (π * |y| / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add h1y, ← Real.exp_add]; ring_nf

/-- For `-z ∈ Complex.slitPlane`, arbitrary `c : ℂ`, and any vertical line `Re s = σ` avoiding the
poles of `Γ(a + s)`, `Γ(b + s)`, and `Γ(-s)`, the Mellin–Barnes integrand of DLMF 15.6.6 is
integrable on `ℝ`. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow
    (c : ℂ) {a b z : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) (hz : -z ∈ slitPlane) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  obtain ⟨hcont, C, _, hbound⟩ := continuous_and_norm_mellinBarnesNegKernel_le c haσ hbσ hσ
  exact (TauCeti.integrable_cpow_smul_of_norm_le_exp_neg_mul_abs
    hcont.aestronglyMeasurable ⟨C, a.re + b.re - c.re - 1, Eventually.of_forall hbound⟩ σ
    (abs_arg_lt_pi_of_mem_slitPlane hz)).congr
      (Eventually.of_forall fun _ ↦ by simp [smul_eq_mul, mul_comm])

/-- The Mellin–Barnes integral in `-z` (DLMF 15.6.6) is complex differentiable in `z` on the cut
plane `{z : ℂ | -z ∈ Complex.slitPlane}` (`ℂ \ [0, ∞)`). -/
theorem differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow
    (c : ℂ) {a b : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) :
    DifferentiableOn ℂ (fun z : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I))
      {z : ℂ | -z ∈ slitPlane} := by
  obtain ⟨hcont, C, _, hbound⟩ := continuous_and_norm_mellinBarnesNegKernel_le c haσ hbσ hσ
  refine ((TauCeti.differentiableOn_integral_cpow_smul
    hcont.aestronglyMeasurable ⟨C, a.re + b.re - c.re - 1, Eventually.of_forall hbound⟩ σ).comp
      differentiableOn_id.neg fun _ hz ↦ ⟨hz, abs_arg_lt_pi_of_mem_slitPlane hz⟩).congr fun _ _ ↦
    integral_congr_ae (Eventually.of_forall fun _ ↦ by simp [smul_eq_mul, mul_comm])

/-- The Mellin–Barnes integral in `-z` (DLMF 15.6.6) is holomorphic in `z` on the cut plane
`{z : ℂ | -z ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow
    (c : ℂ) {a b : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I))
      {z : ℂ | -z ∈ slitPlane} :=
  (differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow
    c haσ hbσ hσ).analyticOnNhd (isOpen_slitPlane.preimage continuous_neg)

/-- For fixed `a, b, z` with `-z ∈ Complex.slitPlane` and pole-free `σ`, the Mellin–Barnes
integral of DLMF 15.6.6 is an entire function of the denominator parameter `c : ℂ`. -/
theorem differentiable_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow_denom
    {a b z : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) (hz : -z ∈ slitPlane) :
    Differentiable ℂ fun c : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  intro c₀
  obtain ⟨h3_cont, C₃, hC₃, h3⟩ := continuous_and_norm_threeGamma_le haσ hbσ hσ
  obtain ⟨C₄, _, h₄⟩ :=
    TauCeti.exists_norm_deriv_inv_Gamma_closedBall_add_mul_I_le (c₀ + (σ : ℂ)) 1
  have hinvG : Differentiable ℂ fun w : ℂ ↦ (Gamma w)⁻¹ := by
    simpa only [one_div] using differentiable_one_div_Gamma
  let h : ℝ → ℂ := fun y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (-(σ + y * I)) * (-z) ^ ((σ : ℂ) + y * I)
  have hh_cont : Continuous h :=
    h3_cont.mul (Continuous.const_cpow (by fun_prop) (Or.inl (slitPlane_ne_zero hz)))
  set δ : ℝ := π - |(-z).arg|
  have hδ : 0 < δ := sub_pos.2 (abs_arg_lt_pi_of_mem_slitPlane hz)
  set K : ℝ := C₃ * ‖-z‖ ^ σ * C₄
  set r' : ℝ := 3 / 2 - (c₀ + (σ : ℂ)).re + 1
  set R : ℝ := a.re + b.re + σ - 3 / 2 + r'
  have hF_meas : ∀ᶠ c in 𝓝 c₀, AEStronglyMeasurable (fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I)) :=
    Eventually.of_forall fun c ↦
      ((continuous_and_norm_mellinBarnesNegKernel_le c haσ hbσ hσ).1.mul
        (Continuous.const_cpow (by fun_prop) (Or.inl (slitPlane_ne_zero hz)))).aestronglyMeasurable
  -- Differentiate under the integral sign on `Metric.ball c₀ 1`.
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (c : ℂ) (y : ℝ) ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I))
    (F' := fun (c : ℂ) (y : ℝ) ↦
      h y * deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (c + ((σ : ℂ) + y * I)))
    (bound := fun y : ℝ ↦ K * ((1 + |y|) ^ R * Real.exp (-δ * |y|)))
    (Metric.ball_mem_nhds c₀ one_pos) hF_meas
    (integrable_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow c₀ haσ hbσ hσ hz)
    (hh_cont.mul ((hinvG.contDiff.continuous_deriv le_rfl).comp (by fun_prop))).aestronglyMeasurable
    ?_ ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs R hδ).const_mul K) ?_).2
      |>.differentiableAt
  · refine Eventually.of_forall fun y c hc ↦ ?_
    have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
    have bpow : ‖(-z) ^ ((σ : ℂ) + y * I)‖ ≤ ‖-z‖ ^ σ * Real.exp ((π - δ) * |y|) := by
      simpa [δ] using norm_cpow_le_rpow_mul_exp_abs_arg_mul_abs_im (-z) ((σ : ℂ) + y * I)
    have h4y : ‖deriv (fun u : ℂ ↦ (Gamma u)⁻¹) (c + ((σ : ℂ) + y * I))‖ ≤
        C₄ * (1 + |y|) ^ r' * Real.exp (π * |y| / 2) := by
      rw [← add_assoc]
      exact h₄ (c + (σ : ℂ))
        (by rw [Metric.mem_closedBall, dist_add_right]; exact (Metric.mem_ball.1 hc).le) y
    dsimp [h]
    rw [norm_mul, norm_mul]
    calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          ‖(-z) ^ ((σ : ℂ) + y * I)‖ *
          ‖deriv (fun u : ℂ ↦ (Gamma u)⁻¹) (c + ((σ : ℂ) + y * I))‖
        ≤ (C₃ * (1 + |y|) ^ (a.re + b.re + σ - 3 / 2) * Real.exp (-(3 * π / 2) * |y|)) *
            (‖-z‖ ^ σ * Real.exp ((π - δ) * |y|)) *
            (C₄ * (1 + |y|) ^ r' * Real.exp (π * |y| / 2)) :=
          mul_le_mul (mul_le_mul (h3 y) bpow (norm_nonneg _) (by positivity)) h4y
            (norm_nonneg _) (by positivity)
      _ = K * ((1 + |y|) ^ (a.re + b.re + σ - 3 / 2) * (1 + |y|) ^ r') *
            (Real.exp (-(3 * π / 2) * |y|) * Real.exp ((π - δ) * |y|) * Real.exp (π * |y| / 2)) :=
          by dsimp [K]; ring
      _ = _ := by
          rw [← Real.rpow_add h1y, ← Real.exp_add, ← Real.exp_add]; dsimp [R]; ring_nf
  · refine Eventually.of_forall fun y c _ ↦ ?_
    have hd : HasDerivAt (fun u : ℂ ↦ (Gamma (u + ((σ : ℂ) + y * I)))⁻¹)
        (deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (c + ((σ : ℂ) + y * I))) c := by
      simpa [Function.comp_def] using
        (hinvG.differentiableAt.hasDerivAt).comp c ((hasDerivAt_id' c).add_const _)
    exact (hd.const_mul (h y)).congr_of_eventuallyEq
      (Eventually.of_forall fun _ ↦ by dsimp [h]; ring)

/-- Pointwise Mellin–Barnes expansion of the Euler integrand for `t > 0` and
`-z ∈ Complex.slitPlane`, used in the Fubini proof of DLMF 15.6.6. -/
private theorem mul_eulerIntegrand_eq_integral_mellinBarnes {a b c z : ℂ} {σ t : ℝ}
    (hz : -z ∈ slitPlane) (hσ : σ < 0) (haσ : -a.re < σ) (ht : 0 < t) :
    Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (t : ℂ) ^ (b + (σ + y * I) - 1) *
        (1 - (t : ℂ)) ^ (c - b - 1) *
          (Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * (-z) ^ (σ + y * I)) := by
  rw [show 1 - z * (t : ℂ) = 1 + (t : ℂ) * (-z) by ring, mul_left_comm (Gamma a),
    ← integral_Gamma_add_mul_Gamma_neg_mul_cpow hσ haσ (TauCeti.ofReal_mul_mem_slitPlane ht hz),
    ← mul_left_comm ((2 * π : ℂ)⁻¹), ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [TauCeti.ofReal_mul_cpow ht.le,
    ← show (t : ℂ) ^ (b - 1) * (t : ℂ) ^ ((σ : ℂ) + y * I) =
        (t : ℂ) ^ (b + ((σ : ℂ) + y * I) - 1) by
      rw [← cpow_add _ _ (ofReal_ne_zero.2 ht.ne')]; congr 1; ring]
  ring

/-- **Mellin–Barnes integral for Euler's hypergeometric integral in `-z` (DLMF 15.6.6).**
For `Re b < Re c`, `-z ∈ Complex.slitPlane`, and `-min(Re a, Re b) < σ < 0`,
`Complex.eulerIntegral a b c z = (2π Γ(a) Γ(b))⁻¹ ∫_ℝ Γ(a + s) Γ(b + s) Γ(-s) (Γ(c + s))⁻¹ (-z)^s`
along `s = σ + i y`. -/
theorem eulerIntegral_eq_mellinBarnes {a b c z : ℂ} {σ : ℝ}
    (hbc : b.re < c.re) (hz : -z ∈ slitPlane)
    (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    eulerIntegral a b c z =
      (2 * π * Gamma a * Gamma b)⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  have hcb : 0 < (c - b).re := by simp only [sub_re]; linarith
  have hbσ_pos : 0 < b.re + σ := by linarith
  have hσ_ne : ∀ n : ℕ, -σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  let s : ℝ → ℂ := fun y ↦ (σ : ℂ) + y * I
  let F : ℝ → ℝ → ℂ := fun t y ↦
    (t : ℂ) ^ (b + s y - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
      (Gamma (a + s y) * Gamma (-s y) * (-z) ^ s y)
  -- Substitute the Mellin–Barnes representation pointwise on `(0, 1]` and exchange integrals.
  have hpoint : ∫ t : ℝ in 0..1,
        Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      (2 * π : ℂ)⁻¹ * ∫ t : ℝ in 0..1, ∫ y : ℝ, F t y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
    rw [uIoc_of_le zero_le_one] at ht
    exact mul_eulerIntegrand_eq_integral_mellinBarnes hz hσ haσ ht.1
  have hF_int : Integrable (uncurry F) ((volume.restrict (uIoc 0 1)).prod volume) :=
    integrable_uncurry_beta_mul_mellinBarnes (u := fun y ↦ b + s y) (v := fun _ ↦ c - b)
      (by fun_prop) continuous_const (fun _ ↦ by simp [s, add_re]) (fun _ ↦ rfl)
      hbσ_pos hcb hσ_ne haσ_ne hz
  -- Evaluate the inner `t`-integral as Euler's Beta function `B(b + s, c - b)`.
  have hinner (y : ℝ) : ∫ t : ℝ in 0..1, F t y =
      Gamma (c - b) * (Gamma (a + s y) * Gamma (b + s y) * Gamma (-s y) *
        (Gamma (c + s y))⁻¹ * (-z) ^ s y) := by
    dsimp [F]
    rw [intervalIntegral.integral_mul_const, ← betaIntegral,
      betaIntegral_eq_Gamma_mul_div (b + s y) (c - b) (by simpa [s, add_re] using hbσ_pos) hcb,
      show b + s y + (c - b) = c + s y by ring, div_eq_mul_inv]
    ring
  rw [intervalIntegral.integral_const_mul, intervalIntegral_integral_swap hF_int] at hpoint
  simp_rw [hinner, integral_const_mul] at hpoint
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hI : (∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * t) ^ (-a)) =
      (Gamma a)⁻¹ * ((2 * π : ℂ)⁻¹ * (Gamma (c - b) *
        ∫ y : ℝ, Gamma (a + s y) * Gamma (b + s y) * Gamma (-s y) *
          (Gamma (c + s y))⁻¹ * (-z) ^ s y)) := by rw [← hpoint, inv_mul_cancel_left₀ hΓa]
  rw [eulerIntegral_def, hI]
  dsimp only [s]
  generalize (∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
    Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I)) = J
  field_simp [hΓa, hΓb, hΓcb, hpi]

/-! ### Mellin–Barnes integral in `1 - z` (DLMF 15.6.7) -/

/-- Continuity and `O((1 + |y|) ^ (Re c - 2) e^{-2π |y|})` vertical decay for the four-Gamma
kernel `y ↦ Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s)` on `s = σ + i y`. -/
private theorem continuous_and_norm_mellinBarnesOneSubKernel_le {a b c : ℂ} {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hcab : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Continuous (fun y : ℝ ↦
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))) ∧
      ∃ C > 0, ∀ y : ℝ,
        ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
            Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
          C * (1 + |y|) ^ (c.re - 2) * Real.exp (-(2 * π) * |y|) := by
  have hcab' : ∀ n : ℕ, (c - a - b - σ).re ≠ -n := by simpa [sub_re] using hcab
  obtain ⟨h3_cont, C₃, hC₃, h3⟩ := continuous_and_norm_threeGamma_le haσ hbσ hσ
  obtain ⟨C₄, _, h₄⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hcab'
  have e3 (y : ℝ) : c - a - b - ((σ : ℂ) + y * I) = (c - a - b - σ) - y * I := by ring
  have h4_cont : Continuous fun y : ℝ ↦ Gamma (c - a - b - ((σ : ℂ) + y * I)) := by
    simpa only [e3] using continuous_Gamma_sub_mul_I hcab'
  have hreord (y : ℝ) :
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) =
        (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))) *
          Gamma (c - a - b - (σ + y * I)) := by ring
  refine ⟨by simp only [hreord]; exact h3_cont.mul h4_cont, C₃ * C₄, by positivity, fun y ↦ ?_⟩
  have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
  have b4 := h₄ y; simp only [sub_re, ofReal_re, ← e3] at b4
  rw [hreord, norm_mul]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
        ‖Gamma (c - a - b - (σ + y * I))‖
      ≤ (C₃ * (1 + |y|) ^ (a.re + b.re + σ - 3 / 2) * Real.exp (-(3 * π / 2) * |y|)) *
          (C₄ * (1 + |y|) ^ (c.re - a.re - b.re - σ - 1 / 2) * Real.exp (-π * |y| / 2)) :=
        mul_le_mul (h3 y) b4 (norm_nonneg _) (by positivity)
    _ = C₃ * C₄ * ((1 + |y|) ^ (a.re + b.re + σ - 3 / 2) *
          (1 + |y|) ^ (c.re - a.re - b.re - σ - 1 / 2)) *
          (Real.exp (-(3 * π / 2) * |y|) * Real.exp (-π * |y| / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add h1y, ← Real.exp_add]; ring_nf

/-- For every `z : ℂ` and any vertical line `Re s = σ` avoiding the poles of `Γ(a + s)`,
`Γ(b + s)`, `Γ(c - a - b - s)`, and `Γ(-s)`, the Mellin–Barnes integrand of DLMF 15.6.7 is
integrable on `ℝ`. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow
    {a b c z : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hcab : ∀ n : ℕ, (c - a - b).re - σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) := by
  obtain ⟨hcont, C, _, hbound⟩ :=
    continuous_and_norm_mellinBarnesOneSubKernel_le haσ hbσ hcab hσ
  exact (TauCeti.integrable_cpow_smul_of_norm_le_exp_neg_mul_abs (α := 2 * π)
    hcont.aestronglyMeasurable ⟨C, c.re - 2, Eventually.of_forall hbound⟩ σ
    ((abs_arg_le_pi (1 - z)).trans_lt (by linarith [Real.pi_pos]))).congr
      (Eventually.of_forall fun _ ↦ by simp [smul_eq_mul, mul_comm])

/-- The Mellin–Barnes integral in `1 - z` (DLMF 15.6.7) is complex differentiable in `z` on the
entire cut plane `{z : ℂ | 1 - z ∈ Complex.slitPlane}` (`ℂ \ [1, ∞)`). -/
theorem differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow
    {a b c : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hcab : ∀ n : ℕ, (c - a - b).re - σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    DifferentiableOn ℂ (fun z : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I))
      {z : ℂ | 1 - z ∈ slitPlane} := by
  obtain ⟨hcont, C, _, hbound⟩ :=
    continuous_and_norm_mellinBarnesOneSubKernel_le haσ hbσ hcab hσ
  refine ((TauCeti.differentiableOn_integral_cpow_smul (α := 2 * π)
    hcont.aestronglyMeasurable ⟨C, c.re - 2, Eventually.of_forall hbound⟩ σ).comp
      (differentiableOn_const (1 : ℂ) |>.sub differentiableOn_id)
      fun _ hz ↦ ⟨hz, (abs_arg_le_pi _).trans_lt (by linarith [Real.pi_pos])⟩).congr fun _ _ ↦
    integral_congr_ae (Eventually.of_forall fun _ ↦ by simp [smul_eq_mul, mul_comm])

/-- The Mellin–Barnes integral in `1 - z` (DLMF 15.6.7) is holomorphic in `z` on the entire cut
plane `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow
    {a b c : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hcab : ∀ n : ℕ, (c - a - b).re - σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I))
      {z : ℂ | 1 - z ∈ slitPlane} :=
  (differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow
    haσ hbσ hcab hσ).analyticOnNhd
      (isOpen_slitPlane.preimage (continuous_const.sub continuous_id))

/-- Pointwise Mellin–Barnes expansion of the Euler integrand in powers of `1 - z` for `t ∈ (0, 1)`
and `1 - z ∈ Complex.slitPlane`, used in the Fubini proof of DLMF 15.6.7. -/
private theorem mul_eulerIntegrand_eq_integral_mellinBarnes_one_sub {a b c z : ℂ} {σ t : ℝ}
    (hz : 1 - z ∈ slitPlane) (hσ : σ < 0) (haσ : -a.re < σ) (ht0 : 0 < t) (ht1 : t < 1) :
    Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (t : ℂ) ^ (b + (σ + y * I) - 1) *
        (1 - (t : ℂ)) ^ (c - a - b - (σ + y * I) - 1) *
          (Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I)) := by
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
  have h1t_ne : (1 - (t : ℂ)) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub]; exact ofReal_ne_zero.2 h1t.ne'
  set q : ℝ := t / (1 - t)
  have hq : 0 < q := div_pos ht0 h1t
  have hfact : 1 - z * (t : ℂ) = ((1 - t : ℝ) : ℂ) * (1 + (q : ℂ) * (1 - z)) := by
    have h1t_ne' : ((1 - t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 h1t.ne'
    dsimp [q]; push_cast; field_simp [h1t_ne']; ring
  have hcpow_fact : (1 - z * (t : ℂ)) ^ (-a) =
      (1 - (t : ℂ)) ^ (-a) * (1 + (q : ℂ) * (1 - z)) ^ (-a) := by
    rw [hfact, TauCeti.ofReal_mul_cpow h1t.le]; push_cast; rfl
  rw [hcpow_fact, show Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
      ((1 - (t : ℂ)) ^ (-a) * (1 + (q : ℂ) * (1 - z)) ^ (-a))) =
    ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - (t : ℂ)) ^ (-a)) *
      (Gamma a * (1 + (q : ℂ) * (1 - z)) ^ (-a)) by ring,
    ← integral_Gamma_add_mul_Gamma_neg_mul_cpow hσ haσ (TauCeti.ofReal_mul_mem_slitPlane hq hz),
    ← mul_left_comm ((2 * π : ℂ)⁻¹), ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  have hq_pow : (q : ℂ) ^ ((σ : ℂ) + y * I) =
      (t : ℂ) ^ ((σ : ℂ) + y * I) * (1 - (t : ℂ)) ^ (-((σ : ℂ) + y * I)) := by
    dsimp [q]
    rw [ofReal_div, div_cpow_ofReal_nonneg ht0.le h1t.le, div_eq_mul_inv, ← cpow_neg,
      ofReal_sub, ofReal_one]
  have hpow_t : (t : ℂ) ^ (b - 1) * (t : ℂ) ^ ((σ : ℂ) + y * I) =
      (t : ℂ) ^ (b + ((σ : ℂ) + y * I) - 1) := by rw [← cpow_add _ _ ht_ne]; congr 1; ring
  have hpow_1t : (1 - (t : ℂ)) ^ (c - b - 1) * (1 - (t : ℂ)) ^ (-a) *
      (1 - (t : ℂ)) ^ (-((σ : ℂ) + y * I)) =
      (1 - (t : ℂ)) ^ (c - a - b - ((σ : ℂ) + y * I) - 1) := by
    rw [← cpow_add _ _ h1t_ne, ← cpow_add _ _ h1t_ne]; congr 1; ring
  dsimp only
  rw [TauCeti.ofReal_mul_cpow hq.le, hq_pow, ← hpow_t, ← hpow_1t]; ring

/-- **Mellin–Barnes integral for Euler's hypergeometric integral in `1 - z` (DLMF 15.6.7).**
On the entire cut plane `1 - z ∈ Complex.slitPlane`, for any vertical line `Re s = σ` separating
the left-opening poles of `Γ(a + s) Γ(b + s)` from the right-opening poles of
`Γ(c - a - b - s) Γ(-s)` (`-min(Re a, Re b) < σ < min(0, Re(c - a - b))`),
`Complex.eulerIntegral a b c z = (2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫_ℝ Γ(a + s) Γ(b + s)
  Γ(c - a - b - s) Γ(-s) (1 - z)^s`. -/
theorem eulerIntegral_eq_mellinBarnes_one_sub {a b c z : ℂ} {σ : ℝ}
    (hz : 1 - z ∈ slitPlane) (hσ : σ < 0) (hcab : σ < (c - a - b).re)
    (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    eulerIntegral a b c z =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - z) ^ (σ + y * I) := by
  have hcb : 0 < (c - b).re := by simp only [sub_re] at hcab ⊢; linarith
  have hca : 0 < (c - a).re := by simp only [sub_re] at hcab ⊢; linarith
  have hbσ_pos : 0 < b.re + σ := by linarith
  have hcab_pos : 0 < (c - a - b).re - σ := by linarith
  have hσ_ne : ∀ n : ℕ, -σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  let s : ℝ → ℂ := fun y ↦ (σ : ℂ) + y * I
  let F : ℝ → ℝ → ℂ := fun t y ↦
    (t : ℂ) ^ (b + s y - 1) * (1 - (t : ℂ)) ^ (c - a - b - s y - 1) *
      (Gamma (a + s y) * Gamma (-s y) * (1 - z) ^ s y)
  -- Substitute the Mellin–Barnes representation pointwise on `(0, 1)` and exchange integrals.
  have hpoint : ∫ t : ℝ in 0..1,
        Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      (2 * π : ℂ)⁻¹ * ∫ t : ℝ in 0..1, ∫ y : ℝ, F t y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Ioo_ae_eq_Ioc] with t ht ht_mem
    rw [uIoc_of_le zero_le_one] at ht_mem
    obtain ⟨ht0, ht1⟩ := ht.2 ht_mem
    exact mul_eulerIntegrand_eq_integral_mellinBarnes_one_sub hz hσ haσ ht0 ht1
  have hF_int : Integrable (uncurry F) ((volume.restrict (uIoc 0 1)).prod volume) :=
    integrable_uncurry_beta_mul_mellinBarnes (u := fun y ↦ b + s y)
      (v := fun y ↦ c - a - b - s y) (by fun_prop) (by fun_prop)
      (fun _ ↦ by simp [s, add_re]) (fun _ ↦ by simp [s, sub_re])
      hbσ_pos hcab_pos hσ_ne haσ_ne hz
  -- Evaluate the inner `t`-integral as Euler's Beta function `B(b + s, c - a - b - s)`.
  have hinner (y : ℝ) : ∫ t : ℝ in 0..1, F t y =
      (Gamma (a + s y) * Gamma (b + s y) * Gamma (c - a - b - s y) *
        Gamma (-s y) * (1 - z) ^ s y) / Gamma (c - a) := by
    dsimp [F]
    rw [intervalIntegral.integral_mul_const, ← betaIntegral,
      betaIntegral_eq_Gamma_mul_div (b + s y) (c - a - b - s y)
        (by simpa [s, add_re] using hbσ_pos) (by simpa [s, sub_re] using hcab_pos),
      show b + s y + (c - a - b - s y) = c - a by ring]
    ring
  rw [intervalIntegral.integral_const_mul, intervalIntegral_integral_swap hF_int] at hpoint
  simp_rw [hinner, integral_div] at hpoint
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hΓca : Gamma (c - a) ≠ 0 := Gamma_ne_zero_of_re_pos hca
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hI : (∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * t) ^ (-a)) =
      (Gamma a)⁻¹ * ((2 * π : ℂ)⁻¹ *
        ((∫ y : ℝ, Gamma (a + s y) * Gamma (b + s y) *
          Gamma (c - a - b - s y) * Gamma (-s y) * (1 - z) ^ s y) / Gamma (c - a))) := by
    rw [← hpoint, inv_mul_cancel_left₀ hΓa]
  rw [eulerIntegral_def, hI]
  dsimp only [s]
  generalize (∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
    Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I)) = J
  field_simp [hΓa, hΓb, hΓca, hΓcb, hpi]

/-- **Multichoose moment of the DLMF 15.6.7 four-Gamma kernel.** For any `n : ℕ` and any vertical
line `s = σ + i y` with `-min(Re a, Re b) < σ < min(0, Re(c - a - b))`,
`(2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫_ℝ Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s)
  (Ring.multichoose (-s) n) dy = (a)_n (b)_n / (n! Γ(c + n))`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_multichoose
    {a b c : ℂ} {σ : ℝ} (hσ : σ < 0) (hcab : σ < (c - a - b).re)
    (haσ : -a.re < σ) (hbσ : -b.re < σ) (n : ℕ) :
    (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          Ring.multichoose (-((σ : ℂ) + y * I)) n =
      ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b) / (n ! * Gamma (c + n)) := by
  have ha : 0 < a.re := by linarith
  have hb : 0 < b.re := by linarith
  have hcb : 0 < (c - b).re := by simp only [sub_re] at hcab ⊢; linarith
  have hca : 0 < (c - a).re := by simp only [sub_re] at hcab ⊢; linarith
  let s : ℝ → ℂ := fun y ↦ (σ : ℂ) + y * I
  have hint_eq : (∫ y : ℝ, Gamma (a + s y) * Gamma (b + s y) * Gamma (c - a - b - s y) *
        Gamma (-s y) * Ring.multichoose (-s y) n) =
      (n ! : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + s y) * Gamma (b + s y) *
        Gamma (c - a - b - s y) * Gamma ((n : ℂ) - s y) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    have hmc := Gamma_mul_multichoose (s := -s y) (n := n)
      fun k _ ↦ ne_neg_natCast_of_re_pos (by simp [s]; linarith) k
    rw [show -s y + n = (n : ℂ) - s y by ring] at hmc
    dsimp only
    rw [mul_assoc (Gamma (a + s y) * Gamma (b + s y) * Gamma (c - a - b - s y)), hmc]
    ring
  have hbarnes := integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub
    (a := a) (b := b) (c := c - a - b) (d := (n : ℂ)) (σ := σ)
    haσ hbσ hcab (by simp; linarith [n.cast_nonneg (α := ℝ)])
  have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hbarnes' : (∫ y : ℝ, Gamma (a + s y) * Gamma (b + s y) *
        Gamma (c - a - b - s y) * Gamma ((n : ℂ) - s y)) =
      (2 * π : ℂ) * (Gamma (c - b) * Gamma (a + n) * Gamma (c - a) *
        Gamma (b + n) / Gamma (c + n)) := by
    rw [show a + (c - a - b) = c - b by ring, show b + (c - a - b) = c - a by ring,
      show a + b + (c - a - b) + (n : ℂ) = c + n by ring] at hbarnes
    dsimp [s]; rw [← hbarnes, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hΓca : Gamma (c - a) ≠ 0 := Gamma_ne_zero_of_re_pos hca
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  dsimp only [s] at hint_eq hbarnes'
  rw [hint_eq, hbarnes',
    ← Gamma_add_nat_div_Gamma_eq (n := n) a (ne_neg_natCast_of_re_pos ha),
    ← Gamma_add_nat_div_Gamma_eq (n := n) b (ne_neg_natCast_of_re_pos hb)]
  field_simp [hpi, hΓa, hΓb, hΓca, hΓcb]

/-- Integrability of the dominated-convergence envelope `y ↦ ‖g y‖ * 2 ^ ‖σ + i y‖` for the
four-Gamma kernel `g` of DLMF 15.6.7. -/
private theorem integrable_mellinBarnesOneSub_mul_two_rpow_norm {a b c : ℂ} {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hcab : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Integrable (fun y : ℝ ↦
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ *
        (2 : ℝ) ^ ‖(σ : ℂ) + y * I‖) volume := by
  obtain ⟨hg_cont, C, _, hg_bound⟩ :=
    continuous_and_norm_mellinBarnesOneSubKernel_le haσ hbσ hcab hσ
  set α : ℝ := 2 * π - Real.log 2
  have hα : 0 < α := by dsimp [α]; linarith [Real.log_two_lt_d9, Real.two_le_pi]
  have hcont : Continuous fun y : ℝ ↦
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ *
        (2 : ℝ) ^ ‖(σ : ℂ) + y * I‖ :=
    hg_cont.norm.mul (continuous_const.rpow (by fun_prop) fun _ ↦ Or.inl two_ne_zero)
  refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (c.re - 2) hα).const_mul
    (C * 2 ^ |σ|)).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  have h2pow : (2 : ℝ) ^ ‖(σ : ℂ) + y * I‖ ≤ 2 ^ |σ| * Real.exp (Real.log 2 * |y|) := by
    calc (2 : ℝ) ^ ‖(σ : ℂ) + y * I‖
        ≤ 2 ^ (|σ| + |y|) := Real.rpow_le_rpow_of_exponent_le one_le_two
          ((norm_add_le _ _).trans_eq (by simp))
      _ = 2 ^ |σ| * Real.exp (Real.log 2 * |y|) := by
          rw [Real.rpow_add two_pos]; congr 1; exact Real.rpow_def_of_pos two_pos _
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ * (2 : ℝ) ^ ‖(σ : ℂ) + y * I‖
      ≤ (C * (1 + |y|) ^ (c.re - 2) * Real.exp (-(2 * π) * |y|)) *
          (2 ^ |σ| * Real.exp (Real.log 2 * |y|)) :=
        mul_le_mul (hg_bound y) h2pow (by positivity) (by positivity)
    _ = C * 2 ^ |σ| * (1 + |y|) ^ (c.re - 2) *
          (Real.exp (-(2 * π) * |y|) * Real.exp (Real.log 2 * |y|)) := by ring
    _ = _ := by rw [← Real.exp_add]; dsimp [α]; ring_nf

/-- Evaluation of the DLMF 15.6.7 Mellin–Barnes integral on the smaller disk `‖w‖ < 1 / 2` by
expanding `(1 - w) ^ s` in its multichoose binomial series and integrating termwise via
`Complex.integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_multichoose`. -/
private theorem regularizedGaussHGFun_eq_mellinBarnes_one_sub_of_norm_lt_half
    {a b c w : ℂ} {σ : ℝ} (hw : ‖w‖ < 1 / 2) (hσ : σ < 0) (hcab : σ < (c - a - b).re)
    (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    regularizedGaussHGFun a b c w =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - w) ^ (σ + y * I) := by
  have haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hbσ_ne : ∀ n : ℕ, b.re + σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hcab_ne : ∀ n : ℕ, (c - a - b).re - σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hσ_ne : ∀ n : ℕ, -σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  let s : ℝ → ℂ := fun y ↦ (σ : ℂ) + y * I
  let g : ℝ → ℂ := fun y ↦
    Gamma (a + s y) * Gamma (b + s y) * Gamma (c - a - b - s y) * Gamma (-s y)
  let M : ℂ := (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹
  let bound : ℕ → ℝ → ℝ := fun n y ↦ ‖g y‖ * (Ring.multichoose ‖s y‖ n * (1 / 2 : ℝ) ^ n)
  have hg_cont : Continuous g :=
    (continuous_and_norm_mellinBarnesOneSubKernel_le haσ_ne hbσ_ne hcab_ne hσ_ne).1
  have hF_meas (n : ℕ) :
      AEStronglyMeasurable (fun y : ℝ ↦ g y * (Ring.multichoose (-s y) n * w ^ n)) volume :=
    (hg_cont.mul (((TauCeti.continuous_multichoose n).comp (by fun_prop)).mul
      continuous_const)).aestronglyMeasurable
  have h_bound (n : ℕ) : ∀ᵐ y : ℝ ∂volume,
      ‖g y * (Ring.multichoose (-s y) n * w ^ n)‖ ≤ bound n y :=
    Eventually.of_forall fun y ↦ by
      dsimp only [bound]
      rw [norm_mul (g y), norm_mul (Ring.multichoose (-s y) n), norm_pow]
      have hmc : ‖Ring.multichoose (-s y) n‖ ≤ Ring.multichoose ‖s y‖ n := by
        simpa only [norm_neg] using TauCeti.norm_multichoose_le (-s y) n
      exact mul_le_mul_of_nonneg_left (mul_le_mul hmc (pow_le_pow_left₀ (norm_nonneg w) hw.le n)
        (pow_nonneg (norm_nonneg w) n) ((norm_nonneg _).trans hmc)) (norm_nonneg _)
  have h_mc_sum (y : ℝ) : HasSum (fun n : ℕ ↦ Ring.multichoose ‖s y‖ n * (1 / 2 : ℝ) ^ n)
      (1 / (1 - (1 / 2 : ℝ)) ^ ‖s y‖) :=
    TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (by norm_num)
  have bound_integrable : Integrable (fun y : ℝ ↦ ∑' n : ℕ, bound n y) volume := by
    refine (integrable_mellinBarnesOneSub_mul_two_rpow_norm haσ_ne hbσ_ne hcab_ne hσ_ne).congr
      (Eventually.of_forall fun y ↦ ?_)
    dsimp only [bound, g, s]
    rw [tsum_mul_left, (h_mc_sum y).tsum_eq, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
      one_div, ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2),
      show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
  have h_lim : ∀ᵐ y : ℝ ∂volume,
      HasSum (fun n : ℕ ↦ g y * (Ring.multichoose (-s y) n * w ^ n)) (g y * (1 - w) ^ s y) :=
    Eventually.of_forall fun y ↦ by
      have hbin := TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one
        (r := -s y) (hw.trans (by norm_num))
      rw [one_div, cpow_neg, inv_inv] at hbin
      exact hbin.mul_left (g y)
  have hswap := (hasSum_integral_of_dominated_convergence bound hF_meas h_bound
    (Eventually.of_forall fun y ↦ (h_mc_sum y).summable.mul_left ‖g y‖) bound_integrable
    h_lim).mul_left M
  have hRHS_sum : HasSum (fun n : ℕ ↦
      ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b) /
        (n ! * Gamma (c + n)) * w ^ n) (M * ∫ y : ℝ, g y * (1 - w) ^ s y) := by
    convert hswap using 1
    ext n
    rw [← integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_multichoose hσ hcab haσ hbσ n]
    dsimp only [M, g, s]
    rw [mul_assoc, ← integral_mul_const]
    congr 2; ext y; ring
  exact (hasSum_regularizedGaussHGFun a b c (hw.trans (by norm_num))).unique hRHS_sum

/-- **Mellin–Barnes integral for `Complex.regularizedGaussHGFun` in `1 - z` (DLMF 15.6.7).**
On the open unit disk `‖z‖ < 1`, for any vertical line `s = σ + i y` with
`-min(Re a, Re b) < σ < min(0, Re(c - a - b))`,
`Complex.regularizedGaussHGFun a b c z = (2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫_ℝ Γ(a + s) Γ(b + s)
  Γ(c - a - b - s) Γ(-s) (1 - z)^s dy`. -/
theorem regularizedGaussHGFun_eq_mellinBarnes_one_sub {a b c z : ℂ} {σ : ℝ}
    (hz : ‖z‖ < 1) (hσ : σ < 0) (hcab : σ < (c - a - b).re)
    (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    regularizedGaussHGFun a b c z =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - z) ^ (σ + y * I) := by
  have haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hbσ_ne : ∀ n : ℕ, b.re + σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hcab_ne : ∀ n : ℕ, (c - a - b).re - σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hσ_ne : ∀ n : ℕ, -σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hball_slit : Metric.ball (0 : ℂ) 1 ⊆ {w : ℂ | 1 - w ∈ slitPlane} := fun w hw ↦ by
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact mem_slitPlane_iff.2 (Or.inl (by simp only [sub_re, one_re]; linarith [re_le_norm w]))
  -- Extend from `‖w‖ < 1 / 2` to the open unit disk `‖w‖ < 1` by analytic continuation.
  have hanL : AnalyticOnNhd ℂ (regularizedGaussHGFun a b c) (Metric.ball 0 1) := fun w hw ↦
    analyticAt_regularizedHGFun_of_card_eq_add_one rfl (by simpa using hw)
  have hanR : AnalyticOnNhd ℂ (fun w : ℂ ↦
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - w) ^ (σ + y * I))
      (Metric.ball 0 1) :=
    analyticOnNhd_const.mul
      ((analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow
        haσ_ne hbσ_ne hcab_ne hσ_ne).mono hball_slit)
  exact (hanL.eqOn_of_preconnected_of_eventuallyEq hanR (convex_ball (0 : ℂ) 1).isPreconnected
    (Metric.mem_ball_self one_pos)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 2))
      fun w hw ↦ regularizedGaussHGFun_eq_mellinBarnes_one_sub_of_norm_lt_half
        (by simpa [Metric.mem_ball] using hw) hσ hcab haσ hbσ))
      (by simpa using hz)

/-- **Mellin–Barnes integral for `₂F₁` in `1 - z` on the open unit disk (DLMF 15.6.7).** -/
theorem ordinaryHypergeometric_eq_mellinBarnes_one_sub {a b c z : ℂ} {σ : ℝ}
    (hz : ‖z‖ < 1) (hσ : σ < 0) (hcab : σ < (c - a - b).re)
    (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    ordinaryHypergeometric a b c z =
      Gamma c * (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - z) ^ (σ + y * I) := by
  have hc : ∀ k : ℕ, c ≠ -k := ne_neg_natCast_of_re_pos (by simp only [sub_re] at hcab; linarith)
  have hreg := regularizedGaussHGFun_eq_mellinBarnes_one_sub
    (a := a) (b := b) (c := c) hz hσ hcab haσ hbσ
  rw [← ordinaryHypergeometric_div_Gamma_eq hc, div_eq_iff (Gamma_ne_zero hc)] at hreg
  linear_combination hreg

end Complex

end
