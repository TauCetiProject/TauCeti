/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.MellinInversion
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Mellin–Barnes integrals for the Gauss hypergeometric function

The regularized Gauss hypergeometric function admits two classical vertical Mellin–Barnes integral
representations ([DLMF 15.6.6](https://dlmf.nist.gov/15.6.E6) and
[DLMF 15.6.7](https://dlmf.nist.gov/15.6.E7)). Along a vertical line `s = σ + i y` avoiding the
poles of the numerator Gamma factors:

1. The three-Gamma-over-one-Gamma integral
   `(2π Γ(a) Γ(b))⁻¹ ∫ Γ(a + s) Γ(b + s) Γ(-s) Γ(c + s)⁻¹ (-z)^s dy`
   has a Gamma kernel decaying like `(1 + |y|)^P exp (-π |y|)`. It therefore converges and is
   holomorphic in `z` on the cut plane `-z ∈ Complex.slitPlane`, and is entire in the lower
   parameter `c` at every such `z`. When `-min(Re a, Re b) < σ < 0` and `0 < Re b < Re c`, it
   agrees with Euler's normalized integral `Complex.eulerIntegral a b c z` throughout
   `-z ∈ Complex.slitPlane`.

2. The four-Gamma integral
   `(2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫ Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s) (1 - z)^s dy`
   has a Gamma kernel decaying like `(1 + |y|)^P exp (-2π |y|)`. It converges and is holomorphic in
   `z` throughout `1 - z ∈ Complex.slitPlane`. When `max(-Re a, -Re b) < σ < min(0, Re(c - a - b))`
   separates the upward and downward pole families, it equals
   `Complex.regularizedGaussHGFun a b c z` on the unit disk `‖z‖ < 1`.

## Main results

* `Complex.integrable_mellinBarnesIntegrand`, `Complex.differentiableOn_integral_mellinBarnes`,
  `Complex.analyticOnNhd_integral_mellinBarnes`, and
  `Complex.differentiable_integral_mellinBarnes_right`: convergence, cut-plane holomorphy in `z`,
  and entirety in `c` of the DLMF 15.6.6 integral on any pole-free vertical line.
* `Complex.eulerIntegral_eq_mellinBarnes`: equality of `Complex.eulerIntegral a b c z` with the
  DLMF 15.6.6 Mellin–Barnes integral for `0 < Re b < Re c`, `-z ∈ Complex.slitPlane`, and
  `-min(Re a, Re b) < σ < 0`.
* `Complex.integrable_mellinBarnesOneSubIntegrand`,
  `Complex.differentiableOn_integral_mellinBarnes_one_sub`, and
  `Complex.analyticOnNhd_integral_mellinBarnes_one_sub`: convergence and cut-plane holomorphy in `z`
  of the DLMF 15.6.7 integral on any pole-free vertical line.
* `Complex.regularizedGaussHGFun_eq_mellinBarnes_one_sub`: equality of
  `Complex.regularizedGaussHGFun a b c z` with the DLMF 15.6.7 Mellin–Barnes integral on `‖z‖ < 1`
  for `max(-Re a, -Re b) < σ < min(0, Re(c - a - b))`.

## References

* NIST Digital Library of Mathematical Functions, §15.6, equations 15.6.6 and 15.6.7.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §§14.5 and 14.51–14.52.
-/

public section

noncomputable section

open Real Filter MeasureTheory Set
open scoped Nat Topology ENNReal
open Complex hiding exp continuous_exp log

namespace Complex

/-! ### Kernel estimates and the DLMF 15.6.6 Mellin–Barnes integral -/

/-- Continuity of `y ↦ Γ(a + (σ + i y))` along a pole-free vertical line. -/
private lemma continuous_Gamma_add_vertical (a : ℂ) {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n) :
    Continuous fun y : ℝ ↦ Gamma (a + (σ + y * I)) := by
  refine continuous_iff_continuousAt.mpr fun y ↦ ?_
  refine ((differentiableAt_Gamma _ fun m hm ↦ haσ m ?_).continuousAt).comp (by fun_prop)
  simpa using congrArg re hm

/-- Continuity of `y ↦ Γ(a - (σ + i y))` along a pole-free vertical line. -/
private lemma continuous_Gamma_sub_vertical (a : ℂ) {σ : ℝ} (haσ : ∀ n : ℕ, a.re - σ ≠ -n) :
    Continuous fun y : ℝ ↦ Gamma (a - (σ + y * I)) := by
  refine continuous_iff_continuousAt.mpr fun y ↦ ?_
  refine ((differentiableAt_Gamma _ fun m hm ↦ haσ m ?_).continuousAt).comp (by fun_prop)
  simpa using congrArg re hm

/-- Sub-`π` exponential decay for the three-Gamma numerator `Γ(a + s) Γ(b + s) Γ(-s)` multiplied by
any polynomial-times-half-exponential growth `(1 + |y|)^{P_c} exp (π |y| / 2)`. -/
private lemma exists_norm_three_Gamma_mul_rpow_exp_le (a b : ℂ) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (Pc : ℝ) {θ' : ℝ} (hθ' : θ' < π) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
        ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2)) ≤ C * Real.exp (-θ' * |y|) := by
  obtain ⟨Ca, hCa⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le (z := a + σ) (by simpa using haσ)
  obtain ⟨Cb, hCb⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le (z := b + σ) (by simpa using hbσ)
  obtain ⟨Cs, hCs⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le (z := -(σ : ℂ))
    fun n hn ↦ hσ n (by simp at hn; linarith)
  set Ca₁ : ℝ := max Ca 0
  set Cb₁ : ℝ := max Cb 0
  set Cs₁ : ℝ := max Cs 0
  set P : ℝ := (a.re + σ - 1 / 2) + (b.re + σ - 1 / 2) + (-σ - 1 / 2) + Pc
  set δ : ℝ := π - θ'
  have hδ : 0 < δ := sub_pos.2 hθ'
  set q : ℝ := |P| + 1
  have hq : 0 < q := by positivity
  set K : ℝ := δ - q - q * Real.log (δ / q)
  refine ⟨Ca₁ * Cb₁ * Cs₁ * Real.exp K, by positivity, fun y ↦ ?_⟩
  have h1y : 0 < 1 + |y| := by positivity
  have ha_le : ‖Gamma (a + (σ + y * I))‖ ≤
      Ca₁ * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    have heq : a + ((σ : ℂ) + y * I) = a + σ + y * I := by ring
    rw [heq]
    refine (hCa y).trans ?_
    simp only [add_re, ofReal_re]
    gcongr
    exact le_max_left Ca 0
  have hb_le : ‖Gamma (b + (σ + y * I))‖ ≤
      Cb₁ * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    have heq : b + ((σ : ℂ) + y * I) = b + σ + y * I := by ring
    rw [heq]
    refine (hCb y).trans ?_
    simp only [add_re, ofReal_re]
    gcongr
    exact le_max_left Cb 0
  have hs_le : ‖Gamma (-((σ : ℂ) + y * I))‖ ≤
      Cs₁ * (1 + |y|) ^ (-σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    have heq : -((σ : ℂ) + y * I) = -(σ : ℂ) - y * I := by ring
    rw [heq]
    refine (hCs y).trans ?_
    simp only [neg_re, ofReal_re]
    gcongr
    exact le_max_left Cs 0
  rw [norm_mul, norm_mul]
  have hprod : ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ *
        ‖Gamma (-((σ : ℂ) + y * I))‖ * ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2)) ≤
      (Ca₁ * Cb₁ * Cs₁) * ((1 + |y|) ^ P * Real.exp (-π * |y|)) := by
    calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ *
            ‖Gamma (-((σ : ℂ) + y * I))‖ * ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2))
        ≤ (Ca₁ * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
            (Cb₁ * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
            (Cs₁ * (1 + |y|) ^ (-σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
            ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2)) :=
          mul_le_mul (mul_le_mul (mul_le_mul ha_le hb_le (norm_nonneg _) (by positivity))
            hs_le (norm_nonneg _) (by positivity)) le_rfl (by positivity) (by positivity)
      _ = (Ca₁ * Cb₁ * Cs₁) *
            (((1 + |y|) ^ (a.re + σ - 1 / 2) * (1 + |y|) ^ (b.re + σ - 1 / 2) *
              (1 + |y|) ^ (-σ - 1 / 2) * (1 + |y|) ^ Pc) *
             (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2) *
              Real.exp (-π * |y| / 2) * Real.exp (π * |y| / 2))) := by ring
      _ = (Ca₁ * Cb₁ * Cs₁) * ((1 + |y|) ^ P * Real.exp (-π * |y|)) := by
          rw [← Real.rpow_add h1y, ← Real.rpow_add h1y, ← Real.rpow_add h1y,
            ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          dsimp only [P]
          congr 3
          ring
  -- Absorb the polynomial factor `(1 + |y|) ^ P` into the exponential gap `δ = π - θ' > 0`.
  have habs : (1 + |y|) ^ P * Real.exp (-π * |y|) ≤ Real.exp K * Real.exp (-θ' * |y|) := by
    have hPq : P * Real.log (1 + |y|) ≤ q * Real.log (1 + |y|) :=
      mul_le_mul_of_nonneg_right ((le_abs_self P).trans (by dsimp [q]; linarith))
        (Real.log_nonneg (by linarith [abs_nonneg y]))
    have hlog_lin : Real.log (δ / q) + Real.log (1 + |y|) ≤ δ / q * (1 + |y|) - 1 := by
      rw [← Real.log_mul (div_pos hδ hq).ne' h1y.ne']
      exact Real.log_le_sub_one_of_pos (mul_pos (div_pos hδ hq) h1y)
    have hq_lin : q * Real.log (1 + |y|) ≤ K + δ * |y| := by
      have hmul := mul_le_mul_of_nonneg_left hlog_lin hq.le
      have hsimp : q * (δ / q * (1 + |y|) - 1) = δ + δ * |y| - q := by field_simp [hq.ne']
      dsimp only [K]
      linarith
    rw [Real.rpow_def_of_pos h1y, mul_comm (Real.log _), ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    dsimp only [δ] at hq_lin
    linarith
  refine hprod.trans ?_
  calc (Ca₁ * Cb₁ * Cs₁) * ((1 + |y|) ^ P * Real.exp (-π * |y|))
      ≤ (Ca₁ * Cb₁ * Cs₁) * (Real.exp K * Real.exp (-θ' * |y|)) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ = _ := by ring

/-- Uniform vertical growth bound for `(Γ(c + (σ + i y)))⁻¹` over `c ∈ Metric.ball c₀ 1`. -/
private lemma exists_norm_inv_Gamma_ball_vertical_le (c₀ : ℂ) (σ : ℝ) :
    ∃ Kc Pc : ℝ, 0 ≤ Kc ∧ ∀ c ∈ Metric.ball c₀ 1, ∀ y : ℝ,
      ‖(Gamma (c + (σ + y * I)))⁻¹‖ ≤ Kc * ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2)) := by
  obtain ⟨Cc, hCc⟩ := TauCeti.exists_norm_inv_Gamma_vertical_strip_le
    (c₀.re - 1 + σ) (c₀.re + 1 + σ)
  set Cc₁ : ℝ := max Cc 0
  set Pc : ℝ := |3 / 2 - c₀.re - σ|
  refine ⟨Cc₁ * (2 + |c₀.im|) ^ Pc * Real.exp (π * (|c₀.im| + 1) / 2), Pc, by positivity,
    fun c hc y ↦ ?_⟩
  have hc_dist : ‖c - c₀‖ < 1 := mem_ball_iff_norm.1 hc
  have hc_re : |c.re - c₀.re| ≤ 1 := (abs_re_le_norm (c - c₀)).trans hc_dist.le
  have hc_im : |c.im - c₀.im| ≤ 1 := (abs_im_le_norm (c - c₀)).trans hc_dist.le
  have hcs_re : (c + (σ + y * I)).re ∈ Icc (c₀.re - 1 + σ) (c₀.re + 1 + σ) := by
    obtain ⟨h1, h2⟩ := abs_le.1 hc_re
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, mem_Icc]
    exact ⟨by linarith, by linarith⟩
  have hcs_im : |(c + (σ + y * I)).im| ≤ |c₀.im| + 1 + |y| := by
    have := abs_sub_abs_le_abs_sub c.im c₀.im
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add]
    linarith [abs_add_le c.im y]
  have hexp_re : 1 / 2 - (c + (σ + y * I)).re ≤ Pc := by
    refine (le_of_le_of_eq ?_ rfl).trans (le_abs_self _)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    linarith [(abs_le.1 hc_re).1]
  have hrpow : (1 + |(c + (σ + y * I)).im|) ^ (1 / 2 - (c + (σ + y * I)).re) ≤
      (2 + |c₀.im|) ^ Pc * (1 + |y|) ^ Pc := by
    refine (Real.rpow_le_rpow_of_exponent_le
      (by linarith [abs_nonneg (c + (σ + y * I)).im]) hexp_re).trans ?_
    calc (1 + |(c + (σ + y * I)).im|) ^ Pc
        ≤ ((2 + |c₀.im|) * (1 + |y|)) ^ Pc :=
          Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg c₀.im, abs_nonneg y])
            (abs_nonneg _)
      _ = (2 + |c₀.im|) ^ Pc * (1 + |y|) ^ Pc :=
          Real.mul_rpow (by positivity) (by positivity)
  have hexp : Real.exp (π * |(c + (σ + y * I)).im| / 2) ≤
      Real.exp (π * (|c₀.im| + 1) / 2) * Real.exp (π * |y| / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  calc ‖(Gamma (c + (σ + y * I)))⁻¹‖
      ≤ Cc₁ * (1 + |(c + (σ + y * I)).im|) ^ (1 / 2 - (c + (σ + y * I)).re) *
          Real.exp (π * |(c + (σ + y * I)).im| / 2) := by
        refine (hCc _ hcs_re).trans ?_
        gcongr
        exact le_max_left Cc 0
    _ ≤ Cc₁ * ((2 + |c₀.im|) ^ Pc * (1 + |y|) ^ Pc) *
          (Real.exp (π * (|c₀.im| + 1) / 2) * Real.exp (π * |y| / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hrpow (le_max_right Cc 0)) hexp
          (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- Uniform vertical growth bound for `deriv (fun w ↦ (Γ w)⁻¹) (c + (σ + i y))` over
`c ∈ Metric.ball c₀ 1`. -/
private lemma exists_norm_deriv_inv_Gamma_ball_vertical_le (c₀ : ℂ) (σ : ℝ) :
    ∃ Kc Pc : ℝ, 0 ≤ Kc ∧ ∀ c ∈ Metric.ball c₀ 1, ∀ y : ℝ,
      ‖deriv (fun w ↦ (Gamma w)⁻¹) (c + (σ + y * I))‖ ≤
        Kc * ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2)) := by
  obtain ⟨Cc, hCc⟩ := TauCeti.exists_norm_deriv_inv_Gamma_vertical_strip_le
    (c₀.re - 1 + σ) (c₀.re + 1 + σ)
  set Cc₁ : ℝ := max Cc 0
  set Pc : ℝ := |5 / 2 - c₀.re - σ|
  refine ⟨Cc₁ * (2 + |c₀.im|) ^ Pc * Real.exp (π * (|c₀.im| + 1) / 2), Pc, by positivity,
    fun c hc y ↦ ?_⟩
  have hc_dist : ‖c - c₀‖ < 1 := mem_ball_iff_norm.1 hc
  have hc_re : |c.re - c₀.re| ≤ 1 := (abs_re_le_norm (c - c₀)).trans hc_dist.le
  have hc_im : |c.im - c₀.im| ≤ 1 := (abs_im_le_norm (c - c₀)).trans hc_dist.le
  have hcs_re : (c + (σ + y * I)).re ∈ Icc (c₀.re - 1 + σ) (c₀.re + 1 + σ) := by
    obtain ⟨h1, h2⟩ := abs_le.1 hc_re
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, mem_Icc]
    exact ⟨by linarith, by linarith⟩
  have hcs_im : |(c + (σ + y * I)).im| ≤ |c₀.im| + 1 + |y| := by
    have := abs_sub_abs_le_abs_sub c.im c₀.im
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
      zero_add]
    linarith [abs_add_le c.im y]
  have hexp_re : 3 / 2 - (c + (σ + y * I)).re ≤ Pc := by
    refine (le_of_le_of_eq ?_ rfl).trans (le_abs_self _)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    linarith [(abs_le.1 hc_re).1]
  have hrpow : (1 + |(c + (σ + y * I)).im|) ^ (3 / 2 - (c + (σ + y * I)).re) ≤
      (2 + |c₀.im|) ^ Pc * (1 + |y|) ^ Pc := by
    refine (Real.rpow_le_rpow_of_exponent_le
      (by linarith [abs_nonneg (c + (σ + y * I)).im]) hexp_re).trans ?_
    calc (1 + |(c + (σ + y * I)).im|) ^ Pc
        ≤ ((2 + |c₀.im|) * (1 + |y|)) ^ Pc :=
          Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg c₀.im, abs_nonneg y])
            (abs_nonneg _)
      _ = (2 + |c₀.im|) ^ Pc * (1 + |y|) ^ Pc :=
          Real.mul_rpow (by positivity) (by positivity)
  have hexp : Real.exp (π * |(c + (σ + y * I)).im| / 2) ≤
      Real.exp (π * (|c₀.im| + 1) / 2) * Real.exp (π * |y| / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  calc ‖deriv (fun w ↦ (Gamma w)⁻¹) (c + (σ + y * I))‖
      ≤ Cc₁ * (1 + |(c + (σ + y * I)).im|) ^ (3 / 2 - (c + (σ + y * I)).re) *
          Real.exp (π * |(c + (σ + y * I)).im| / 2) := by
        refine (hCc _ hcs_re).trans ?_
        gcongr
        exact le_max_left Cc 0
    _ ≤ Cc₁ * ((2 + |c₀.im|) ^ Pc * (1 + |y|) ^ Pc) *
          (Real.exp (π * (|c₀.im| + 1) / 2) * Real.exp (π * |y| / 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hrpow (le_max_right Cc 0)) hexp
          (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- Uniform sub-`π` exponential decay on `c ∈ Metric.ball c₀ 1` for the Gamma kernel of DLMF 15.6.6
along a pole-free vertical line `Re s = σ`. -/
private lemma exists_norm_mellinBarnesKernel_ball_le (a b c₀ : ℂ) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    {θ' : ℝ} (hθ' : θ' < π) :
    ∃ C : ℝ, ∀ c ∈ Metric.ball c₀ 1, ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
          (Gamma (c + (σ + y * I)))⁻¹‖ ≤ C * Real.exp (-θ' * |y|) := by
  obtain ⟨Kc, Pc, hKc0, hKc⟩ := exists_norm_inv_Gamma_ball_vertical_le c₀ σ
  obtain ⟨C₃, _, hC₃⟩ := exists_norm_three_Gamma_mul_rpow_exp_le a b hσ haσ hbσ Pc hθ'
  refine ⟨Kc * C₃, fun c hc y ↦ ?_⟩
  rw [norm_mul]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          ‖(Gamma (c + (σ + y * I)))⁻¹‖
      ≤ ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          (Kc * ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2))) :=
        mul_le_mul_of_nonneg_left (hKc c hc y) (norm_nonneg _)
    _ = Kc * (‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2))) := by ring
    _ ≤ Kc * (C₃ * Real.exp (-θ' * |y|)) := mul_le_mul_of_nonneg_left (hC₃ y) hKc0
    _ = (Kc * C₃) * Real.exp (-θ' * |y|) := by ring

/-- Uniform sub-`π` exponential decay on `c ∈ Metric.ball c₀ 1` for the `c`-derivative of the
DLMF 15.6.6 Gamma kernel along a pole-free vertical line `Re s = σ`. -/
private lemma exists_norm_mellinBarnesKernel_deriv_ball_le (a b c₀ : ℂ) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    {θ' : ℝ} (hθ' : θ' < π) :
    ∃ C : ℝ, ∀ c ∈ Metric.ball c₀ 1, ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
          deriv (fun w ↦ (Gamma w)⁻¹) (c + (σ + y * I))‖ ≤ C * Real.exp (-θ' * |y|) := by
  obtain ⟨Kc, Pc, hKc0, hKc⟩ := exists_norm_deriv_inv_Gamma_ball_vertical_le c₀ σ
  obtain ⟨C₃, _, hC₃⟩ := exists_norm_three_Gamma_mul_rpow_exp_le a b hσ haσ hbσ Pc hθ'
  refine ⟨Kc * C₃, fun c hc y ↦ ?_⟩
  rw [norm_mul]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          ‖deriv (fun w ↦ (Gamma w)⁻¹) (c + (σ + y * I))‖
      ≤ ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          (Kc * ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2))) :=
        mul_le_mul_of_nonneg_left (hKc c hc y) (norm_nonneg _)
    _ = Kc * (‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2))) := by ring
    _ ≤ Kc * (C₃ * Real.exp (-θ' * |y|)) := mul_le_mul_of_nonneg_left (hC₃ y) hKc0
    _ = (Kc * C₃) * Real.exp (-θ' * |y|) := by ring

/-- Continuity of the DLMF 15.6.6 Gamma kernel along a pole-free vertical line. -/
private lemma continuous_mellinBarnesKernel (a b c : ℂ) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) :
    Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ := by
  have hs : Continuous fun y : ℝ ↦ Gamma (-((σ : ℂ) + y * I)) := by
    simpa using continuous_Gamma_sub_vertical 0 fun n hn ↦ hσ n (by simp at hn; linarith)
  have hinv : Continuous fun w : ℂ ↦ (Gamma w)⁻¹ := by
    simpa only [one_div] using differentiable_one_div_Gamma.continuous
  exact (((continuous_Gamma_add_vertical a haσ).mul
    (continuous_Gamma_add_vertical b hbσ)).mul hs).mul (hinv.comp (by fun_prop))

/-- The integrand of the first hypergeometric Mellin–Barnes integral (DLMF 15.6.6) is integrable on
`ℝ` for `-z ∈ Complex.slitPlane` and any `c : ℂ` whenever the vertical line `Re s = σ` avoids the
poles of `Γ(a + s)`, `Γ(b + s)`, and `Γ(-s)`. -/
theorem integrable_mellinBarnesIntegrand (a b c : ℂ) {z : ℂ} (hz : -z ∈ slitPlane) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  have harg : |(-z).arg| < π := abs_arg_lt_pi_of_mem_slitPlane hz
  set θ' : ℝ := (|(-z).arg| + π) / 2
  obtain ⟨C, hC⟩ := exists_norm_mellinBarnesKernel_ball_le a b c hσ haσ hbσ
    (by dsimp [θ']; linarith : θ' < π)
  have hint := TauCeti.integrable_cpow_vertical_smul
    (continuous_mellinBarnesKernel a b c hσ haσ hbσ).aestronglyMeasurable
    (slitPlane_ne_zero hz) σ (θ := θ') (by dsimp [θ']; linarith)
    (hC c (Metric.mem_ball_self one_pos))
  exact hint.congr (Eventually.of_forall fun _ ↦ by dsimp; rw [mul_comm])

/-- The first hypergeometric Mellin–Barnes integral (DLMF 15.6.6) is complex differentiable in `z`
on `{z | -z ∈ Complex.slitPlane}` along every pole-avoiding vertical line `Re s = σ`. -/
theorem differentiableOn_integral_mellinBarnes (a b c : ℂ) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) :
    DifferentiableOn ℂ
      (fun z : ℂ ↦ ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I))
      {z : ℂ | -z ∈ slitPlane} := by
  have hdiff : DifferentiableOn ℂ
      ((fun w : ℂ ↦ ∫ y : ℝ, w ^ ((σ : ℂ) + y * I) •
        (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹)) ∘ fun z : ℂ ↦ -z)
      {z : ℂ | -z ∈ slitPlane} :=
    (TauCeti.differentiableOn_integral_cpow_vertical_smul
      (continuous_mellinBarnesKernel a b c hσ haσ hbσ).aestronglyMeasurable σ fun θ' hθ' ↦ by
        obtain ⟨C, hC⟩ := exists_norm_mellinBarnesKernel_ball_le a b c hσ haσ hbσ hθ'
        exact ⟨C, hC c (Metric.mem_ball_self one_pos)⟩).comp
      differentiable_neg.differentiableOn fun _ hz ↦ hz
  refine hdiff.congr fun _ _ ↦ integral_congr_ae (Eventually.of_forall fun _ ↦ ?_)
  dsimp
  rw [mul_comm]

/-- The first hypergeometric Mellin–Barnes integral (DLMF 15.6.6) is holomorphic in `z` on
`{z | -z ∈ Complex.slitPlane}` along every pole-avoiding vertical line `Re s = σ`. -/
theorem analyticOnNhd_integral_mellinBarnes (a b c : ℂ) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) :
    AnalyticOnNhd ℂ
      (fun z : ℂ ↦ ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I))
      {z : ℂ | -z ∈ slitPlane} :=
  (differentiableOn_integral_mellinBarnes a b c hσ haσ hbσ).analyticOnNhd
    (isOpen_slitPlane.preimage continuous_neg)

/-- For fixed `a`, `b`, `-z ∈ Complex.slitPlane`, and a pole-avoiding vertical line `Re s = σ`, the
first hypergeometric Mellin–Barnes integral (DLMF 15.6.6) is an entire function of the lower
parameter `c`. -/
theorem differentiable_integral_mellinBarnes_right (a b : ℂ) {z : ℂ} (hz : -z ∈ slitPlane) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) :
    Differentiable ℂ fun c : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  intro c₀
  -- Split the angular slack `π - |arg (-z)| > 0` equally between the kernel and the majorant.
  have hne : -z ≠ 0 := slitPlane_ne_zero hz
  have harg : |(-z).arg| < π := abs_arg_lt_pi_of_mem_slitPlane hz
  set θ' : ℝ := (|(-z).arg| + π) / 2
  set η : ℝ := (π - |(-z).arg|) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨C, hC⟩ := exists_norm_mellinBarnesKernel_deriv_ball_le a b c₀ hσ haσ hbσ
    (by dsimp [θ']; linarith : θ' < π)
  set C₁ : ℝ := max C 0
  have hent : Differentiable ℂ (fun w : ℂ ↦ (Gamma w)⁻¹) := by
    simpa only [one_div] using differentiable_one_div_Gamma
  let F : ℂ → ℝ → ℂ := fun c y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
      (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ ((σ : ℂ) + y * I)
  let F' : ℂ → ℝ → ℂ := fun c y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
      deriv (fun w ↦ (Gamma w)⁻¹) (c + (σ + y * I)) * (-z) ^ ((σ : ℂ) + y * I)
  have hcpow_cont : Continuous fun y : ℝ ↦ (-z) ^ ((σ : ℂ) + y * I) := by
    simp_rw [cpow_def_of_ne_zero hne]
    fun_prop
  have hF_meas : ∀ᶠ c in 𝓝 c₀, AEStronglyMeasurable (F c) volume :=
    Eventually.of_forall fun c ↦
      ((continuous_mellinBarnesKernel a b c hσ haσ hbσ).mul hcpow_cont).aestronglyMeasurable
  have hF_int : Integrable (F c₀) volume :=
    integrable_mellinBarnesIntegrand a b c₀ hz hσ haσ hbσ
  have hF'_meas : AEStronglyMeasurable (F' c₀) volume := by
    have hs : Continuous fun y : ℝ ↦ Gamma (-((σ : ℂ) + y * I)) := by
      simpa using continuous_Gamma_sub_vertical 0 fun n hn ↦ hσ n (by simp at hn; linarith)
    have hd : Continuous fun y : ℝ ↦ deriv (fun w ↦ (Gamma w)⁻¹) (c₀ + (σ + y * I)) :=
      (hent.contDiff.continuous_deriv le_rfl).comp (by fun_prop)
    exact (((((continuous_Gamma_add_vertical a haσ).mul
      (continuous_Gamma_add_vertical b hbσ)).mul hs).mul hd).mul hcpow_cont).aestronglyMeasurable
  -- Uniformly dominate `‖F' c y‖` on `c ∈ Metric.ball c₀ 1` and differentiate under the integral.
  have h_bound : ∀ᵐ y : ℝ ∂volume, ∀ c ∈ Metric.ball c₀ 1,
      ‖F' c y‖ ≤ (C₁ * ‖-z‖ ^ σ) * Real.exp (-(η * |y|)) := by
    refine Eventually.of_forall fun y c hc ↦ ?_
    dsimp only [F']
    rw [norm_mul, norm_cpow_of_ne_zero hne, div_eq_mul_inv, ← Real.exp_neg]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    have hker : ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        deriv (fun w ↦ (Gamma w)⁻¹) (c + (σ + y * I))‖ ≤ C₁ * Real.exp (-θ' * |y|) :=
      (hC c hc y).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le)
    have hpow : Real.exp (-((-z).arg * y)) ≤ Real.exp (|(-z).arg| * |y|) :=
      Real.exp_le_exp.2 ((le_abs_self _).trans_eq (by rw [abs_neg, abs_mul]))
    calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
            deriv (fun w ↦ (Gamma w)⁻¹) (c + (σ + y * I))‖ *
          (‖-z‖ ^ σ * Real.exp (-((-z).arg * y)))
        ≤ (C₁ * Real.exp (-θ' * |y|)) * (‖-z‖ ^ σ * Real.exp (|(-z).arg| * |y|)) :=
          mul_le_mul hker (mul_le_mul_of_nonneg_left hpow (by positivity))
            (by positivity) (by positivity)
      _ = (C₁ * ‖-z‖ ^ σ) * (Real.exp (-θ' * |y|) * Real.exp (|(-z).arg| * |y|)) := by ring
      _ = (C₁ * ‖-z‖ ^ σ) * Real.exp (-(η * |y|)) := by
          rw [← Real.exp_add]
          congr 2
          dsimp [θ', η]
          ring
  have h_diff : ∀ᵐ y : ℝ ∂volume, ∀ c ∈ Metric.ball c₀ 1, HasDerivAt (F · y) (F' c y) c := by
    refine Eventually.of_forall fun y c _ ↦ ?_
    have hd : HasDerivAt (fun c ↦ (Gamma (c + (σ + y * I)))⁻¹)
        (deriv (fun w ↦ (Gamma w)⁻¹) (c + (σ + y * I))) c := by
      simpa only [Function.comp_def, mul_one] using
        (hent (c + (σ + y * I))).hasDerivAt.comp c ((hasDerivAt_id' c).add_const _)
    exact (hd.const_mul (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (-(σ + y * I)))).mul_const ((-z) ^ ((σ : ℂ) + y * I))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds c₀ one_pos)
    hF_meas hF_int hF'_meas h_bound
    ((TauCeti.integrable_exp_neg_mul_abs hη).const_mul (C₁ * ‖-z‖ ^ σ)) h_diff).2.differentiableAt

/-- Joint integrability on `Ioo 0 1 × ℝ` for the Fubini step connecting Euler's integral at `-x`
(`x > 0`) with the DLMF 15.6.6 Mellin–Barnes integral. -/
private lemma integrable_eulerMellinFubini (a b : ℂ) {c : ℂ} (hcb : 0 < (c - b).re)
    {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    Integrable
      (Function.uncurry fun (t : ℝ) (y : ℝ) ↦
        ((t : ℂ) ^ (b + ((σ : ℂ) + y * I) - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
          ((x : ℂ) ^ ((σ : ℂ) + y * I) *
            (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I)))))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  let F : ℝ → ℝ → ℂ := fun t y ↦
    ((t : ℂ) ^ (b + ((σ : ℂ) + y * I) - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
      ((x : ℂ) ^ ((σ : ℂ) + y * I) * (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I))))
  have hf_int : Integrable (fun t : ℝ ↦ (t : ℂ) ^ (b + σ - 1) * (1 - (t : ℂ)) ^ (c - b - 1))
      (volume.restrict (Ioo 0 1)) := by
    have h := betaIntegral_convergent (u := b + σ) (v := c - b) (by simp; linarith) hcb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
    exact h.mono_set Ioo_subset_Ioc_self
  have hg_int : Integrable fun y : ℝ ↦
      (x : ℂ) ^ ((σ : ℂ) + y * I) *
        (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I))) := by
    have hgam : Integrable fun y : ℝ ↦
        Gamma ((a + σ) + y * I) * Gamma ((-(σ : ℂ)) - y * I) :=
      integrable_Gamma_add_mul_Gamma_sub
        (fun n hn ↦ by simp at hn; linarith [n.cast_nonneg' (α := ℝ)])
        (fun n hn ↦ by simp at hn; linarith [n.cast_nonneg' (α := ℝ)])
    have hcont : Continuous fun y : ℝ ↦ (x : ℂ) ^ ((σ : ℂ) + y * I) := by
      simp_rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne')]
      fun_prop
    refine (hgam.bdd_mul (c := x ^ σ) hcont.aestronglyMeasurable
      (Eventually.of_forall fun y ↦ ?_)).congr (Eventually.of_forall fun y ↦ ?_)
    · rw [norm_cpow_eq_rpow_re_of_pos hx]
      simp
    · dsimp
      have h1 : a + (σ : ℂ) + y * I = a + ((σ : ℂ) + y * I) := by ring
      have h2 : -(σ : ℂ) - y * I = -((σ : ℂ) + y * I) := by ring
      rw [h1, h2]
      ring
  have hF_meas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod]
    refine (continuousOn_of_forall_continuousAt fun p hp ↦ ?_).aestronglyMeasurable
      (measurableSet_Ioo.prod MeasurableSet.univ)
    obtain ⟨⟨ht0, ht1⟩, -⟩ := hp
    have ht_slit : (p.1 : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht0
    have h1t_slit : 1 - (p.1 : ℂ) ∈ slitPlane := by
      rw [← ofReal_one, ← ofReal_sub]
      exact ofReal_mem_slitPlane.mpr (by linarith)
    have hs_cont : Continuous fun y : ℝ ↦ Gamma (-((σ : ℂ) + y * I)) := by
      simpa using continuous_Gamma_sub_vertical 0
        fun n hn ↦ by simp at hn; linarith [n.cast_nonneg' (α := ℝ)]
    have ha_cont := continuous_Gamma_add_vertical a (σ := σ)
      fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
    have hc1 : ContinuousAt (fun q : ℝ × ℝ ↦ (q.1 : ℂ) ^ (b + ((σ : ℂ) + q.2 * I) - 1)) p :=
      ContinuousAt.cpow (by fun_prop) (by fun_prop) ht_slit
    have hc2 : ContinuousAt (fun q : ℝ × ℝ ↦ (1 - (q.1 : ℂ)) ^ (c - b - 1)) p :=
      ContinuousAt.cpow (by fun_prop) (by fun_prop) h1t_slit
    have hc3 : ContinuousAt (fun q : ℝ × ℝ ↦ (x : ℂ) ^ ((σ : ℂ) + q.2 * I)) p :=
      ContinuousAt.cpow (by fun_prop) (by fun_prop) (ofReal_mem_slitPlane.mpr hx)
    have hc4 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (-((σ : ℂ) + q.2 * I))) p :=
      (hs_cont.comp continuous_snd).continuousAt
    have hc5 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (a + ((σ : ℂ) + q.2 * I))) p :=
      (ha_cont.comp continuous_snd).continuousAt
    exact (hc1.mul hc2).mul (hc3.mul (hc4.mul hc5))
  refine (hf_int.norm.mul_prod hg_int.norm).mono' hF_meas ?_
  rw [Measure.restrict_prod_eq_prod_univ]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with p hp
  obtain ⟨⟨ht0, _⟩, -⟩ := hp
  have ht0' : (0 : ℝ) < p.1 := ht0
  simp only [Function.uncurry, norm_mul, norm_cpow_eq_rpow_re_of_pos ht0']
  have hre : (b + ((σ : ℂ) + (p.2 : ℂ) * I) - 1).re = (b + (σ : ℂ) - 1).re := by simp
  rw [hre]

/-- Equality of `eulerIntegral a b c (-x)` (`x > 0`) with the DLMF 15.6.6 Mellin–Barnes integral
along `-min(Re a, Re b) < σ < 0`. -/
private lemma eulerIntegral_neg_ofReal_eq_mellinBarnes (a : ℂ) {b c : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ)
    (hbσ : -b.re < σ) :
    eulerIntegral a b c (-(x : ℂ)) = (2 * π * Gamma a * Gamma b)⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ ((σ : ℂ) + y * I) := by
  have ha : 0 < a.re := by linarith
  have hcb : 0 < (c - b).re := by simpa using sub_pos.2 hbc
  let F : ℝ → ℝ → ℂ := fun t y ↦
    ((t : ℂ) ^ (b + ((σ : ℂ) + y * I) - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
      ((x : ℂ) ^ ((σ : ℂ) + y * I) * (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I))))
  have hswap := integral_integral_swap (integrable_eulerMellinFubini a b hcb hx hσ haσ hbσ)
  -- Integrating in `y` first gives `(1 + x t)^{-a}` by Mellin inversion, hence `eulerIntegral`.
  have hlhs : (∫ t in Ioo (0 : ℝ) 1, ∫ y : ℝ, F t y) =
      (2 * π * Gamma a * Gamma b * Gamma (c - b)) * eulerIntegral a b c (-(x : ℂ)) := by
    have hinner : ∀ t ∈ Ioo (0 : ℝ) 1, ∫ y : ℝ, F t y =
        (2 * π * Gamma a) *
          ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
            (1 - (-(x : ℂ)) * (t : ℂ)) ^ (-a)) := by
      intro t ⟨ht0, _⟩
      have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
      have hxt : 0 < x * t := mul_pos hx ht0
      let g : ℝ → ℂ := fun w ↦
        ((x * t : ℝ) : ℂ) ^ (-((-σ : ℝ) + w * I)) *
          (Gamma ((-σ : ℝ) + w * I) * Gamma (a - ((-σ : ℝ) + w * I)))
      have hF_eq : (fun y : ℝ ↦ F t y) = fun y : ℝ ↦
          ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) * g (-y) := by
        ext y
        simp only [F, g]
        have hpow_t : (t : ℂ) ^ (b + ((σ : ℂ) + y * I) - 1) =
            (t : ℂ) ^ (b - 1) * (t : ℂ) ^ ((σ : ℂ) + y * I) := by
          rw [← cpow_add _ _ ht_ne]
          congr 1
          ring
        have hs1 : ((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I = -((σ : ℂ) + y * I) := by
          push_cast
          ring
        have hpow_xt : (x : ℂ) ^ ((σ : ℂ) + y * I) * (t : ℂ) ^ ((σ : ℂ) + y * I) =
            ((x * t : ℝ) : ℂ) ^ ((σ : ℂ) + y * I) := by
          rw [ofReal_mul, mul_cpow_ofReal_nonneg hx.le ht0.le]
        have hs2 : a - -((σ : ℂ) + y * I) = a + ((σ : ℂ) + y * I) := sub_neg_eq_add _ _
        rw [hpow_t, hs1, hs2, neg_neg, ← hpow_xt]
        ring
      rw [hF_eq, integral_const_mul, integral_neg_eq_self g volume]
      dsimp only [g]
      rw [integral_cpow_neg_mul_Gamma_mul_Gamma_sub (by linarith) (by linarith) hxt]
      have h1xt : (1 : ℂ) + ((x * t : ℝ) : ℂ) = 1 - (-(x : ℂ)) * (t : ℂ) := by
        push_cast
        ring
      rw [h1xt]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioo hinner, integral_const_mul,
      setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      eulerIntegral_def]
    have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
    have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
    field_simp [hΓb, hΓcb]
    have hcomm (t : ℝ) : (1 - -((t : ℂ) * (x : ℂ))) = (1 - -((x : ℂ) * (t : ℂ))) := by ring
    simp_rw [hcomm]
  -- Integrating in `t` first evaluates the Beta integral `B(b + s, c - b)`.
  have hrhs : (∫ y : ℝ, ∫ t in Ioo (0 : ℝ) 1, F t y) =
      Gamma (c - b) * ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ ((σ : ℂ) + y * I) := by
    have hinner : ∀ y : ℝ, (∫ t in Ioo (0 : ℝ) 1, F t y) =
        Gamma (c - b) * (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ *
          (x : ℂ) ^ ((σ : ℂ) + y * I)) := by
      intro y
      simp only [F, integral_mul_const]
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
        ← betaIntegral, betaIntegral_eq_Gamma_mul_div (b + ((σ : ℂ) + y * I)) (c - b)
          (by simp; linarith) hcb]
      have hadd : b + ((σ : ℂ) + y * I) + (c - b) = c + ((σ : ℂ) + y * I) := by ring
      rw [hadd, div_eq_mul_inv]
      ring
    simp_rw [hinner, integral_const_mul]
  rw [hlhs, hrhs] at hswap
  have h2pi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hcancel : (2 * π * Gamma a * Gamma b) * eulerIntegral a b c (-(x : ℂ)) =
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ ((σ : ℂ) + y * I) := by
    apply mul_left_cancel₀ hΓcb
    linear_combination hswap
  rw [← hcancel, inv_mul_cancel_left₀ (mul_ne_zero (mul_ne_zero h2pi hΓa) hΓb)]

/-- **Mellin–Barnes representation of Euler's hypergeometric integral**
([DLMF 15.6.6](https://dlmf.nist.gov/15.6.E6)).
For `0 < Re b < Re c`, `-z ∈ Complex.slitPlane`, and `-min(Re a, Re b) < σ < 0`,
`eulerIntegral a b c z = (2π Γ(a) Γ(b))⁻¹ ∫ Γ(a + (σ + i y)) Γ(b + (σ + i y)) Γ(-(σ + i y))
  Γ(c + (σ + i y))⁻¹ (-z)^{σ + i y} dy`. -/
theorem eulerIntegral_eq_mellinBarnes (a : ℂ) {b c z : ℂ} (hb : 0 < b.re) (hbc : b.re < c.re)
    (hz : -z ∈ slitPlane) {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    eulerIntegral a b c z = (2 * π * Gamma a * Gamma b)⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  let U : Set ℂ := {w : ℂ | -w ∈ slitPlane}
  have hU_eq : (fun w : ℂ ↦ -w) '' slitPlane = U := by
    ext w
    simp [U]
  have hU_pre : IsPreconnected U := by
    rw [← hU_eq]
    have hpath := starConvex_one_slitPlane.isPathConnected one_mem_slitPlane
    exact hpath.isConnected.isPreconnected.image _ continuous_neg.continuousOn
  have hlhs_an : AnalyticOnNhd ℂ (eulerIntegral a b c) U := fun w hw ↦ by
    have hw1 : 1 - w ∈ slitPlane := by
      simpa [sub_eq_add_neg] using TauCeti.ofReal_add_mem_slitPlane hw zero_le_one
    exact (analyticOnNhd_eulerIntegral hb hbc (a, w) hw1).curry_right
  have hrhs_an : AnalyticOnNhd ℂ
      (fun w : ℂ ↦ (2 * π * Gamma a * Gamma b)⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
          (Gamma (c + (σ + y * I)))⁻¹ * (-w) ^ (σ + y * I)) U :=
    analyticOnNhd_const.mul (analyticOnNhd_integral_mellinBarnes a b c
      (fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]))
  let zseq : ℕ → ℂ := fun n ↦ -(((1 + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ))
  have hzseq_lim : Tendsto zseq atTop (𝓝[≠] (-1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n h ↦ ?_⟩
    · have hreal : Tendsto (fun n : ℕ ↦ (1 : ℝ) + ((n : ℝ) + 1)⁻¹) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n ↦ one_div _)
      rw [add_zero] at hreal
      simpa only [zseq, ofReal_one, Function.comp_def] using
        ((continuous_ofReal.tendsto 1).comp hreal).neg
    · have hre := congrArg re h
      simp only [zseq, neg_re, ofReal_re, one_re] at hre
      have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith
  have hfreq : ∃ᶠ w in 𝓝[≠] (-1 : ℂ), eulerIntegral a b c w =
      (2 * π * Gamma a * Gamma b)⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
          (Gamma (c + (σ + y * I)))⁻¹ * (-w) ^ (σ + y * I) := by
    refine hzseq_lim.frequently ((Eventually.of_forall fun n : ℕ ↦ ?_).frequently)
    have hx : (0 : ℝ) < 1 + ((n : ℝ) + 1)⁻¹ := by positivity
    simpa only [zseq, neg_neg] using
      eulerIntegral_neg_ofReal_eq_mellinBarnes a hb hbc hx hσ haσ hbσ
  exact hlhs_an.eqOn_of_preconnected_of_frequently_eq hrhs_an hU_pre
    (by simp [U, one_mem_slitPlane]) hfreq hz

/-! ### The DLMF 15.6.7 Mellin–Barnes integral on `{z | 1 - z ∈ slitPlane}` and `‖z‖ < 1` -/

/-- Continuity of the four-Gamma kernel of DLMF 15.6.7 along a pole-free vertical line. -/
private lemma continuous_mellinBarnesOneSubKernel (a b c : ℂ) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (hσc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n)
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) :
    Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) := by
  have hs : Continuous fun y : ℝ ↦ Gamma (-((σ : ℂ) + y * I)) := by
    simpa using continuous_Gamma_sub_vertical 0 fun n hn ↦ hσ n (by simp at hn; linarith)
  exact (((continuous_Gamma_add_vertical a haσ).mul
    (continuous_Gamma_add_vertical b hbσ)).mul
    (continuous_Gamma_sub_vertical (c - a - b) hσc)).mul hs

/-- Sub-`π` exponential decay for the four-Gamma kernel of DLMF 15.6.7 along a pole-free vertical
line `Re s = σ`. -/
private lemma exists_norm_mellinBarnesOneSubKernel_le (a b c : ℂ) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (hσc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n)
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    {θ' : ℝ} (hθ' : θ' < π) :
    ∃ C : ℝ, ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
        C * Real.exp (-θ' * |y|) := by
  obtain ⟨Cc, hCc⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le (z := c - a - b - σ)
    (by simpa using hσc)
  set Cc₁ : ℝ := max Cc 0
  set Pc : ℝ := (c - a - b).re - σ - 1 / 2
  obtain ⟨C₃, _, hC₃⟩ := exists_norm_three_Gamma_mul_rpow_exp_le a b hσ haσ hbσ Pc hθ'
  refine ⟨Cc₁ * C₃, fun y ↦ ?_⟩
  have hc_le : ‖Gamma (c - a - b - (σ + y * I))‖ ≤
      Cc₁ * ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2)) := by
    have heq : c - a - b - ((σ : ℂ) + y * I) = c - a - b - σ - y * I := by ring
    rw [heq]
    have hexp : Real.exp (-π * |y| / 2) ≤ Real.exp (π * |y| / 2) :=
      Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, abs_nonneg y])
    calc ‖Gamma (c - a - b - σ - y * I)‖
        ≤ Cc₁ * (1 + |y|) ^ Pc * Real.exp (-π * |y| / 2) := by
          refine (hCc y).trans ?_
          dsimp [Pc]
          gcongr
          exact le_max_left Cc 0
      _ ≤ Cc₁ * (1 + |y|) ^ Pc * Real.exp (π * |y| / 2) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring
  have hrew : Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) =
      (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))) *
        Gamma (c - a - b - (σ + y * I)) := by ring
  rw [hrew, norm_mul]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          ‖Gamma (c - a - b - (σ + y * I))‖
      ≤ ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          (Cc₁ * ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2))) :=
        mul_le_mul_of_nonneg_left hc_le (norm_nonneg _)
    _ = Cc₁ * (‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          ((1 + |y|) ^ Pc * Real.exp (π * |y| / 2))) := by ring
    _ ≤ Cc₁ * (C₃ * Real.exp (-θ' * |y|)) :=
        mul_le_mul_of_nonneg_left (hC₃ y) (le_max_right Cc 0)
    _ = (Cc₁ * C₃) * Real.exp (-θ' * |y|) := by ring

/-- The integrand of the second hypergeometric Mellin–Barnes integral (DLMF 15.6.7) is integrable
on `ℝ` for `1 - z ∈ Complex.slitPlane` whenever the vertical line `Re s = σ` avoids the poles of
all four Gamma factors. -/
theorem integrable_mellinBarnesOneSubIntegrand (a b c : ℂ) {z : ℂ} (hz : 1 - z ∈ slitPlane)
    {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ n) (hσc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n)
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) := by
  have harg : |(1 - z).arg| < π := abs_arg_lt_pi_of_mem_slitPlane hz
  set θ' : ℝ := (|(1 - z).arg| + π) / 2
  obtain ⟨C, hC⟩ := exists_norm_mellinBarnesOneSubKernel_le a b c hσ hσc haσ hbσ
    (by dsimp [θ']; linarith : θ' < π)
  have hint := TauCeti.integrable_cpow_vertical_smul
    (continuous_mellinBarnesOneSubKernel a b c hσ hσc haσ hbσ).aestronglyMeasurable
    (slitPlane_ne_zero hz) σ (θ := θ') (by dsimp [θ']; linarith) hC
  exact hint.congr (Eventually.of_forall fun _ ↦ by dsimp; rw [mul_comm])

/-- The second hypergeometric Mellin–Barnes integral (DLMF 15.6.7) is complex differentiable in `z`
on `{z | 1 - z ∈ Complex.slitPlane}` along every pole-avoiding vertical line `Re s = σ`. -/
theorem differentiableOn_integral_mellinBarnes_one_sub (a b c : ℂ) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (hσc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n)
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) :
    DifferentiableOn ℂ
      (fun z : ℂ ↦ ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I))
      {z : ℂ | 1 - z ∈ slitPlane} := by
  have hsub : DifferentiableOn ℂ (fun z : ℂ ↦ 1 - z) {z : ℂ | 1 - z ∈ slitPlane} := by fun_prop
  have hdiff : DifferentiableOn ℂ
      ((fun w : ℂ ↦ ∫ y : ℝ, w ^ ((σ : ℂ) + y * I) •
        (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)))) ∘ fun z : ℂ ↦ 1 - z)
      {z : ℂ | 1 - z ∈ slitPlane} :=
    (TauCeti.differentiableOn_integral_cpow_vertical_smul
      (continuous_mellinBarnesOneSubKernel a b c hσ hσc haσ hbσ).aestronglyMeasurable σ
      fun θ' hθ' ↦ exists_norm_mellinBarnesOneSubKernel_le a b c hσ hσc haσ hbσ hθ').comp
      hsub fun _ hz ↦ hz
  refine hdiff.congr fun _ _ ↦ integral_congr_ae (Eventually.of_forall fun _ ↦ ?_)
  dsimp
  rw [mul_comm]

/-- The second hypergeometric Mellin–Barnes integral (DLMF 15.6.7) is holomorphic in `z` on
`{z | 1 - z ∈ Complex.slitPlane}` along every pole-avoiding vertical line `Re s = σ`. -/
theorem analyticOnNhd_integral_mellinBarnes_one_sub (a b c : ℂ) {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ n) (hσc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n)
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) :
    AnalyticOnNhd ℂ
      (fun z : ℂ ↦ ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I))
      {z : ℂ | 1 - z ∈ slitPlane} :=
  (differentiableOn_integral_mellinBarnes_one_sub a b c hσ hσc haσ hbσ).analyticOnNhd
    (isOpen_slitPlane.preimage (continuous_const.sub continuous_id))

/-- Integrability of the `n`-independent three-Gamma factor
`y ↦ Γ(a + (σ + i y)) Γ(b + (σ + i y)) Γ(c - a - b - (σ + i y))` on a separating line. -/
private lemma integrable_three_Gamma_vertical {a b c : ℂ} {σ : ℝ}
    (hσc : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (c - a - b - (σ + y * I)) := by
  obtain ⟨Cb, hCb⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow (σ := b.re + σ)
    (fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]) 0
  have h2 : Integrable fun y : ℝ ↦
      Gamma ((a + σ) + y * I) * Gamma ((c - a - b - σ) - y * I) :=
    integrable_Gamma_add_mul_Gamma_sub
      (fun n hn ↦ by simp only [add_re, ofReal_re] at hn; linarith [n.cast_nonneg' (α := ℝ)])
      (fun n hn ↦ by
        simp only [sub_re, ofReal_re] at hσc hn
        linarith [n.cast_nonneg' (α := ℝ)])
  have hb_cont := continuous_Gamma_add_vertical b (σ := σ)
    fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hb_eq (y : ℝ) :
      b + ((σ : ℂ) + y * I) = ((b.re + σ : ℝ) : ℂ) + ((b.im + y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  refine (h2.mul_bdd (c := Cb) hb_cont.aestronglyMeasurable
    (Eventually.of_forall fun y ↦ by simpa [hb_eq] using hCb (b.im + y))).congr
    (Eventually.of_forall fun y ↦ ?_)
  dsimp
  have h1 : a + (σ : ℂ) + y * I = a + ((σ : ℂ) + y * I) := by ring
  have h3 : c - a - b - (σ : ℂ) - y * I = c - a - b - ((σ : ℂ) + y * I) := by ring
  rw [h1, h3]
  ring

/-- Uniform vertical bound `‖Γ(n - (σ + i y)) (z^n / n!)‖ ≤ Γ(-σ) multichoose (-σ) n ‖z‖^n`
for `σ < 0`. -/
private lemma norm_Gamma_nat_sub_mul_div_factorial_le (z : ℂ) {σ : ℝ} (hσ : σ < 0) (n : ℕ)
    (y : ℝ) :
    ‖Gamma ((n : ℂ) - ((σ : ℂ) + y * I)) * (z ^ n / n !)‖ ≤
      Real.Gamma (-σ) * (Ring.multichoose (-σ) n * ‖z‖ ^ n) := by
  have hre_pos : 0 < ((n : ℂ) - ((σ : ℂ) + y * I)).re := by
    simp
    linarith [n.cast_nonneg' (α := ℝ)]
  have hgam_le : ‖Gamma ((n : ℂ) - ((σ : ℂ) + y * I))‖ ≤ Real.Gamma (-σ + n) := by
    refine (norm_Gamma_le_Gamma_re hre_pos).trans_eq ?_
    congr 1
    simp
    ring
  have hpoch := Real.Gamma_add_nat_div_Gamma_eq (n := n) (-σ)
    fun k hk ↦ by linarith [k.cast_nonneg' (α := ℝ)]
  have hmc := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (-σ) n
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at hmc
  have hΓpos : 0 < Real.Gamma (-σ) := Real.Gamma_pos_of_pos (by linarith)
  have hcoeff_eq : Real.Gamma (-σ + n) / n ! = Real.Gamma (-σ) * Ring.multichoose (-σ) n := by
    have h1 : Real.Gamma (-σ + n) = (ascPochhammer ℝ n).eval (-σ) * Real.Gamma (-σ) :=
      (div_eq_iff hΓpos.ne').1 hpoch
    rw [h1, ← hmc]
    field_simp [Nat.cast_ne_zero.mpr n.factorial_ne_zero]
  rw [norm_mul, norm_div, norm_pow, norm_natCast]
  calc ‖Gamma ((n : ℂ) - ((σ : ℂ) + y * I))‖ * (‖z‖ ^ n / n !)
      ≤ Real.Gamma (-σ + n) * (‖z‖ ^ n / n !) :=
        mul_le_mul_of_nonneg_right hgam_le (by positivity)
    _ = (Real.Gamma (-σ + n) / n !) * ‖z‖ ^ n := by ring
    _ = Real.Gamma (-σ) * (Ring.multichoose (-σ) n * ‖z‖ ^ n) := by rw [hcoeff_eq]; ring

/-- Pointwise binomial expansion of the DLMF 15.6.7 integrand on `‖z‖ < 1` along `Re s = σ < 0`. -/
private lemma hasSum_mellinBarnesOneSubIntegrand (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    {σ : ℝ} (hσ : σ < 0) (y : ℝ) :
    HasSum
      (fun n : ℕ ↦
        (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (c - a - b - (σ + y * I))) *
          (Gamma ((n : ℂ) - ((σ : ℂ) + y * I)) * (z ^ n / n !)))
      (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I)) := by
  set s : ℂ := (σ : ℂ) + y * I
  let G : ℂ := Gamma (a + s) * Gamma (b + s) * Gamma (c - a - b - s)
  have hs_re : 0 < (-s).re := by simp [s]; linarith
  have hs_ne : ∀ k : ℕ, -s ≠ -k := fun k hk ↦ by
    have hre := congrArg re hk
    simp [s] at hre
    linarith [k.cast_nonneg' (α := ℝ)]
  have hΓs : Gamma (-s) ≠ 0 := Gamma_ne_zero_of_re_pos hs_re
  have hbin := (TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one
    (r := -s) hz).mul_left (G * Gamma (-s))
  rw [one_div, cpow_neg, inv_inv] at hbin
  refine hbin.congr_fun fun n ↦ ?_
  have hpoch := Gamma_add_nat_div_Gamma_eq (n := n) (-s) hs_ne
  have hmc := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (-s) n
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at hmc
  have hgam_eq : Gamma (-s) * Ring.multichoose (-s) n = Gamma ((n : ℂ) - s) / n ! := by
    have h1 : Gamma (-s + n) = (ascPochhammer ℂ n).eval (-s) * Gamma (-s) :=
      (div_eq_iff hΓs).1 hpoch
    have hns : -s + (n : ℂ) = (n : ℂ) - s := by ring
    rw [hns] at h1
    rw [h1, ← hmc]
    field_simp [Nat.cast_ne_zero.mpr n.factorial_ne_zero]
  calc G * (Gamma ((n : ℂ) - s) * (z ^ n / n !))
      = G * ((Gamma ((n : ℂ) - s) / n !) * z ^ n) := by ring
    _ = G * Gamma (-s) * (Ring.multichoose (-s) n * z ^ n) := by rw [← hgam_eq]; ring

/-- **Second Mellin–Barnes representation on the unit disk**
([DLMF 15.6.7](https://dlmf.nist.gov/15.6.E7)).
For `‖z‖ < 1` and a vertical line `Re s = σ` with `max(-Re a, -Re b) < σ < min(0, Re(c - a - b))`,
`regularizedGaussHGFun a b c z = (2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫ Γ(a + (σ + i y))
  Γ(b + (σ + i y)) Γ(c - a - b - (σ + i y)) Γ(-(σ + i y)) (1 - z)^{σ + i y} dy`. -/
theorem regularizedGaussHGFun_eq_mellinBarnes_one_sub (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    {σ : ℝ} (hσ : σ < 0) (hσc : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    regularizedGaussHGFun a b c z =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) := by
  have ha : 0 < a.re := by linarith
  have hb : 0 < b.re := by linarith
  have hca : 0 < (c - a).re := by simp only [sub_re] at hσc ⊢; linarith
  have hcb : 0 < (c - b).re := by simp only [sub_re] at hσc ⊢; linarith
  have h2pi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hΓca : Gamma (c - a) ≠ 0 := Gamma_ne_zero_of_re_pos hca
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  -- Exchange sum and integral for the binomial expansion of `(1 - z)^s` by dominated convergence.
  let G : ℝ → ℂ := fun y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (c - a - b - (σ + y * I))
  let F : ℕ → ℝ → ℂ := fun n y ↦
    G y * (Gamma ((n : ℂ) - ((σ : ℂ) + y * I)) * (z ^ n / n !))
  have hG_int : Integrable G := integrable_three_Gamma_vertical hσc haσ hbσ
  let bound : ℕ → ℝ → ℝ := fun n y ↦
    (Real.Gamma (-σ) * (Ring.multichoose (-σ) n * ‖z‖ ^ n)) * ‖G y‖
  have hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n) volume := fun n ↦ by
    have hn_cont := continuous_Gamma_sub_vertical (n : ℂ) (σ := σ) fun m hm ↦ by
      simp only [natCast_re] at hm
      linarith [n.cast_nonneg' (α := ℝ), m.cast_nonneg' (α := ℝ)]
    exact hG_int.aestronglyMeasurable.mul (hn_cont.mul continuous_const).aestronglyMeasurable
  have h_bound : ∀ n : ℕ, ∀ᵐ y : ℝ ∂volume, ‖F n y‖ ≤ bound n y := fun n ↦
    Eventually.of_forall fun y ↦ by
      dsimp only [F, bound]
      rw [norm_mul (G y), mul_comm _ ‖G y‖]
      exact mul_le_mul_of_nonneg_left
        (norm_Gamma_nat_sub_mul_div_factorial_le z hσ n y) (norm_nonneg _)
  have hreal_sum := TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (r := -σ) (x := ‖z‖)
    (by simpa using hz)
  have bound_summable : ∀ᵐ y : ℝ ∂volume, Summable fun n : ℕ ↦ bound n y :=
    Eventually.of_forall fun y ↦ (hreal_sum.summable.mul_left (Real.Gamma (-σ))).mul_right ‖G y‖
  have bound_integrable : Integrable (fun y : ℝ ↦ ∑' n : ℕ, bound n y) volume := by
    have htsum : (fun y : ℝ ↦ ∑' n : ℕ, bound n y) =
        fun y : ℝ ↦ (Real.Gamma (-σ) * (1 / (1 - ‖z‖) ^ (-σ))) * ‖G y‖ := by
      ext y
      dsimp only [bound]
      rw [tsum_mul_right, tsum_mul_left, hreal_sum.tsum_eq]
    rw [htsum]
    exact hG_int.norm.const_mul _
  have h_lim : ∀ᵐ y : ℝ ∂volume, HasSum (fun n : ℕ ↦ F n y)
      (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I)) :=
    Eventually.of_forall (hasSum_mellinBarnesOneSubIntegrand a b c hz hσ)
  have hsum_int := (hasSum_integral_of_dominated_convergence bound hF_meas h_bound bound_summable
    bound_integrable h_lim).mul_left
      ((2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹)
  -- Evaluate each termwise integral via Barnes's first lemma and match the Gauss power series.
  have hterm : ∀ n : ℕ, (a.regularizedGaussHGFunSeries b c).coeff n * z ^ n =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ * (∫ y : ℝ, F n y) := by
    intro n
    dsimp only [F, G]
    simp_rw [← mul_assoc]
    rw [integral_mul_const]
    have hbarnes := integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub
      (a := a) (b := b) (c := c - a - b) (d := (n : ℂ)) (σ := σ)
      haσ hbσ hσc (by simp; linarith [n.cast_nonneg' (α := ℝ)])
    have hint_eq : (∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma ((n : ℂ) - (σ + y * I))) =
        2 * π * (Gamma (c - b) * Gamma (a + n) * Gamma (c - a) * Gamma (b + n) /
          Gamma (c + n)) := by
      have hac : a + (c - a - b) = c - b := by ring
      have hbc' : b + (c - a - b) = c - a := by ring
      have habcd : a + b + (c - a - b) + (n : ℂ) = c + n := by ring
      rw [hac, hbc', habcd] at hbarnes
      rw [← hbarnes, ← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
    rw [hint_eq, coeff_regularizedGaussHGFunSeries,
      ← Gamma_add_nat_div_Gamma_eq a fun k hk ↦ by
        have := congrArg re hk; simp at this; linarith [k.cast_nonneg' (α := ℝ)],
      ← Gamma_add_nat_div_Gamma_eq b fun k hk ↦ by
        have := congrArg re hk; simp at this; linarith [k.cast_nonneg' (α := ℝ)]]
    field_simp [h2pi, hΓa, hΓb, hΓca, hΓcb, Nat.cast_ne_zero.mpr n.factorial_ne_zero]
  have hgauss_sum : HasSum (fun n : ℕ ↦ (a.regularizedGaussHGFunSeries b c).coeff n * z ^ n)
      (regularizedGaussHGFun a b c z) := by
    have hmem : z ∈ Metric.eball (0 : ℂ) (a.regularizedGaussHGFunSeries b c).radius := by
      refine lt_of_lt_of_le ?_ (radius_regularizedGaussHGFunSeries_ge_one a b c)
      rwa [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
    simpa [regularizedGaussHGFun, regularizedGaussHGFunSeries, regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, coeff_regularizedGaussHGFunSeries, mul_comm] using
      (a.regularizedGaussHGFunSeries b c).hasSum hmem
  exact hgauss_sum.unique (hsum_int.congr_fun hterm)

end Complex

end
