/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Loop.Integral
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Loop.Pochhammer
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Gauss series evaluations of hypergeometric loop integrals

On the open unit disk, the loop around one and Pochhammer's double loop give integral
representations of the regularized Gauss series by analytic continuation in the parameters.
On the Euler convergence region, both contours agree with the series after normalization by
`Complex.hypergeometricLoopOne_eq_eulerIntegral`,
`Complex.hypergeometricPochhammerLoop_eq_eulerIntegral`, and
`Complex.regularizedGaussHGFun_eq_eulerIntegral`.
The formulas for the contour values use reciprocal Gamma factors and remain valid when those
factors vanish. Inverting the factors gives the representations in
[DLMF 15.6.2](https://dlmf.nist.gov/15.6.E2) and [DLMF 15.6.5](https://dlmf.nist.gov/15.6.E5).
-/

public section

open Metric Real Set

namespace Complex

/-- The loop around one on the open unit disk equals the regularized Gauss series times its
Gamma factor. The identity includes positive integral `c - b`, where the loop vanishes. -/
theorem hypergeometricLoopOne_eq_mul_regularizedGaussHGFun (a : ℂ) {b c z : ℂ}
    (hb : 0 < b.re) (hz : ‖z‖ < 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hzρ : closedBall (1 - z) (‖z‖ * ρ) ⊆ slitPlane) :
    hypergeometricLoopOne a b c z ρ =
      2 * π * I * Gamma b / Gamma (1 + b - c) * regularizedGaussHGFun a b c z := by
  have hloop : AnalyticOnNhd ℂ (fun w => hypergeometricLoopOne a b w z ρ) univ := fun w _ =>
    (analyticOnNhd_hypergeometricLoopOne hb hρ hρ1 (a, w, z) hzρ).comp₂
      analyticAt_const (analyticAt_id.prod analyticAt_const)
  have hseries : AnalyticOnNhd ℂ
      (fun w => 2 * π * I * Gamma b / Gamma (1 + b - w) * regularizedGaussHGFun a b w z)
      univ := by
    intro w _
    simp only [div_eq_mul_inv]
    exact (analyticAt_const.mul ((differentiable_one_div_Gamma.analyticAt _).comp
      (analyticAt_const.sub analyticAt_id))).mul
      (analyticAt_const.regularizedGaussHGFun analyticAt_const analyticAt_id analyticAt_const hz)
  have heq := hloop.eq_of_eventuallyEq hseries (z₀ := b + 1) (by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by simp : b.re < (b + 1).re)] with w hw
    rw [hypergeometricLoopOne_eq_eulerIntegral a hb hw hρ hρ1 hzρ,
      regularizedGaussHGFun_eq_eulerIntegral a hb hw hz])
  exact congrFun heq c

/-- The loop around one represents the regularized Gauss series on the open unit disk for
`0 < b.re` and `c - b ∉ {1, 2, …}` (DLMF 15.6.2). -/
theorem regularizedGaussHGFun_eq_mul_hypergeometricLoopOne (a : ℂ) {b c z : ℂ}
    (hb : 0 < b.re) (hcb : ∀ n : ℕ, c - b ≠ n + 1) (hz : ‖z‖ < 1)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : closedBall (1 - z) (‖z‖ * ρ) ⊆ slitPlane) :
    regularizedGaussHGFun a b c z =
      Gamma (1 + b - c) / (2 * π * I * Gamma b) * hypergeometricLoopOne a b c z ρ := by
  have hGb := Gamma_ne_zero_of_re_pos hb
  have hG : Gamma (1 + b - c) ≠ 0 := Gamma_ne_zero fun n hn =>
    hcb n (by linear_combination -hn)
  rw [hypergeometricLoopOne_eq_mul_regularizedGaussHGFun a hb hz hρ hρ1 hzρ]
  field_simp [Real.pi_ne_zero, I_ne_zero]

/-- Pochhammer's double-loop integral on the open unit disk equals the regularized Gauss series
times the indicated Gamma and phase factors. The identity holds for all complex parameters,
including positive integral `b` or `c - b`, where the loop vanishes. -/
theorem hypergeometricPochhammerLoop_eq_mul_regularizedGaussHGFun (a : ℂ) {b c z : ℂ}
    (hz : ‖z‖ < 1) {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A)
    (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A)
    (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane) :
    hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ =
      4 * π ^ 2 * exp (c * π * I) / (Gamma (1 - b) * Gamma (1 + b - c)) *
        regularizedGaussHGFun a b c z := by
  have hz₀ : ‖z‖ * ρ₀ < 1 :=
    (mul_le_of_le_one_right (norm_nonneg z) (by linarith)).trans_lt hz
  have hloop : AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ => hypergeometricPochhammerLoop a p.1 p.2 z A ρ₀ ρ₁) univ :=
    fun p _ =>
      (analyticOnNhd_hypergeometricPochhammerLoop hρ₀ hρ₀A hρ₁ hρ₁A (a, p.1, p.2, z)
        ⟨hz₀, hz₁⟩).comp₂ analyticAt_const
          (analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const))
  have hseries : AnalyticOnNhd ℂ (fun p : ℂ × ℂ =>
      4 * π ^ 2 * exp (p.2 * π * I) / (Gamma (1 - p.1) * Gamma (1 + p.1 - p.2)) *
        regularizedGaussHGFun a p.1 p.2 z) univ := by
    intro p _
    simp only [div_eq_mul_inv, mul_inv]
    have hb : AnalyticAt ℂ (fun w : ℂ × ℂ => w.1) p := analyticAt_fst
    have hc : AnalyticAt ℂ (fun w : ℂ × ℂ => w.2) p := analyticAt_snd
    have hphase : AnalyticAt ℂ (fun w : ℂ × ℂ => exp (w.2 * π * I)) p :=
      ((hc.mul analyticAt_const).mul analyticAt_const).cexp
    have hΓ₀ : AnalyticAt ℂ (fun w : ℂ × ℂ => (Gamma (1 - w.1))⁻¹) p :=
      (differentiable_one_div_Gamma.analyticAt _).comp (analyticAt_const.sub hb)
    have hΓ₁ : AnalyticAt ℂ (fun w : ℂ × ℂ => (Gamma (1 + w.1 - w.2))⁻¹) p :=
      (differentiable_one_div_Gamma.analyticAt _).comp ((analyticAt_const.add hb).sub hc)
    exact ((analyticAt_const.mul hphase).mul (hΓ₀.mul hΓ₁)).mul
      (analyticAt_const.regularizedGaussHGFun hb hc analyticAt_const hz)
  have hU : IsOpen {p : ℂ × ℂ | 0 < p.1.re ∧ p.1.re < p.2.re} :=
    (isOpen_lt continuous_const (continuous_re.comp continuous_fst)).inter
      (isOpen_lt (continuous_re.comp continuous_fst) (continuous_re.comp continuous_snd))
  have heq := hloop.eq_of_eventuallyEq hseries (z₀ := (1, 2)) (by
    filter_upwards [hU.mem_nhds (by simp : (0 : ℝ) < (1 : ℂ).re ∧ (1 : ℂ).re < (2 : ℂ).re)]
      with p hp
    rw [hypergeometricPochhammerLoop_eq_eulerIntegral a hp.1 hp.2 hρ₀ hρ₀A hρ₁ hρ₁A hz₀ hz₁,
      regularizedGaussHGFun_eq_eulerIntegral a hp.1 hp.2 hz])
  exact congrFun heq (b, c)

/-- Pochhammer's contour represents the regularized Gauss series on the open unit disk when
neither `b` nor `c - b` is a positive integer (DLMF 15.6.5). -/
theorem regularizedGaussHGFun_eq_mul_hypergeometricPochhammerLoop (a : ℂ) {b c z : ℂ}
    (hb : ∀ n : ℕ, b ≠ n + 1) (hcb : ∀ n : ℕ, c - b ≠ n + 1) (hz : ‖z‖ < 1)
    {A ρ₀ ρ₁ : ℝ} (hρ₀ : 0 < ρ₀) (hρ₀A : ρ₀ < A) (hρ₁ : 0 < ρ₁) (hρ₁A : ρ₁ < 1 - A)
    (hz₁ : closedBall (1 - z) (‖z‖ * ρ₁) ⊆ slitPlane) :
    regularizedGaussHGFun a b c z =
      exp (-c * π * I) * Gamma (1 - b) * Gamma (1 + b - c) / (4 * π ^ 2) *
        hypergeometricPochhammerLoop a b c z A ρ₀ ρ₁ := by
  have hGb : Gamma (1 - b) ≠ 0 := Gamma_ne_zero fun n hn => hb n (by linear_combination -hn)
  have hGcb : Gamma (1 + b - c) ≠ 0 := Gamma_ne_zero fun n hn =>
    hcb n (by linear_combination -hn)
  rw [hypergeometricPochhammerLoop_eq_mul_regularizedGaussHGFun a hz hρ₀ hρ₀A hρ₁ hρ₁A hz₁,
    neg_mul, neg_mul, exp_neg]
  field_simp [Real.pi_ne_zero, exp_ne_zero]

end Complex
