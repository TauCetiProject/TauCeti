/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.LinearCombination
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Branch-cut power series on a slit punctured disc

This file records differentiation, analytic uniqueness, and Wronskian factorization for complex
functions of the form `(z - z₀) ^ σ * ∑' s, c s * (z - z₀) ^ s` on the slit punctured disc
`{z : ℂ | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}`:
* `TauCeti.hasDerivAt_cpow_mul_tsum`: product-rule derivative formula on the slit punctured disc in
  terms of the inner series `A` and `deriv A` (for termwise expansion of `deriv A`, see
  `HasFPowerSeriesOnBall.deriv_ofScalars` and `HasFPowerSeriesOnBall.hasSum_mul_deriv_ofScalars`).
* `TauCeti.eq_zero_of_cpow_mul_tsum_eq_zero`: for a series with positive radius `0 < r` converging
  on the punctured disc `0 < ‖u‖ < r`, vanishing on the slit punctured disc forces every series
  coefficient to vanish.
* `TauCeti.wronskian_cpow_mul_log_eq`: Wronskian factorization for `y^{α₁} ∑ a_s y^s` and
  `y^{α₂} ∑ b_s y^s + c y^{α₁} (∑ a_s y^s) log y` on the slit disc when `c = 0` or `α₁ = α₂ + N`.
-/

public section

open Complex Metric
open scoped Topology ENNReal

namespace TauCeti

/-- First derivative of `(z - z₀)^σ ∑' s, c s * (z - z₀)^s` on the slit punctured disc,
requiring only convergence of `∑ c_s (z - z₀)^s` on `‖z - z₀‖ < r`. -/
theorem hasDerivAt_cpow_mul_tsum {z₀ σ : ℂ} {r : ℝ} {c : ℕ → ℂ}
    (hc : ∀ z, ‖z - z₀‖ < r → Summable fun s ↦ c s * (z - z₀) ^ s)
    {z : ℂ} (hzs : z - z₀ ∈ slitPlane) (hzb : ‖z - z₀‖ < r) :
    HasDerivAt (fun w : ℂ ↦ (w - z₀) ^ σ * ∑' s, c s * (w - z₀) ^ s)
      ((z - z₀) ^ (σ - 1) * (σ * (∑' s, c s * (z - z₀) ^ s) +
        (z - z₀) * deriv (fun u ↦ ∑' s, c s * u ^ s) (z - z₀))) z := by
  have hr : 0 < r := (norm_nonneg _).trans_lt hzb
  have hu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
  have hp := hasFPowerSeriesOnBall_tsum_mul_pow c (ENNReal.ofReal_pos.mpr hr)
    (le_radius_ofScalars_of_summable_sub c fun w _ hwr ↦ hc w hwr)
  have hA_diff := (hp.analyticOnNhd (z - z₀) (by
    simpa [Metric.mem_eball, edist_zero_right] using eNorm_lt_ofReal_iff.mpr hzb)).differentiableAt
  have hpow := ((hasDerivAt_id z).sub_const z₀).cpow_const (c := σ) hzs
  refine (hpow.mul (hA_diff.hasDerivAt.comp_sub_const z z₀)).congr_deriv ?_
  dsimp only [id]
  rw [cpow_eq_cpow_sub_natCast_mul_pow hu0 σ 1, Nat.cast_one, pow_one]
  ring

/-- Analytic uniqueness for branch-cut power series: if `∑' s, d s * u ^ s` converges on
`0 < ‖u‖ < r` (`0 < r`) and `(z - z₀)^α ∑' s, d s * (z - z₀)^s = 0` on
`{z | z - z₀ ∈ slitPlane ∧ ‖z - z₀‖ < r}`, then every coefficient `d s` vanishes. -/
theorem eq_zero_of_cpow_mul_tsum_eq_zero {z₀ α : ℂ} {d : ℕ → ℂ} {r : ℝ}
    (hr : 0 < r) (hd : ∀ u : ℂ, u ≠ 0 → ‖u‖ < r → Summable fun s ↦ d s * u ^ s)
    (hzero : ∀ z : ℂ, z - z₀ ∈ slitPlane → ‖z - z₀‖ < r →
      (z - z₀) ^ α * (∑' s, d s * (z - z₀) ^ s) = 0) :
    ∀ s : ℕ, d s = 0 := by
  have hp := hasFPowerSeriesOnBall_tsum_mul_pow d (ENNReal.ofReal_pos.mpr hr)
    (le_radius_ofScalars_of_summable_sub d fun z hz0 hzr ↦
      hd (z - z₀) (norm_pos_iff.mp hz0) hzr)
  set u₀ : ℂ := ((r / 2 : ℝ) : ℂ)
  have hu₀_ball : u₀ ∈ ball (0 : ℂ) r := by simp [u₀, abs_of_pos hr, half_lt_self hr]
  have hev : (fun u : ℂ ↦ ∑' s, d s * u ^ s) =ᶠ[𝓝 u₀] 0 := by
    filter_upwards [(Complex.isOpen_slitPlane.inter Metric.isOpen_ball).mem_nhds
      ⟨Complex.ofReal_mem_slitPlane.mpr (half_pos hr), hu₀_ball⟩] with u ⟨hus, hub⟩
    have hz := hzero (z₀ + u) (by simpa using hus) (by simpa using hub)
    simp only [add_sub_cancel_left] at hz
    exact (mul_eq_zero.mp hz).resolve_left
      (Complex.cpow_ne_zero_iff.mpr (.inl (Complex.slitPlane_ne_zero hus)))
  exact congrFun (hp.ofScalars_eq_zero_of_eventuallyEq_zero
    (Metric.eball_ofReal (x := (0 : ℂ)) (ε := r) ▸ (convex_ball (0 : ℂ) r).isPreconnected)
    (by rwa [Metric.eball_ofReal]) hev)

/-- The Wronskian of `y^{α₁} ∑ aₛ yˢ` and `y^{α₂} ∑ bₛ yˢ + c y^{α₁} (∑ aₛ yˢ) log y` at a point
`y` of the slit disc of convergence is `y^{α₁ + α₂ - 1} H(y)`, with `H` holomorphic on that disc,
provided that `c = 0` or `α₁ = α₂ + N`. -/
theorem wronskian_cpow_mul_log_eq {α₁ α₂ c y : ℂ} {N : ℕ} {r : ℝ} {a b : ℕ → ℂ}
    (ha : ∀ u, ‖u‖ < r → Summable fun s ↦ a s * u ^ s)
    (hb : ∀ u, ‖u‖ < r → Summable fun s ↦ b s * u ^ s)
    (hc : c = 0 ∨ α₁ = α₂ + N) (hy : y ∈ slitPlane) (hyr : ‖y‖ < r) :
    y ^ α₁ * (∑' s, a s * y ^ s) *
        deriv (fun y ↦ y ^ α₂ * (∑' s, b s * y ^ s) +
          c * (y ^ α₁ * (∑' s, a s * y ^ s) * log y)) y -
        deriv (fun y ↦ y ^ α₁ * (∑' s, a s * y ^ s)) y *
          (y ^ α₂ * (∑' s, b s * y ^ s) + c * (y ^ α₁ * (∑' s, a s * y ^ s) * log y)) =
      y ^ (α₁ + α₂ - 1) * ((α₂ - α₁) * (∑' s, a s * y ^ s) * (∑' s, b s * y ^ s) +
        y * ((∑' s, a s * y ^ s) * deriv (fun u ↦ ∑' s, b s * u ^ s) y -
          deriv (fun u ↦ ∑' s, a s * u ^ s) y * (∑' s, b s * y ^ s)) +
        c * y ^ N * (∑' s, a s * y ^ s) ^ 2) := by
  have hy0 : y ≠ 0 := slitPlane_ne_zero hy
  have h1 := hasDerivAt_cpow_mul_tsum (z₀ := 0) (σ := α₁)
    (fun u hu ↦ by simpa using ha u (by simpa using hu)) (by simpa using hy) (by simpa using hyr)
  have h2 := (hasDerivAt_cpow_mul_tsum (z₀ := 0) (σ := α₂)
    (fun u hu ↦ by simpa using hb u (by simpa using hu)) (by simpa using hy)
    (by simpa using hyr)).fun_add ((h1.fun_mul (hasDerivAt_log hy)).const_mul c)
  simp only [sub_zero] at h1 h2
  rw [h2.deriv, h1.deriv]
  set S := ∑' s, a s * y ^ s
  set T := ∑' s, b s * y ^ s
  set dS := deriv (fun u ↦ ∑' s, a s * u ^ s) y
  set dT := deriv (fun u ↦ ∑' s, b s * u ^ s) y
  have e₁ : y ^ α₁ = y ^ (α₁ - 1) * y := by
    conv_lhs => rw [show α₁ = α₁ - 1 + 1 by ring, cpow_add _ _ hy0, cpow_one]
  have e₂ : y ^ α₂ = y ^ (α₂ - 1) * y := by
    conv_lhs => rw [show α₂ = α₂ - 1 + 1 by ring, cpow_add _ _ hy0, cpow_one]
  have e₁₂ : y ^ (α₁ + α₂ - 1) = y ^ (α₁ - 1) * y ^ (α₂ - 1) * y := by
    rw [show α₁ + α₂ - 1 = α₁ - 1 + (α₂ - 1) + 1 by ring, cpow_add _ _ hy0, cpow_add _ _ hy0,
      cpow_one]
  have eN : c * y ^ (α₁ - 1) = c * (y ^ (α₂ - 1) * y ^ N) := by
    rcases hc with rfl | rfl
    · simp only [zero_mul]
    · rw [show α₂ + N - 1 = α₂ - 1 + N by ring, cpow_add _ _ hy0, cpow_natCast]
  rw [e₁, e₂, e₁₂]
  linear_combination c * y ^ (α₁ - 1) * y ^ (α₁ - 1) * y * S ^ 2 * mul_inv_cancel₀ hy0 +
    y ^ (α₁ - 1) * y * S ^ 2 * eN

end TauCeti
