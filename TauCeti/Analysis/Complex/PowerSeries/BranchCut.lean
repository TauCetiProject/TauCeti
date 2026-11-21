/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Branch-cut power series on a slit punctured disc

This file records differentiation and analytic uniqueness for complex functions of the form
`(z - z₀) ^ σ * ∑' s, c s * (z - z₀) ^ s` on the slit punctured disc
`{z : ℂ | z - z₀ ∈ Complex.slitPlane ∧ ‖z - z₀‖ < r}`:
* `TauCeti.hasDerivAt_cpow_mul_tsum`: termwise differentiation on the slit punctured disc.
* `TauCeti.eq_zero_of_cpow_mul_tsum_eq_zero`: vanishing on the slit punctured disc forces every
  series coefficient to vanish.
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
    let A : ℂ → ℂ := fun u ↦ ∑' s, c s * u ^ s
    HasDerivAt (fun w : ℂ ↦ (w - z₀) ^ σ * A (w - z₀))
      ((z - z₀) ^ (σ - 1) * (σ * A (z - z₀) + (z - z₀) * deriv A (z - z₀))) z := by
  intro A
  have hr : 0 < r := (norm_nonneg _).trans_lt hzb
  have hu0 : z - z₀ ≠ 0 := Complex.slitPlane_ne_zero hzs
  have hA_diff := (FormalMultilinearSeries.analyticOnNhd_tsum_ofScalars_of_norm_sub_lt c z₀ hr
    (fun w _ hwr ↦ hc w hwr) (z - z₀) (mem_ball_zero_iff.mpr hzb)).differentiableAt
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
  have hp := FormalMultilinearSeries.hasFPowerSeriesOnBall_tsum_ofScalars_of_norm_sub_lt d z₀ hr
    fun z hz0 hzr ↦ hd (z - z₀) (norm_pos_iff.mp hz0) hzr
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

end TauCeti
