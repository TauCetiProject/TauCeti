/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Polar coordinates, smoothness, and powers of `circleMap`

This file collects general facts about Mathlib's circle parametrization
`circleMap z₀ ρ θ = z₀ + ρ * exp (θ * I)`:

## Main results

* `TauCeti.circleMap_mem_ball_diff_singleton`: the circle of radius `r < R` about `z₀` lies in the
  punctured disc of radius `R`.
* `TauCeti.contDiff_circleMap_zpow`: the integer powers `θ ↦ (R e^{iθ}) ^ k` are smooth.
* `TauCeti.eq_and_eq_of_circleMap_eq`: polar uniqueness for positive radius and angles within `2π`.
* `TauCeti.arg_circleMap_sub`: for `0 < ρ` and `θ ∈ (-π, π]`, `arg (circleMap z₀ ρ θ - z₀) = θ`.
* `TauCeti.hasDerivAt_circleMap_radius`, `TauCeti.deriv_circleMap_radius`: radial derivative of
  `ρ ↦ circleMap z₀ ρ θ`.
* `TauCeti.contDiff_uncurry_circleMap`, `TauCeti.continuous_uncurry_circleMap`: joint smoothness
  and continuity of `(ρ, θ) ↦ circleMap z₀ ρ θ`.
-/

public section

namespace TauCeti

open Complex Metric Set

/-- The circle of radius `0 < r < R` about `z₀` lies in the punctured disc of radius `R`. -/
theorem circleMap_mem_ball_diff_singleton {z₀ : ℂ} {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (θ : ℝ) : circleMap z₀ r θ ∈ ball z₀ R \ {z₀} := by
  have hsph := mem_sphere.1 (circleMap_mem_sphere z₀ hr.le θ)
  refine ⟨mem_ball.2 (hsph.trans_lt hrR), fun h => ?_⟩
  rw [mem_singleton_iff.1 h, dist_self] at hsph
  exact hr.ne hsph

/-- The integer powers `θ ↦ (R e^{iθ}) ^ k = R ^ k e^{ikθ}` of a circle about the origin are
smooth. -/
theorem contDiff_circleMap_zpow (R : ℝ) (k : ℤ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun θ ↦ circleMap 0 R θ ^ k := by
  simp_rw [circleMap_zero_zpow]
  exact (contDiff_circleMap 0 (R ^ k)).comp (contDiff_const.mul contDiff_id)

/-- Polar coordinates around `z₀` determine a positive radius and an angle within `2π`: if
`0 < ρ₁`, `0 ≤ ρ₂`, `|φ₁ - φ₂| < 2π` and `circleMap z₀ ρ₁ φ₁ = circleMap z₀ ρ₂ φ₂`, then
`ρ₁ = ρ₂` and `φ₁ = φ₂`. -/
theorem eq_and_eq_of_circleMap_eq {z₀ : ℂ} {ρ₁ ρ₂ φ₁ φ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 ≤ ρ₂)
    (hφ : |φ₁ - φ₂| < 2 * Real.pi) (h : circleMap z₀ ρ₁ φ₁ = circleMap z₀ ρ₂ φ₂) :
    ρ₁ = ρ₂ ∧ φ₁ = φ₂ := by
  have hnorm : ‖circleMap z₀ ρ₁ φ₁ - z₀‖ = ‖circleMap z₀ ρ₂ φ₂ - z₀‖ := by rw [h]
  rw [circleMap_sub_center, circleMap_sub_center, norm_circleMap_zero, norm_circleMap_zero,
    abs_of_pos hρ₁, abs_of_nonneg hρ₂] at hnorm
  subst hnorm
  exact ⟨rfl, eq_of_circleMap_eq hρ₁.ne' hφ h⟩

/-- For `0 < ρ` and `θ ∈ (-π, π]`, the principal argument of `circleMap z₀ ρ θ - z₀` is `θ`. -/
theorem arg_circleMap_sub {z₀ : ℂ} {ρ θ : ℝ} (hρ : 0 < ρ) (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    arg (circleMap z₀ ρ θ - z₀) = θ := by
  rw [circleMap_sub_center, circleMap_zero, arg_real_mul _ hρ, arg_exp_mul_I,
    (toIocMod_eq_self Real.two_pi_pos).2 ⟨hθ.1, by linarith [hθ.2]⟩]

/-- Holding the centre `z₀` and angle `θ` fixed, `ρ ↦ circleMap z₀ ρ θ` has derivative
`exp (θ * I)` at every `ρ : ℝ`. -/
theorem hasDerivAt_circleMap_radius (z₀ : ℂ) (θ ρ : ℝ) :
    HasDerivAt (fun r : ℝ ↦ circleMap z₀ r θ) (exp ((θ : ℂ) * I)) ρ := by
  have h : HasDerivAt (fun r : ℝ ↦ z₀ + (r : ℂ) * exp ((θ : ℂ) * I))
      (0 + (1 : ℂ) * exp ((θ : ℂ) * I)) ρ :=
    (hasDerivAt_const ρ z₀).add ((hasDerivAt_id ρ).ofReal_comp.mul_const (exp ((θ : ℂ) * I)))
  simpa only [circleMap, zero_add, one_mul] using h

/-- Holding the centre `z₀` and angle `θ` fixed, `deriv (fun r ↦ circleMap z₀ r θ) ρ = exp (θ * I)`.
-/
theorem deriv_circleMap_radius (z₀ : ℂ) (θ ρ : ℝ) :
    deriv (fun r : ℝ ↦ circleMap z₀ r θ) ρ = exp ((θ : ℂ) * I) :=
  (hasDerivAt_circleMap_radius z₀ θ ρ).deriv

/-- The polar map `(ρ, θ) ↦ circleMap z₀ ρ θ` is `C^n` on `ℝ × ℝ` for every `n : WithTop ℕ∞`. -/
theorem contDiff_uncurry_circleMap (z₀ : ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (Function.uncurry (circleMap z₀)) := by
  have hexp : ContDiff ℝ n (fun p : ℝ × ℝ ↦ exp ((p.2 : ℂ) * I)) :=
    ((contDiff_exp (𝕜 := ℂ)).restrict_scalars ℝ).comp
      ((ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const)
  exact contDiff_const.add ((ofRealCLM.contDiff.comp contDiff_fst).mul hexp)

/-- The polar map `(ρ, θ) ↦ circleMap z₀ ρ θ` is jointly continuous in radius and angle. -/
theorem continuous_uncurry_circleMap (z₀ : ℂ) :
    Continuous (Function.uncurry (circleMap z₀)) :=
  (contDiff_uncurry_circleMap z₀ (n := 0)).continuous

end TauCeti
