/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import TauCeti.Analysis.Calculus.FDeriv.CircleMap

/-!
# Integration by parts along a circle

Let `γ = circleMap c R` and let `φ` be holomorphic and `g : ℂ → E` of class `C¹` on an open set
containing the circle `γ`. Integrating by parts on `[0, 2π]`, the boundary terms cancel because
`γ` is closed, and the derivative of `φ ∘ γ` is `φ'(γ θ) γ'(θ)`, so

`∫₀^{2π} φ(γ θ) • (g ∘ γ)'(θ) dθ = -∮_γ φ'(z) • g(z) dz`

(`TauCeti.intervalIntegral_smul_deriv_comp_circleMap`). Only the derivative of `g` along the
circle enters the left-hand side, so `g` need not be holomorphic.
-/

public section

open Complex Metric Set intervalIntegral
open scoped Real

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- **Integration by parts on the circle.** For `φ` holomorphic and `g : ℂ → E` of class `C¹` on
an open set `s` containing the circle `γ = circleMap c R`,
`∫₀^{2π} φ(γ θ) • (g ∘ γ)'(θ) dθ = -∮_γ φ'(z) • g(z) dz`. -/
theorem intervalIntegral_smul_deriv_comp_circleMap {φ : ℂ → ℂ} {g : ℂ → E} {s : Set ℂ}
    {c : ℂ} {R : ℝ} (hs : IsOpen s) (hsub : sphere c |R| ⊆ s) (hg : ContDiffOn ℝ 1 g s)
    (hφ : DifferentiableOn ℂ φ s) :
    ∫ θ in 0..2 * π, φ (circleMap c R θ) • deriv (fun t ↦ g (circleMap c R t)) θ =
      -∮ z in C(c, R), deriv φ z • g z := by
  have hmem (θ : ℝ) : circleMap c R θ ∈ s := hsub (circleMap_mem_sphere' c R θ)
  have hu (θ : ℝ) : HasDerivAt (fun t ↦ φ (circleMap c R t))
      (deriv φ (circleMap c R θ) * deriv (circleMap c R) θ) θ :=
    ((hφ.differentiableAt (hs.mem_nhds (hmem θ))).hasDerivAt.comp θ
      (hasDerivAt_circleMap c R θ)).congr_deriv (by rw [(hasDerivAt_circleMap c R θ).deriv])
  have hv (θ : ℝ) : HasDerivAt (fun t ↦ g (circleMap c R t))
      (deriv (fun t ↦ g (circleMap c R t)) θ) θ :=
    (((hg.differentiableOn one_ne_zero _ (hmem θ)).differentiableAt
      (hs.mem_nhds (hmem θ))).comp θ (hasDerivAt_circleMap c R θ).differentiableAt).hasDerivAt
  have hu' : Continuous fun θ ↦ deriv φ (circleMap c R θ) * deriv (circleMap c R) θ := by
    rw [funext (deriv_circleMap c R)]
    exact (((hφ.deriv hs).continuousOn).comp_continuous (continuous_circleMap c R) hmem).mul
      (by fun_prop)
  rw [integral_smul_deriv_eq_deriv_smul (fun θ _ ↦ hu θ) (fun θ _ ↦ hv θ)
    (hu'.intervalIntegrable _ _)
    ((continuous_deriv_comp_circleMap hs hsub hg).intervalIntegrable _ _)]
  have hper : circleMap c R (2 * π) = circleMap c R 0 := by
    simpa using periodic_circleMap c R 0
  rw [hper, sub_self, zero_sub, circleIntegral]
  congr 1
  refine integral_congr fun θ _ ↦ ?_
  simp only [smul_smul, mul_comm]

end TauCeti
