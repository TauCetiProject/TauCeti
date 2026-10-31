/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz

/-!
# Mollification of Lipschitz functions

Let `ψ` be `K`-Lipschitz on a finite-dimensional real normed space and let `ρ` be a smooth bump
centred at `0`. The mollification `ρ.normed μ ⋆ ψ` stays within `K` times the outer radius of `ρ`
of `ψ`. Its derivative in a direction `v` is the mollification of the directional derivative
`∂_v ψ`, which exists almost everywhere by Rademacher's theorem and is the weak derivative of `ψ`.
Hence these derivatives are bounded by `K ‖v‖`. When the radii shrink to zero with a bounded ratio
of outer to inner radius, they converge to `∂_v ψ` almost everywhere, by the Lebesgue
differentiation theorem.

These are the estimates that pass an identity proved for smooth factors to Lipschitz ones by
dominated convergence, as in the Leibniz rule `TauCeti.HasWeakLineDerivOn.lipschitzWith_smul`.

## Main results

* `LipschitzWith.dist_normed_convolution_le`: mollification moves a `K`-Lipschitz function by at
  most `K` times the outer radius of the bump.
* `LipschitzWith.fderiv_normed_convolution_apply`: the directional derivative of the mollification
  is the mollification of the almost-everywhere directional derivative.
* `LipschitzWith.norm_fderiv_normed_convolution_apply_le`: these derivatives are bounded by
  `K ‖v‖`.
* `LipschitzWith.ae_tendsto_fderiv_normed_convolution_apply`: they converge almost everywhere to
  the directional derivative as the bumps shrink.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed.,
  §4.2.2 and §4.2.3.
-/

public section

open ContinuousLinearMap Filter Metric MeasureTheory
open scoped NNReal Convolution ContDiff Topology

namespace LipschitzWith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {K : ℝ≥0}

/-- Mollifying a `K`-Lipschitz function by a normalized bump moves each value by at most `K` times
the outer radius of the bump. -/
theorem dist_normed_convolution_le {g : E → F} (hg : LipschitzWith K g) (ρ : ContDiffBump (0 : E))
    (x : E) : dist ((ρ.normed μ ⋆[lsmul ℝ ℝ, μ] g) x) (g x) ≤ K * ρ.rOut :=
  ρ.dist_normed_convolution_le hg.continuous.aestronglyMeasurable fun y hy =>
    (hg.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (mem_ball.1 hy).le K.2)

variable {ψ : E → ℝ}

/-- The derivative in a direction `v` of the mollification of a Lipschitz function is the
mollification of its directional derivative `∂_v ψ`, which exists almost everywhere. -/
theorem fderiv_normed_convolution_apply (hψ : LipschitzWith K ψ) (ρ : ContDiffBump (0 : E))
    (x v : E) :
    fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x v =
      (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] fun y => lineDeriv ℝ ψ y v) x := by
  have hweak : TauCeti.HasWeakLineDerivOn μ ⊤ ψ (fun y => lineDeriv ℝ ψ y v) v :=
    hψ.locallyLipschitz.locallyLipschitzOn.hasWeakLineDerivOn
      ((hψ.ae_lineDifferentiableAt v).mono fun x hx _ => hx.hasLineDerivAt)
  have hl := hweak.lineDeriv_convolution_right hψ.continuous.locallyIntegrable (ρ.normed μ)
    ρ.contDiff_normed ρ.hasCompactSupport_normed x (by simp)
  have hsmooth : ContDiff ℝ ∞ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) :=
    ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed
      hψ.continuous.locallyIntegrable
  rw [convolution_flip, convolution_flip] at hl
  rw [← hl, (hsmooth.differentiable (by simp) x).lineDeriv_eq_fderiv]

/-- The derivatives in a direction `v` of the mollifications of a `K`-Lipschitz function are
bounded by `K ‖v‖`. -/
theorem norm_fderiv_normed_convolution_apply_le (hψ : LipschitzWith K ψ)
    (ρ : ContDiffBump (0 : E)) (x v : E) :
    ‖fderiv ℝ (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x v‖ ≤ K * ‖v‖ := by
  rw [hψ.fderiv_normed_convolution_apply, ← dist_zero_right]
  exact dist_convolution_le (by positivity) ρ.support_normed_eq.subset ρ.nonneg_normed
    ρ.integral_normed (measurable_lineDeriv hψ.continuous).aestronglyMeasurable fun y _ => by
      rw [dist_zero_right]
      exact norm_lineDeriv_le_of_lipschitz ℝ hψ

/-- As normalized bumps shrink to `0` with a bounded ratio of outer to inner radius, the
derivatives in a direction `v` of the mollifications of a Lipschitz function converge almost
everywhere to its directional derivative `∂_v ψ`. -/
theorem ae_tendsto_fderiv_normed_convolution_apply (hψ : LipschitzWith K ψ) {ι : Type*}
    {l : Filter ι} {ρ : ι → ContDiffBump (0 : E)} {C : ℝ}
    (hρ : Tendsto (fun i => (ρ i).rOut) l (𝓝 0)) (h'ρ : ∀ᶠ i in l, (ρ i).rOut ≤ C * (ρ i).rIn)
    (v : E) :
    ∀ᵐ x ∂μ, Tendsto (fun i => fderiv ℝ ((ρ i).normed μ ⋆[lsmul ℝ ℝ, μ] ψ) x v) l
      (𝓝 (lineDeriv ℝ ψ x v)) := by
  filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hρ h'ρ
    ((hψ.memLp_lineDeriv v).locallyIntegrable le_top)] with x hx
  simpa only [hψ.fderiv_normed_convolution_apply] using hx

end LipschitzWith
