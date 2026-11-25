/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import TauCeti.Analysis.Calculus.GraphFlattening.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Sobolev.Mollification.Lipschitz

/-!
# Mollified Lipschitz shears

For a function `γ : E → ℝ`, the shear `(t, x) ↦ (t - γ x, x)` of `WithLp 2 (ℝ × E)` is
`TauCeti.graphFlattening γ`. It moves the region above the graph of `γ`, the domain of a
Lipschitz boundary chart, onto the half-space `{0 < t}`.

Mollifying `γ` with a normalized bump `ρ` gives the smooth shears `Φ_ρ` along `ρ ⋆ γ`
(`TauCeti.contDiff_graphFlattening_normed_convolution`), of determinant `1`, with
`‖DΦ_ρ‖ ≤ 1 + K` for a `K`-Lipschitz `γ`
(`TauCeti.norm_fderiv_graphFlattening_normed_convolution_le`), uniformly within `K · ρ.rOut` of
the shear along `γ` (`TauCeti.dist_graphFlattening_normed_convolution_le`). These are the inputs
for the composition `u ↦ u ∘ Φ` on `W^{1,p}` through smooth approximations.

The continuity proof of `ρ ⋆ γ` is an argument of the statements; any proof may be supplied.

## Main declarations

* `TauCeti.contDiff_graphFlattening_normed_convolution`,
  `TauCeti.det_fderiv_graphFlattening_normed_convolution`,
  `TauCeti.norm_fderiv_graphFlattening_normed_convolution_le`,
  `TauCeti.dist_graphFlattening_normed_convolution_le`: the mollified shears.
-/

public section

noncomputable section

open ContinuousLinearMap MeasureTheory
open scoped NNReal Convolution ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {γ : E → ℝ} {K : ℝ≥0}

/-- **Mollified shears are smooth**, for every locally integrable `γ`. -/
theorem contDiff_graphFlattening_normed_convolution (hγ : LocallyIntegrable γ μ)
    (ρ : ContDiffBump (0 : E)) (hc : Continuous (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ)) :
    ContDiff ℝ ∞ (graphFlattening (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ) hc) :=
  contDiff_graphFlattening
    (ρ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ρ.contDiff_normed hγ)

/-- **Mollified shears have Jacobian `1`**, for every locally integrable `γ`. -/
theorem det_fderiv_graphFlattening_normed_convolution (hγ : LocallyIntegrable γ μ)
    (ρ : ContDiffBump (0 : E)) (hc : Continuous (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ))
    (z : WithLp 2 (ℝ × E)) :
    LinearMap.det (fderiv ℝ (graphFlattening (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ) hc) z).toLinearMap =
      1 :=
  det_fderiv_graphFlattening hc ((ρ.hasCompactSupport_normed.contDiff_convolution_left (n := 1)
    (lsmul ℝ ℝ) ρ.contDiff_normed hγ).differentiable one_ne_zero _)

/-- **Mollified shears have derivatives of norm at most `1 + K`** for a `K`-Lipschitz `γ`. -/
theorem norm_fderiv_graphFlattening_normed_convolution_le (hγ : LipschitzWith K γ)
    (ρ : ContDiffBump (0 : E)) (hc : Continuous (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ))
    (z : WithLp 2 (ℝ × E)) :
    ‖fderiv ℝ (graphFlattening (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ) hc) z‖ ≤ 1 + K :=
  norm_fderiv_graphFlattening_le_one_add
    ((ρ.hasCompactSupport_normed.contDiff_convolution_left (n := 1) (lsmul ℝ ℝ)
      ρ.contDiff_normed hγ.continuous.locallyIntegrable).differentiable one_ne_zero)
    (hγ.norm_fderiv_normed_convolution_le ρ) z

/-- **Mollified shears are uniformly close**: the shear along `ρ ⋆ γ` is within `K · ρ.rOut` of
the shear along a `K`-Lipschitz `γ`, at every point. -/
theorem dist_graphFlattening_normed_convolution_le (hγ : LipschitzWith K γ)
    (ρ : ContDiffBump (0 : E)) (hc : Continuous (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ))
    (z : WithLp 2 (ℝ × E)) :
    dist (graphFlattening (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ) hc z)
      (graphFlattening γ hγ.continuous z) ≤ K * ρ.rOut := by
  rw [dist_graphFlattening_graphFlattening]
  exact hγ.dist_normed_convolution_le ρ z.snd

end TauCeti
