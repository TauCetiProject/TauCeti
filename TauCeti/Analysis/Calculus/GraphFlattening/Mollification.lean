/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import TauCeti.Analysis.Calculus.GraphFlattening.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Convolution

/-!
# Mollified Lipschitz shears

For a function `γ : E → ℝ`, the shear `(t, x) ↦ (t - γ x, x)` of `WithLp 2 (ℝ × E)` is
`TauCeti.graphFlattening γ`. It moves the region above the graph of `γ`, the domain of a
Lipschitz boundary chart, onto the half-space `{0 < t}`.

Mollifying `γ` with a normalized bump `ρ` gives the shears `Φ_ρ` along `ρ ⋆ γ`. Since `ρ ⋆ γ`
is smooth (`ContDiffBump.contDiff_normed_convolution`), these are smooth
(`TauCeti.contDiff_graphFlattening`) of determinant `1` (`TauCeti.det_fderiv_graphFlattening`).
This file proves `‖DΦ_ρ‖ ≤ 1 + K` for a `K`-Lipschitz `γ`
(`TauCeti.norm_fderiv_graphFlattening_normed_convolution_le`), and that `Φ_ρ` is uniformly within
`K · ρ.rOut` of the shear along `γ` (`TauCeti.dist_graphFlattening_normed_convolution_le`).
These are the inputs for the composition `u ↦ u ∘ Φ` on `W^{1,p}` through smooth
approximations.

The continuity proof of `ρ ⋆ γ` is an argument of the statements; any proof may be supplied.

## Main declarations

* `TauCeti.norm_fderiv_graphFlattening_normed_convolution_le`,
  `TauCeti.dist_graphFlattening_normed_convolution_le`: the mollified shears.
-/

public section

noncomputable section

open ContinuousLinearMap MeasureTheory
open scoped NNReal Convolution ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {γ : E → ℝ} {K : ℝ≥0}

/-- **Mollified shears have derivatives of norm at most `1 + K`** for a `K`-Lipschitz `γ`. -/
theorem norm_fderiv_graphFlattening_normed_convolution_le (hγ : LipschitzWith K γ)
    (ρ : ContDiffBump (0 : E)) (hc : Continuous (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ))
    (z : WithLp 2 (ℝ × E)) :
    ‖fderiv ℝ (graphFlattening (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] γ) hc) z‖ ≤ 1 + K :=
  norm_fderiv_graphFlattening_le_one_add
    ((ρ.contDiff_normed_convolution hγ.continuous.locallyIntegrable (n := 1)).differentiable
      one_ne_zero)
    (fun _ => norm_fderiv_le_of_lipschitz ℝ (hγ.normed_convolution ρ)) z

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
