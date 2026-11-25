/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import TauCeti.Topology.ContinuousMap.Bounded.Smooth
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Calculus.ContDiff.Convolution

/-!
# Mollifying bounded uniformly continuous functions

On a finite-dimensional real normed space `G` with an additive Haar measure `μ`, the
mollification `ρ ⋆ f` of a bounded uniformly continuous function `f` by a normalized bump `ρ`
is again bounded uniformly continuous, bounded by `‖f‖` and Lipschitz
(`ContDiffBump.normedConvolutionBUC`). It is smooth with bounded derivatives of every order, so
it lies in `BoundedContinuousFunction.smoothBoundedDerivativesSubmodule`
(`ContDiffBump.normedConvolutionBUC_mem_smoothBoundedDerivativesSubmodule`), and as the radii of
the bumps tend to zero it converges to `f` in the supremum norm
(`ContDiffBump.tendsto_normedConvolutionBUC`). So the smooth functions with bounded derivatives
are dense in the bounded uniformly continuous functions.

## Main declarations

* `ContDiffBump.normedConvolutionBUC`: mollification by a normalized bump, as a bounded uniformly
  continuous function.
* `ContDiffBump.normedConvolutionBUC_mem_smoothBoundedDerivativesSubmodule`: the mollification
  is smooth with bounded derivatives of every order.
* `ContDiffBump.tendsto_normedConvolutionBUC`: mollifications converge in the supremum norm as
  the bumps shrink.
-/

public section

noncomputable section

namespace ContDiffBump

open BoundedContinuousFunction ContinuousLinearMap Filter MeasureTheory Topology
open scoped Convolution

variable {G F : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The mollification `ρ ⋆ f` of a bounded uniformly continuous function by a normalized bump, as
a bounded uniformly continuous function: it is bounded by `‖f‖` and Lipschitz. -/
def normedConvolutionBUC (ρ : ContDiffBump (0 : G)) (μ : Measure G) [μ.IsAddHaarMeasure]
    (f : uniformContinuousSubmodule ℝ G F) : uniformContinuousSubmodule ℝ G F :=
  ⟨.ofNormedAddCommGroup (ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f.val : G → F))
    (ρ.hasCompactSupport_normed.continuous_convolution_left (lsmul ℝ ℝ) ρ.continuous_normed
      f.val.continuous.locallyIntegrable) ‖f.val‖
    (ρ.norm_normed_convolution_le (Eventually.of_forall f.val.norm_coe_le_norm)),
    (mem_uniformContinuousSubmodule _).2
      (ρ.hasCompactSupport_normed.lipschitzWith_convolution_left (μ := μ)
        (ρ.contDiff_normed (n := 1))
        f.val.continuous.locallyIntegrable f.val.norm_coe_le_norm).uniformContinuous⟩

/-- The mollification of `f` by `ρ` evaluates to the convolution `ρ ⋆ f`. -/
@[simp]
theorem coe_normedConvolutionBUC (ρ : ContDiffBump (0 : G)) (μ : Measure G)
    [μ.IsAddHaarMeasure] (f : uniformContinuousSubmodule ℝ G F) :
    ((ρ.normedConvolutionBUC μ f).val : G → F) = ρ.normed μ ⋆[lsmul ℝ ℝ, μ] (f.val : G → F) :=
  (rfl)

/-- The mollification of a bounded uniformly continuous function by a normalized bump is smooth
with bounded derivatives of every order. -/
theorem normedConvolutionBUC_mem_smoothBoundedDerivativesSubmodule (ρ : ContDiffBump (0 : G))
    (μ : Measure G) [μ.IsAddHaarMeasure] (f : uniformContinuousSubmodule ℝ G F) :
    ρ.normedConvolutionBUC μ f ∈ smoothBoundedDerivativesSubmodule ℝ G F := by
  refine (mem_smoothBoundedDerivativesSubmodule ℝ G F _).2 ⟨?_, fun m ↦
    ⟨‖f.val‖ * ∫ y, ‖iteratedFDeriv ℝ m (ρ.normed μ) y‖ ∂μ, fun x ↦ ?_⟩⟩
  · exact ρ.contDiff_normed_convolution f.val.continuous.locallyIntegrable
  · rw [coe_normedConvolutionBUC]
    exact ρ.hasCompactSupport_normed.norm_iteratedFDeriv_convolution_left_le
      (ρ.contDiff_normed (n := (⊤ : ℕ∞))) le_top f.val.continuous.locallyIntegrable
      f.val.norm_coe_le_norm x

/-- Mollifications by normalized bumps of radii tending to zero converge to a bounded uniformly
continuous function in the supremum norm. -/
theorem tendsto_normedConvolutionBUC [CompleteSpace F] {ι : Type*} {l : Filter ι}
    {ρ : ι → ContDiffBump (0 : G)} (hρ : Tendsto (fun i ↦ (ρ i).rOut) l (𝓝 0)) (μ : Measure G)
    [μ.IsAddHaarMeasure] (f : uniformContinuousSubmodule ℝ G F) :
    Tendsto (fun i ↦ (ρ i).normedConvolutionBUC μ f) l (𝓝 f) := by
  rw [tendsto_subtype_rng, BoundedContinuousFunction.tendsto_iff_tendstoUniformly]
  exact tendstoUniformly_normed_convolution hρ ((mem_uniformContinuousSubmodule _).1 f.property)

end ContDiffBump
