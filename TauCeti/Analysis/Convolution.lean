/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution

/-!
# Continuous linear maps commute with convolution

A continuous linear map `L : F →L[𝕜] F'` between real or complex Banach spaces commutes with
convolution against a scalar kernel `ρ : G → 𝕜`: `ρ ⋆ (L ∘ f) = L (ρ ⋆ f)` at every point where
`ρ ⋆ f` exists (`ContinuousLinearMap.convolution_lsmul_comp_comm`). This is the convolution form
of `ContinuousLinearMap.integral_comp_comm`. It lets a mollification be moved through a continuous
linear map, for instance to mollify the image of a function in a dual space.
-/

public section

open MeasureTheory
open scoped Convolution

/-- A continuous linear map commutes with convolution against a scalar kernel, at every point
where the convolution exists. -/
theorem ContinuousLinearMap.convolution_lsmul_comp_comm {𝕜 G F F' : Type*} [RCLike 𝕜] [Sub G]
    [MeasurableSpace G] {μ : Measure G} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
    [CompleteSpace F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedSpace ℝ F']
    [CompleteSpace F'] (L : F →L[𝕜] F') {ρ : G → 𝕜} {f : G → F} {x : G}
    (h : ConvolutionExistsAt ρ f x (ContinuousLinearMap.lsmul 𝕜 𝕜) μ) :
    (ρ ⋆[ContinuousLinearMap.lsmul 𝕜 𝕜, μ] fun y ↦ L (f y)) x =
      L ((ρ ⋆[ContinuousLinearMap.lsmul 𝕜 𝕜, μ] f) x) := by
  simpa only [convolution_lsmul, ContinuousLinearMap.lsmul_apply, map_smul] using
    L.integral_comp_comm h.integrable
