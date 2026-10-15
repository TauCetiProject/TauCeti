/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution

/-!
# Continuous linear maps commute with convolution

A continuous linear map `L : F →L[ℝ] F'` between Banach spaces commutes with convolution against
a scalar kernel: `ρ ⋆ (L ∘ f) = L (ρ ⋆ f)` at every point where `ρ ⋆ f` exists
(`ContinuousLinearMap.convolution_lsmul_comp_comm`). This is the convolution form of
`ContinuousLinearMap.integral_comp_comm`. It lets a mollification be moved through a continuous
linear map, for instance to mollify the image of a function in a dual space.
-/

public section

open MeasureTheory
open scoped Convolution

/-- A continuous linear map commutes with convolution against a scalar kernel, at every point
where the convolution exists. -/
theorem ContinuousLinearMap.convolution_lsmul_comp_comm {G F F' : Type*} [AddGroup G]
    [MeasurableSpace G] {μ : Measure G} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup F'] [NormedSpace ℝ F'] [CompleteSpace F'] (L : F →L[ℝ] F') {ρ : G → ℝ}
    {f : G → F} {x : G}
    (h : ConvolutionExistsAt ρ f x (ContinuousLinearMap.lsmul ℝ ℝ) μ) :
    (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] fun y ↦ L (f y)) x =
      L ((ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x) := by
  have hi := h.integrable
  simp only [ContinuousLinearMap.lsmul_apply] at hi
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, ← L.integral_comp_comm hi, map_smul]
