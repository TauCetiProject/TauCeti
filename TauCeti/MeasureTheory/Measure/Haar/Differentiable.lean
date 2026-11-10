/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.Analysis.Calculus.Sard.LowDimension
public import TauCeti.MeasureTheory.Measure.Haar.Lipschitz

/-!
# Differentiable images of Haar-null sets

Let `E` and `F` be finite-dimensional real normed spaces with `finrank ℝ E ≤ finrank ℝ F`. A map
`f : E → F` that is differentiable on a set `s` which is null for an additive Haar measure on `E`
sends `s` to a set which is null for every additive Haar measure on `F`.

In equal dimensions, composing with a linear equivalence `F ≃L[ℝ] E` reduces this to Mathlib's
`MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` for maps from `E` to
itself, and the inverse linear equivalence, being Lipschitz, carries the null image back to `F` by
`LipschitzOnWith.addHaar_image_eq_zero`. When `F` has larger dimension, the image of `s` is null
by `DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank`, whether or not `s` is null.
-/

public section

open MeasureTheory Module Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Differentiable maps preserve Haar-null sets.** If `f : E → F` is differentiable on a set
`s` that is null for an additive Haar measure `μ` on `E`, and `E` and `F` are finite-dimensional
real normed spaces with `finrank ℝ E ≤ finrank ℝ F`, then `f '' s` is null for every additive
Haar measure `ν` on `F`. -/
theorem DifferentiableOn.addHaar_image_eq_zero (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] (hdim : finrank ℝ E ≤ finrank ℝ F) {f : E → F}
    {s : Set E} (hf : DifferentiableOn ℝ f s) (hs : μ s = 0) : ν (f '' s) = 0 := by
  rcases hdim.lt_or_eq with hlt | heq
  · exact hf.addHaar_image_eq_zero_of_finrank_lt_finrank ν hlt
  let e : F ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq heq.symm
  have hz := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
    (e.differentiable.comp_differentiableOn hf) hs
  have him := e.symm.toContinuousLinearMap.lipschitzWith.lipschitzOnWith.addHaar_image_eq_zero
    μ ν heq.le hz
  simpa only [image_comp, image_image, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply, image_id'] using him
