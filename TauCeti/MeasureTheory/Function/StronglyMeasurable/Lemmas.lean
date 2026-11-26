/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

/-!
# Almost everywhere strong measurability of applied continuous linear maps

Applying an a.e. strongly measurable family `f` of continuous linear maps to an a.e. strongly
measurable family `g` of vectors gives the a.e. strongly measurable function `x ↦ f x (g x)`
(`MeasureTheory.AEStronglyMeasurable.clm_apply`). This is the measurable counterpart of
`Continuous.clm_apply`; Mathlib's `MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap`
covers only a constant vector, and `ContinuousLinearMap.aestronglyMeasurable_comp₂` only a fixed
bilinear map.
-/

public section

namespace MeasureTheory

variable {α 𝕜 E F : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Applying an a.e. strongly measurable family of continuous linear maps to an a.e. strongly
measurable family of vectors gives an a.e. strongly measurable function. -/
theorem AEStronglyMeasurable.clm_apply {f : α → E →L[𝕜] F} {g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x ↦ f x (g x)) μ :=
  (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable₂ hf hg

end MeasureTheory
