/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# Surjective linear maps are quasi-measure-preserving for Haar measures

The image of an additive Haar measure under a surjective linear map between finite-dimensional
spaces is a positive (possibly infinite) multiple of any additive Haar measure on the target
(`LinearMap.exists_map_addHaar_eq_smul_addHaar`). Hence such a map is quasi-measure-preserving:
preimages of null sets are null. This is the linear model of the fact that submersions pull null
sets back to null sets.

## Main results

* `LinearMap.quasiMeasurePreserving_of_surjective`: a surjective linear map is quasi-measure
  preserving for additive Haar measures on its source and target.
-/

public section

open MeasureTheory Measure

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [NormedSpace 𝕜 E]
  [LocallyCompactSpace E]
  [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [NormedSpace 𝕜 F]

/-- A surjective linear map out of a locally compact space is quasi-measure-preserving for
additive Haar measures on its source and target: the preimage of a null set is null. Unlike
`LinearMap.quasiMeasurePreserving`, the source and target may have different dimensions. -/
theorem LinearMap.quasiMeasurePreserving_of_surjective (L : E →ₗ[𝕜] F)
    (hL : Function.Surjective L) (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F)
    [ν.IsAddHaarMeasure] : QuasiMeasurePreserving L μ ν := by
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  obtain ⟨c, -, hc⟩ := L.exists_map_addHaar_eq_smul_addHaar μ ν hL
  exact ⟨L.continuous_of_finiteDimensional.aemeasurable, hc ▸ smul_absolutelyContinuous⟩
