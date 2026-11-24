/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod
public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem

/-!
# Haar measures under surjective linear maps

The image of an additive Haar measure under a surjective linear map between finite-dimensional
spaces is a positive (possibly infinite) multiple of any additive Haar measure on the target
(`LinearMap.exists_map_addHaar_eq_smul_addHaar`). Hence such a map is quasi-measure-preserving:
preimages of null sets are null. This is the linear model of the fact that submersions pull null
sets back to null sets.

For a surjective linear map `A` between finite-dimensional real spaces, the linear coordinates
`x ↦ (A x, P x)` of `ContinuousLinearMap.linearCoord`, with `P` a projection onto `ker A`, carry an
additive Haar measure on the source to a positive multiple of the product of Haar measures on the
target and on `ker A`, so integrals of products factor in these coordinates.

## Main results

* `LinearMap.quasiMeasurePreserving_of_surjective`: a surjective linear map is quasi-measure
  preserving for additive Haar measures on its source and target.
* `ContinuousLinearMap.map_linearCoord`: in the linear coordinates
  `ContinuousLinearMap.linearCoord` `x ↦ (A x, P x)` of a surjective linear map `A`, an additive
  Haar measure on the source is a positive multiple `ContinuousLinearMap.linearScale` of the
  product of Haar measures on the target and on `ker A`.
* `ContinuousLinearMap.integral_mul_linearCoord`: Fubini's theorem in these coordinates.
-/

public section

open MeasureTheory Measure

section QuasiMeasurePreserving

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

end QuasiMeasurePreserving

namespace ContinuousLinearMap

/-! ### Haar measures in the linear coordinates of a surjective linear map -/

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  (A : E →L[ℝ] E') (hA : Function.Surjective A)
  (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure E') [ν.IsAddHaarMeasure]

/-- The constant comparing `μ` with the product of `ν` and a Haar measure on `ker A`, through
`linearCoord`. -/
noncomputable def linearScale : NNReal :=
  addHaarScalarFactor (μ.map (A.linearCoord hA)) (ν.prod addHaar)

/-- The constant `linearScale` is positive. -/
theorem linearScale_pos : 0 < A.linearScale hA μ ν :=
  addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

/-- The image of `μ` under `linearCoord` is `linearScale` times the product of `ν` and a Haar
measure on `ker A`. -/
theorem map_linearCoord :
    μ.map (A.linearCoord hA) = A.linearScale hA μ ν • ν.prod addHaar :=
  isAddLeftInvariant_eq_smul _ _

/-- **Fubini in the linear coordinates.** Integrating a product `u (A x) v (P x)` against `μ`
gives `linearScale` times the product of the integrals. -/
theorem integral_mul_linearCoord {𝕜 : Type*} [RCLike 𝕜] (u : E' → 𝕜)
    (v : (A : E →ₗ[ℝ] E').ker → 𝕜) :
    ∫ x, u (A.linearCoord hA x).1 * v (A.linearCoord hA x).2 ∂μ =
      (A.linearScale hA μ ν : ℝ) • ((∫ y, u y ∂ν) * ∫ k, v k ∂addHaar) := by
  rw [← integral_prod_mul, ← NNReal.smul_def, ← integral_smul_nnreal_measure,
    ← map_linearCoord, ← (A.linearCoord hA).coe_toHomeomorph, ← Homeomorph.toMeasurableEquiv_coe,
    integral_map_equiv]

end ContinuousLinearMap
