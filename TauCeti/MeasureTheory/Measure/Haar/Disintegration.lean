/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Prod
public import TauCeti.Analysis.Calculus.ImplicitFunction.Basic
import TauCeti.MeasureTheory.Function.LocallyIntegrable

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
* `MeasureTheory.LocallyIntegrableOn.comp_surjective`: local integrability on an open set pulls
  back along a surjective linear map.
* `MeasureTheory.IntegrableOn.exists_mem_nhds_integrableOn_of_comp_surjective`: if `g ∘ A` is
  integrable on a neighbourhood of `x`, then `g` is integrable on a neighbourhood of `A x`.
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

/-! ### Integrability along a surjective linear map -/

namespace MeasureTheory

open Set Filter
open scoped Topology

variable {E E' G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] [NormedAddCommGroup G]
  {μ : Measure E} [μ.IsAddHaarMeasure] {ν : Measure E'} [ν.IsAddHaarMeasure]
  {A : E →L[ℝ] E'}

omit [μ.IsAddHaarMeasure] in
/-- Integrability of a function of the first coordinate against the image of `μ` under
`ContinuousLinearMap.linearCoord` is integrability of its pullback along `A`. -/
private theorem integrableOn_map_linearCoord_iff (hA : Function.Surjective A) {g : E' → G}
    {s : Set (E' × (A : E →ₗ[ℝ] E').ker)} :
    IntegrableOn (fun z : E' × (A : E →ₗ[ℝ] E').ker => g z.1) s (μ.map (A.linearCoord hA)) ↔
      IntegrableOn (g ∘ A) (A.linearCoord hA ⁻¹' s) μ := by
  have hgL : (fun z : E' × (A : E →ₗ[ℝ] E').ker => g z.1) ∘ (A.linearCoord hA).toHomeomorph =
      g ∘ A :=
    funext fun y => by simp
  refine (A.linearCoord hA).toHomeomorph.measurableEmbedding.integrableOn_map_iff.trans ?_
  rw [hgL, ContinuousLinearEquiv.coe_toHomeomorph]

/-- Local integrability on an open set `V` pulls back along a surjective linear map `A` to
`A⁻¹ V`. -/
theorem LocallyIntegrableOn.comp_surjective {g : E' → G} {V : Set E'} (hV : IsOpen V)
    (hg : LocallyIntegrableOn g V ν) (hA : Function.Surjective A) :
    LocallyIntegrableOn (g ∘ A) (A ⁻¹' V) μ := by
  set L := A.linearCoord hA
  have hp : LocallyIntegrableOn (fun z : E' × (A : E →ₗ[ℝ] E').ker => g z.1) (Prod.fst ⁻¹' V)
      (μ.map L) := by
    rw [A.map_linearCoord hA μ ν]
    exact (hg.comp_fst hV).smul_measure ENNReal.coe_ne_top
  intro x hx
  obtain ⟨t, ht, hgt⟩ := hp (L x) (by simpa [L] using hx)
  refine ⟨L ⁻¹' t, L.continuous.continuousWithinAt.tendsto_nhdsWithin
    (fun y hy => by simpa [L] using hy) ht, (integrableOn_map_linearCoord_iff hA).1 hgt⟩

/-- If `g ∘ A` is integrable on a neighbourhood of `x`, for a surjective linear map `A`, then `g`
is integrable on a neighbourhood of `A x`. -/
theorem IntegrableOn.exists_mem_nhds_integrableOn_of_comp_surjective {g : E' → G} {s : Set E}
    {x : E} (hs : s ∈ 𝓝 x) (hg : IntegrableOn (g ∘ A) s μ) (hA : Function.Surjective A) :
    ∃ t ∈ 𝓝 (A x), IntegrableOn g t ν := by
  set L := A.linearCoord hA
  have hs' : L.symm ⁻¹' s ∈ 𝓝 (L x) :=
    L.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hs)
  obtain ⟨t₁, ht₁, t₂, ht₂, hst⟩ := mem_nhds_prod_iff.1 hs'
  refine ⟨t₁, by simpa [L] using ht₁, ?_⟩
  -- Pass to `μ.map L`, a positive multiple of the product measure.
  have hmap : IntegrableOn (fun z : E' × (A : E →ₗ[ℝ] E').ker => g z.1) (t₁ ×ˢ t₂)
      (μ.map L) := by
    refine (integrableOn_map_linearCoord_iff hA).2 (hg.mono_set fun y hy => ?_)
    simpa [L] using hst hy
  have hc : (A.linearScale hA μ ν)⁻¹ • μ.map L = ν.prod Measure.addHaar := by
    rw [A.map_linearCoord hA μ ν, smul_smul, inv_mul_cancel₀ (A.linearScale_pos hA μ ν).ne',
      one_smul]
  have hprod : IntegrableOn (fun z : E' × (A : E →ₗ[ℝ] E').ker => g z.1) (t₁ ×ˢ t₂)
      (ν.prod Measure.addHaar) := by
    rw [← hc, IntegrableOn, Measure.restrict_smul]
    exact hmap.integrable.smul_measure_nnreal
  rw [IntegrableOn, ← Measure.prod_restrict] at hprod
  refine hprod.of_comp_fst ?_
  rw [Ne, Measure.restrict_eq_zero]
  exact (Measure.measure_pos_of_mem_nhds _ ht₂).ne'

end MeasureTheory
