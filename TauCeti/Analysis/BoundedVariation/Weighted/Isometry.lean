/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Isometric transport of weighted variation and Gaussian perimeter

A linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'` carries the weight `W` on `E'` to the weight
`W ∘ e` on `E`. Pulling a function and the weight back along `e` preserves the weighted variation
when `e` identifies the source domain `V` with the target domain `Ω`, as for the canonical
pullback `Opens.comap e Ω`; when `e` only maps `V` into `Ω`, the pulled-back weighted variation is
at most the original one. The same holds for the weighted perimeter of a preimage or an image.
Since the Gaussian weight is invariant under `e` (`LinearIsometryEquiv.gaussianWeight_comp`), the
Gaussian perimeter of a set equals that of its image, `P_{γ_{E'}}(e(U)) = P_{γ_E}(U)`; the
companion identity `γ_{E'}(e(U)) = γ_E(U)` for the standard Gaussian measure is
`LinearIsometryEquiv.stdGaussian_image`.

## Main declarations

* `LinearIsometryEquiv.weightedVariation_comp_le`, `LinearIsometryEquiv.weightedVariation_comp`
  and `LinearIsometryEquiv.weightedVariation_comap`: pulling back into a smaller domain does not
  increase the weighted variation, and exact transport preserves it.
* `LinearIsometryEquiv.weightedPerimeter_preimage_le`,
  `LinearIsometryEquiv.weightedPerimeter_preimage`, `LinearIsometryEquiv.weightedPerimeter_comap`
  and `LinearIsometryEquiv.weightedPerimeter_image`: the same for the weighted perimeter.
* `LinearIsometryEquiv.gaussianPerimeter_image` and
  `LinearIsometryEquiv.gaussianPerimeter_preimage`: invariance of the Gaussian perimeter.

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), Section 2 for the orthogonal invariance of the Gaussian measure and Section 3 for the
  weighted perimeter.
-/

public section

noncomputable section

open MeasureTheory Set TestFunction TopologicalSpace TauCeti
open scoped Distributions

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  {V : Opens E} {Ω : Opens E'} {W : E' → ℝ} {u : E' → ℝ}

namespace LinearIsometryEquiv

/-- Pulling a function and the weight back along a linear isometry equivalence `e` does not
increase the weighted variation when `e` maps `V` into `Ω`. As for the unweighted
`LinearIsometryEquiv.totalVariationOn_comp_le`, each admissible test field `X` on `V` is
transported to the field `y ↦ e (X (e.symm y))` on `Ω`. -/
theorem weightedVariation_comp_le (e : E ≃ₗᵢ[ℝ] E') (hVO : MapsTo e V Ω) :
    weightedVariation (W ∘ e) V (u ∘ e) ≤ weightedVariation W Ω u := by
  refine weightedVariation_le_iff.mpr fun X hX => ?_
  let e' : E ≃L[ℝ] E' := e.toContinuousLinearEquiv
  have hVO' : MapsTo e' V Ω := by rwa [coe_toContinuousLinearEquiv]
  -- The transported field `y ↦ e (X (e.symm y))`, a test vector field on `Ω`.
  let Y : 𝓓(Ω, E') := postcompCLM (e' : E →L[ℝ] E') (e'.transportTestFunction hVO' X)
  have hY (x : E) : Y (e x) = e (X x) := by
    simp [Y, e', ContinuousLinearEquiv.transportTestFunction_apply]
  have hdiv (x : E) : divergenceCLM Y (e x) = divergenceCLM X x := by
    simp only [Y, ContinuousLinearEquiv.divergenceCLM_postcompCLM_transportTestFunction,
      ContinuousLinearEquiv.transportTestFunction_apply, e', coe_symm_toContinuousLinearEquiv,
      symm_apply_apply]
  have hW (x : E) : fderiv ℝ (W ∘ e) x (X x) = fderiv ℝ W (e x) (Y (e x)) := by
    have h := e'.comp_right_fderiv (f := W) (x := x)
    rw [coe_toContinuousLinearEquiv] at h
    rw [h, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      coe_toContinuousLinearEquiv, hY]
  have hpair : (∫ x, (divergenceCLM X x - fderiv ℝ (W ∘ e) x (X x)) *
        Real.exp (-(W ∘ e) x) * (u ∘ e) x) =
      ∫ y, (divergenceCLM Y y - fderiv ℝ W y (Y y)) * Real.exp (-W y) * u y := by
    rw [← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding]
    simp [hdiv, hW]
  rw [hpair]
  refine ofReal_integral_le_weightedVariation Y fun y => ?_
  rw [← e.apply_symm_apply y, hY, e.norm_map]
  exact hX (e.symm y)

/-- **Isometry invariance of the weighted variation.** If a linear isometry equivalence `e`
identifies `V` with `Ω`, then pulling a function and the weight back along `e` does not change the
weighted variation. -/
theorem weightedVariation_comp (e : E ≃ₗᵢ[ℝ] E') (hVO : MapsTo e V Ω)
    (hOV : MapsTo e.symm Ω V) :
    weightedVariation (W ∘ e) V (u ∘ e) = weightedVariation W Ω u := by
  refine le_antisymm (weightedVariation_comp_le e hVO) ?_
  simpa [Function.comp_def] using
    weightedVariation_comp_le (W := W ∘ e) (u := u ∘ e) e.symm hOV

/-- The weighted variation is invariant when a function, the weight and the domain are pulled back
along a linear isometry equivalence, with the pulled-back domain written canonically as the
preimage open set. -/
theorem weightedVariation_comap (e : E ≃ₗᵢ[ℝ] E') :
    weightedVariation (W ∘ e) (Opens.comap (e : C(E, E')) Ω) (u ∘ e) =
      weightedVariation W Ω u :=
  weightedVariation_comp e (fun _ hx => Opens.mem_comap.mp hx)
    fun y hy => Opens.mem_comap.mpr (by simpa using hy)

omit [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E'] [MeasurableSpace E']
  [BorelSpace E'] in
/-- The weighted perimeter of a preimage is the weighted variation of the pulled-back indicator. -/
private theorem weightedPerimeter_preimage_eq_weightedVariation (f : E → E') (s : Set E') :
    weightedPerimeter (W ∘ f) V (f ⁻¹' s) = weightedVariation (W ∘ f) V (s.indicator 1 ∘ f) := by
  rw [weightedPerimeter_def]
  exact congrArg _ (funext fun _ => Set.indicator_comp_right (g := fun _ => (1 : ℝ)) f)

/-- Pulling a set and the weight back along a linear isometry equivalence `e` does not increase the
weighted perimeter when `e` maps `V` into `Ω`. -/
theorem weightedPerimeter_preimage_le (e : E ≃ₗᵢ[ℝ] E') (hVO : MapsTo e V Ω) (s : Set E') :
    weightedPerimeter (W ∘ e) V (e ⁻¹' s) ≤ weightedPerimeter W Ω s := by
  rw [weightedPerimeter_preimage_eq_weightedVariation, weightedPerimeter_def]
  exact weightedVariation_comp_le e hVO

/-- **Isometry invariance of the weighted perimeter.** If a linear isometry equivalence `e`
identifies `V` with `Ω`, then the weighted perimeter in `V` of the preimage of `s` for the
pulled-back weight equals the weighted perimeter of `s` in `Ω`. -/
theorem weightedPerimeter_preimage (e : E ≃ₗᵢ[ℝ] E') (hVO : MapsTo e V Ω)
    (hOV : MapsTo e.symm Ω V) (s : Set E') :
    weightedPerimeter (W ∘ e) V (e ⁻¹' s) = weightedPerimeter W Ω s := by
  rw [weightedPerimeter_preimage_eq_weightedVariation, weightedPerimeter_def]
  exact weightedVariation_comp e hVO hOV

/-- The weighted perimeter is invariant when a set, the weight and the domain are pulled back along
a linear isometry equivalence, with the pulled-back domain written canonically as the preimage open
set. -/
theorem weightedPerimeter_comap (e : E ≃ₗᵢ[ℝ] E') (s : Set E') :
    weightedPerimeter (W ∘ e) (Opens.comap (e : C(E, E')) Ω) (e ⁻¹' s) =
      weightedPerimeter W Ω s := by
  rw [weightedPerimeter_preimage_eq_weightedVariation, weightedPerimeter_def]
  exact weightedVariation_comap e

/-- The image of a set under a linear isometry equivalence `e` identifying `V` with `Ω` has, in
`Ω` and for the pushed-forward weight, the weighted perimeter of the original set in `V`. -/
theorem weightedPerimeter_image {W : E → ℝ} (e : E ≃ₗᵢ[ℝ] E') (hVO : MapsTo e V Ω)
    (hOV : MapsTo e.symm Ω V) (s : Set E) :
    weightedPerimeter (W ∘ e.symm) Ω (e '' s) = weightedPerimeter W V s := by
  rw [e.image_eq_preimage_symm]
  exact weightedPerimeter_preimage e.symm hOV (by simpa using hVO) s

/-- **Isometry invariance of the Gaussian perimeter.** The Gaussian perimeter of the preimage of a
set under a linear isometry equivalence is the Gaussian perimeter of the set. -/
@[simp]
theorem gaussianPerimeter_preimage (e : E ≃ₗᵢ[ℝ] E') (s : Set E') :
    gaussianPerimeter (e ⁻¹' s) = gaussianPerimeter s := by
  rw [gaussianPerimeter_def, gaussianPerimeter_def, ← gaussianWeight_comp e]
  exact weightedPerimeter_preimage e (mapsTo_univ _ _) (mapsTo_univ _ _) s

/-- **Isometry invariance of the Gaussian perimeter.** For a linear isometry equivalence
`e : E ≃ₗᵢ[ℝ] E'`, `P_{γ_{E'}}(e(U)) = P_{γ_E}(U)`. -/
@[simp]
theorem gaussianPerimeter_image (e : E ≃ₗᵢ[ℝ] E') (s : Set E) :
    gaussianPerimeter (e '' s) = gaussianPerimeter s := by
  rw [e.image_eq_preimage_symm, gaussianPerimeter_preimage]

end LinearIsometryEquiv
