/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted
public import TauCeti.Analysis.Distribution.TestFunction.LinearEquiv
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Isometric transport of weighted variation and Gaussian perimeter

A linear isometry equivalence `e : E ≃ₗᵢ[ℝ] E'` carries the weight `W` on `E'` to the weight
`W ∘ e` on `E`, and the weighted variation is unchanged when a function, its open domain and the
weight are pulled back along `e`. Since the Gaussian weight is `‖x‖² / 2` plus a constant
depending only on the dimension, it is invariant under `e`, so the Gaussian perimeter and the
standard Gaussian measure of a set are those of its image:
`P_{γ_{E'}}(e(U)) = P_{γ_E}(U)` and `γ_{E'}(e(U)) = γ_E(U)`.

The proof transports each admissible test vector field `X` to `y ↦ e (X (e.symm y))`, as for the
unweighted variation in `TauCeti.Analysis.BoundedVariation.Isometry`; the weighted divergence is
transported because `D(W ∘ e)(x) v = DW(e x)(e v)`.

## Main declarations

* `LinearIsometryEquiv.weightedVariation_comp_le` and
  `LinearIsometryEquiv.weightedVariation_comp`: pulling back into a smaller domain does not
  increase the weighted variation, and exact transport preserves it.
* `LinearIsometryEquiv.weightedPerimeter_preimage` and
  `LinearIsometryEquiv.weightedPerimeter_image`: the same for the weighted perimeter.
* `LinearIsometryEquiv.gaussianPerimeter_image`, `LinearIsometryEquiv.gaussianPerimeter_preimage`
  and `LinearIsometryEquiv.stdGaussian_image`: invariance of the Gaussian perimeter and the
  standard Gaussian measure.

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), Section 3.
-/

public section

noncomputable section

open MeasureTheory Set TestFunction TopologicalSpace TauCeti ProbabilityTheory
open scoped Distributions

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace E'] [BorelSpace E']
  {V : Opens E} {Ω : Opens E'} {W : E' → ℝ} {u : E' → ℝ}

namespace LinearIsometryEquiv

/-- Pulling a function and the weight back along a linear isometry equivalence `e` does not
increase the weighted variation when `e` maps `V` into `Ω`. -/
theorem weightedVariation_comp_le (e : E ≃ₗᵢ[ℝ] E') (hVO : MapsTo e V Ω) :
    weightedVariation (W ∘ e) V (u ∘ e) ≤ weightedVariation W Ω u := by
  refine weightedVariation_le_iff.mpr fun X hX => ?_
  let e' : E ≃L[ℝ] E' := e.toContinuousLinearEquiv
  have hVO' : MapsTo e' V Ω := hVO
  -- The transported field `y ↦ e (X (e.symm y))`, a test vector field on `Ω`.
  let Y : 𝓓(Ω, E') := postcompCLM (e' : E →L[ℝ] E') (e'.transportTestFunction hVO' X)
  have hY (x : E) : Y (e x) = e (X x) := by
    simp [Y, e', ContinuousLinearEquiv.transportTestFunction_apply]
  have hdiv (x : E) : divergenceCLM Y (e x) = divergenceCLM X x := by
    simp only [Y, ContinuousLinearEquiv.divergenceCLM_postcompCLM_transportTestFunction,
      ContinuousLinearEquiv.transportTestFunction_apply, e', coe_symm_toContinuousLinearEquiv,
      symm_apply_apply]
  have hW (x : E) : fderiv ℝ (W ∘ e) x (X x) = fderiv ℝ W (e x) (Y (e x)) := by
    rw [hY]
    exact congrArg (fun L : E →L[ℝ] ℝ => L (X x)) (e'.comp_right_fderiv (f := W) (x := x))
  have hpair : (∫ x, (divergenceCLM X x - fderiv ℝ (W ∘ e) x (X x)) *
        Real.exp (-(W ∘ e) x) * (u ∘ e) x) =
      ∫ y, (divergenceCLM Y y - fderiv ℝ W y (Y y)) * Real.exp (-W y) * u y := by
    rw [← e.measurePreserving.integral_comp e.toMeasurableEquiv.measurableEmbedding]
    simp [hdiv, hW]
  rw [hpair]
  refine ofReal_integral_le_weightedVariation Y fun y => ?_
  rw [show Y y = e (X (e.symm y)) by simpa using hY (e.symm y), e.norm_map]
  exact hX _

/-- **Isometry invariance of the weighted variation.** If a linear isometry equivalence `e`
identifies `V` with `Ω`, then pulling a function and the weight back along `e` does not change the
weighted variation. -/
theorem weightedVariation_comp (e : E ≃ₗᵢ[ℝ] E') (hVO : MapsTo e V Ω)
    (hOV : MapsTo e.symm Ω V) :
    weightedVariation (W ∘ e) V (u ∘ e) = weightedVariation W Ω u := by
  refine le_antisymm (weightedVariation_comp_le e hVO) ?_
  simpa [Function.comp_def] using
    weightedVariation_comp_le (W := W ∘ e) (u := u ∘ e) e.symm hOV

/-- **Isometry invariance of the weighted perimeter.** If a linear isometry equivalence `e`
identifies `V` with `Ω`, then the weighted perimeter in `V` of the preimage of `s` for the
pulled-back weight equals the weighted perimeter of `s` in `Ω`. -/
theorem weightedPerimeter_preimage (e : E ≃ₗᵢ[ℝ] E') (hVO : MapsTo e V Ω)
    (hOV : MapsTo e.symm Ω V) (s : Set E') :
    weightedPerimeter (W ∘ e) V (e ⁻¹' s) = weightedPerimeter W Ω s := by
  rw [weightedPerimeter_def, weightedPerimeter_def, ← weightedVariation_comp e hVO hOV]
  exact congrArg _ (funext fun _ => Set.indicator_comp_right (g := fun _ => (1 : ℝ)) e)

/-- The image of a set under a linear isometry equivalence `e` identifying `V` with `Ω` has, in
`Ω` and for the pushed-forward weight, the weighted perimeter of the original set in `V`. -/
theorem weightedPerimeter_image {W : E → ℝ} (e : E ≃ₗᵢ[ℝ] E') (hVO : MapsTo e V Ω)
    (hOV : MapsTo e.symm Ω V) (s : Set E) :
    weightedPerimeter (W ∘ e.symm) Ω (e '' s) = weightedPerimeter W V s := by
  rw [e.image_eq_preimage_symm]
  exact weightedPerimeter_preimage e.symm hOV (by simpa using hVO) s

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E'] [BorelSpace E'] in
/-- The Gaussian weight is invariant under linear isometry equivalences. -/
theorem gaussianWeight_comp (e : E ≃ₗᵢ[ℝ] E') : gaussianWeight E' ∘ e = gaussianWeight E := by
  ext x
  simp [gaussianWeight_def, e.toLinearEquiv.finrank_eq]

/-- **Isometry invariance of the Gaussian perimeter.** The Gaussian perimeter of the preimage of a
set under a linear isometry equivalence is the Gaussian perimeter of the set. -/
theorem gaussianPerimeter_preimage (e : E ≃ₗᵢ[ℝ] E') (s : Set E') :
    gaussianPerimeter (e ⁻¹' s) = gaussianPerimeter s := by
  rw [gaussianPerimeter_def, gaussianPerimeter_def, ← gaussianWeight_comp e]
  exact weightedPerimeter_preimage e (mapsTo_univ _ _) (mapsTo_univ _ _) s

/-- **Isometry invariance of the Gaussian perimeter.** For a linear isometry equivalence
`e : E ≃ₗᵢ[ℝ] E'`, `P_{γ_{E'}}(e(U)) = P_{γ_E}(U)`. -/
theorem gaussianPerimeter_image (e : E ≃ₗᵢ[ℝ] E') (s : Set E) :
    gaussianPerimeter (e '' s) = gaussianPerimeter s := by
  rw [e.image_eq_preimage_symm, gaussianPerimeter_preimage]

/-- **Isometry invariance of the standard Gaussian measure.** For a linear isometry equivalence
`e : E ≃ₗᵢ[ℝ] E'`, `γ_{E'}(e(U)) = γ_E(U)`, for every set `U`. -/
theorem stdGaussian_image (e : E ≃ₗᵢ[ℝ] E') (s : Set E) :
    stdGaussian E' (e '' s) = stdGaussian E s := by
  rw [← stdGaussian_map e]
  change Measure.map e.toMeasurableEquiv (stdGaussian E) (e.toMeasurableEquiv '' s) = _
  rw [MeasurableEquiv.map_apply, MeasurableEquiv.preimage_image]

end LinearIsometryEquiv
