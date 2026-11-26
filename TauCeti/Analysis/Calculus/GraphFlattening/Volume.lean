/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.Analysis.Calculus.GraphFlattening.Direction
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The shear along a direction preserves volume

For a differentiable function `γ` on a finite-dimensional real normed space `E`, invariant under
translation along a vector `ν`, the shear `TauCeti.shearAlong γ ν z = z + γ z • ν` is a bijection
of `E` whose inverse is the shear by `-γ`, and its derivative is a transvection, of Jacobian
determinant one (`TauCeti.det_fderiv_shearAlong`). By the change of variables formula it therefore
preserves every additive Haar measure (`TauCeti.measurePreserving_shearAlong`). This is what makes
precomposition with the shear that flattens the region above a `C¹` graph an isometry of the
Lebesgue spaces.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {γ : E → ℝ} {ν : E}

/-- A shear `shearAlong γ ν` with Jacobian determinant one does not change the measure of a
measurable set under an additive Haar measure. -/
private theorem addHaar_image_shearAlong (μ : Measure E) [μ.IsAddHaarMeasure]
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) {s : Set E}
    (hs : MeasurableSet s) : μ (shearAlong γ ν '' s) = μ s := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image μ hs
      (fun x _ => (hasFDerivAt_shearAlong (hγ x)).hasFDerivWithinAt)
      (Function.LeftInverse.injective (g := shearAlong (-γ) ν)
        (shearAlong_neg_shearAlong hγν)).injOn]
  have hdet (x : E) : (ContinuousLinearMap.id ℝ E + (fderiv ℝ γ x).smulRight ν).det = 1 := by
    rw [← fderiv_shearAlong (hγ x), det_fderiv_shearAlong hγν (hγ x)]
  simp [hdet]

/-- **The shear along a direction preserves volume.** If `γ` is differentiable and invariant
under translation along `ν`, the shear `z ↦ z + γ z • ν` preserves every additive Haar measure. -/
theorem measurePreserving_shearAlong (μ : Measure E) [μ.IsAddHaarMeasure]
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) :
    MeasurePreserving (shearAlong γ ν) μ μ := by
  have hγν' : ∀ x (t : ℝ), (-γ) (x + t • ν) = (-γ) x := fun x t => by
    simp only [Pi.neg_apply, hγν]
  have hΦ : Continuous (shearAlong γ ν) :=
    Differentiable.continuous (𝕜 := ℝ) fun y => (hasFDerivAt_shearAlong (hγ y)).differentiableAt
  refine ⟨hΦ.measurable, Measure.ext fun s hs => ?_⟩
  -- The preimage of `s` under the shear by `γ` is its image under the shear by `-γ`.
  rw [Measure.map_apply hΦ.measurable hs, ← image_eq_preimage_of_inverse
    (shearAlong_shearAlong_neg hγν) (shearAlong_neg_shearAlong hγν)]
  exact addHaar_image_shearAlong μ hγ.neg hγν' hs

end TauCeti
