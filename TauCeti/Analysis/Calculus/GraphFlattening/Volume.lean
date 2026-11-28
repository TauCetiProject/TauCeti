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
preserves every additive Haar measure (`TauCeti.measurePreserving_shearAlong`). For a unit vector
`ν` in an inner product space it therefore maps the measure on the half-space `{0 < ⟪y, ν⟫}` to the
measure on the region `{γ x < ⟪x, ν⟫}` above the graph of `γ`
(`TauCeti.measurePreserving_shearAlong_restrict`). This is what makes precomposition with the
shear that flattens the region above a `C¹` graph an isometry of the Lebesgue spaces.
-/

public section

open MeasureTheory Set
open scoped InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {γ : E → ℝ} {ν : E}

/-- A shear `shearAlong γ ν` with Jacobian determinant one does not change the measure of a
measurable set under an additive Haar measure. -/
private theorem addHaar_image_shearAlong (μ : Measure E) [μ.IsAddHaarMeasure]
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) {s : Set E}
    (hs : MeasurableSet s) : μ (shearAlong γ ν '' s) = μ s := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image μ hs
      (fun x _ => (differentiable_shearAlong hγ x).hasFDerivAt.hasFDerivWithinAt)
      (injective_shearAlong hγν).injOn]
  simp [abs_det_fderiv_shearAlong hγ hγν]

/-- **The shear along a direction preserves volume.** If `γ` is differentiable and invariant
under translation along `ν`, the shear `z ↦ z + γ z • ν` preserves every additive Haar measure. -/
theorem measurePreserving_shearAlong (μ : Measure E) [μ.IsAddHaarMeasure]
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) :
    MeasurePreserving (shearAlong γ ν) μ μ := by
  have hΦ : Continuous (shearAlong γ ν) := (differentiable_shearAlong hγ).continuous
  refine ⟨hΦ.measurable, Measure.ext fun s hs => ?_⟩
  -- The preimage of `s` under the shear by `γ` is its image under the shear by `-γ`.
  rw [Measure.map_apply hΦ.measurable hs, ← image_eq_preimage_of_inverse
    (shearAlong_shearAlong_neg hγν) (shearAlong_neg_shearAlong hγν)]
  exact addHaar_image_shearAlong μ hγ.neg (neg_apply_add_smul_eq hγν) hs

/-- **The shear flattens the measure above a graph.** For a unit vector `ν` and a differentiable
`γ` invariant along `ν`, the shear `shearAlong γ ν` maps an additive Haar measure restricted to the
half-space `{0 < ⟪y, ν⟫}` to its restriction to the region `{γ x < ⟪x, ν⟫}` above the graph of
`γ`. -/
theorem measurePreserving_shearAlong_restrict {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {γ : E → ℝ} {ν : E} (μ : Measure E) [μ.IsAddHaarMeasure] (hν : ‖ν‖ = 1)
    (hγ : Differentiable ℝ γ) (hγν : ∀ x (t : ℝ), γ (x + t • ν) = γ x) :
    MeasurePreserving (shearAlong γ ν) (μ.restrict {y | 0 < ⟪y, ν⟫_ℝ})
      (μ.restrict {x | γ x < ⟪x, ν⟫_ℝ}) := by
  rw [← preimage_shearAlong_setOf_lt_inner hν hγν]
  exact (measurePreserving_shearAlong μ hγ hγν).restrict_preimage
    (measurableSet_lt hγ.continuous.measurable (continuous_id.inner continuous_const).measurable)

end TauCeti
