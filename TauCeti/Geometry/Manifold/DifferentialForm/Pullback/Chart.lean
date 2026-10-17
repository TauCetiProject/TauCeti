/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv

/-!
# Coordinate expressions of actual manifold pullback

The coordinate expression of a pullback uses the within-range derivative of the map composed
with the inverse source chart. This is the actual manifold chain rule, including boundary
points, and supplies the coefficient transport used in interval and product comparisons.
-/

public section

noncomputable section

open Set
open scoped Manifold Topology

namespace TauCeti.RoughForm

variable {E H M E' H' M' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The actual pullback's coefficient in a preferred source chart is obtained from the
within-range derivative of the composite with its inverse chart. -/
theorem inChartAt_mpullback (ω : RoughForm I' M' F k) (f : M → M') (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target)
    (hf : MDifferentiableAt I I' f ((extChartAt I α).symm z)) :
    (mpullback I I' f ω).inChartAt α z =
      (ω (f ((extChartAt I α).symm z))).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, E) I' (f ∘ (extChartAt I α).symm) (range I) z) := by
  have hd := mfderiv_comp_mfderivWithin (I := 𝓘(ℝ, E)) (I' := I) (I'' := I') z hf
    (mdifferentiableWithinAt_extChartAt_symm hz)
    (I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range α hz)
      |>.uniqueMDiffWithinAt)
  ext v
  rw [inChartAt_apply, mpullback_apply]
  have he := congrArg (fun L : E →L[ℝ] TangentSpace I' (f ((extChartAt I α).symm z)) ↦
    ω (f ((extChartAt I α).symm z)) (fun i ↦ L (v i))) hd
  exact he.symm

end TauCeti.RoughForm

namespace TauCeti.RoughForm

variable {E H M X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- For a model-valued map, actual pullback coefficients use its ordinary within-range
Fréchet derivative, with the canonical model tangent identification made explicit. -/
theorem inChartAt_mpullback_modelSpace (ω : RoughForm 𝓘(ℝ, X) X F k) (f : M → X)
    (α : M) {z : E} (hz : z ∈ (extChartAt I α).target)
    (hf : MDifferentiableAt I 𝓘(ℝ, X) f ((extChartAt I α).symm z)) :
    (mpullback I 𝓘(ℝ, X) f ω).inChartAt α z =
      (ω (f ((extChartAt I α).symm z))).compContinuousLinearMap
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ)
          (f ((extChartAt I α).symm z))).symm.toContinuousLinearMap.comp
          (fderivWithin ℝ (f ∘ (extChartAt I α).symm) (range I) z)) := by
  rw [inChartAt_mpullback ω f α hz hf, mfderivWithin_eq_fderivWithin]
  rfl

end TauCeti.RoughForm
