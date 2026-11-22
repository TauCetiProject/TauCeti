/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# Within-range derivatives of inverse extended charts

Provides within-range manifold derivative formulas for `(extChartAt I α).symm`:

* `TauCeti.mfderivWithin_extChartAt_symm_apply_eq_trivializationAt_symm`: on a chart target, the
  within-range derivative of `(extChartAt I α).symm` evaluates as the inverse preferred
  tangent-bundle trivialization.
* `TauCeti.mfderivWithin_extChartAt_symm_eq_comp_fderivWithin`: on chart overlaps, the within-range
  derivative of `(extChartAt I x₀).symm` factors through `(extChartAt I x).symm` and the
  within-range coordinate-change derivative.
* `TauCeti.hasMFDerivWithinAt_extChartAt_symm_self`: the inverse extended chart at `x` has the
  identity as its manifold derivative within `range I` at `extChartAt I x x`, with no smoothness
  hypothesis on the atlas.
-/

public section

open Set
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The inverse of the preferred extended chart at `x` has the identity as its manifold derivative
within `range I` at the chart image `extChartAt I x x` of its centre. There is no smoothness
hypothesis on the atlas. -/
theorem hasMFDerivWithinAt_extChartAt_symm_self (x : M) :
    HasMFDerivWithinAt 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (extChartAt I x x)
      (ContinuousLinearMap.id 𝕜 E) := by
  refine ⟨(continuousAt_extChartAt_symm x).continuousWithinAt, ?_⟩
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, preimage_id_eq, id_eq, modelWithCornersSelf_coe, range_id, inter_univ,
    (extChartAt I x).left_inv (mem_extChartAt_source x)]
  exact (hasFDerivWithinAt_id (𝕜 := 𝕜) (extChartAt I x x) (range I)).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin x) fun _ hy ↦
      (extChartAt I x).right_inv hy)
    ((extChartAt I x).right_inv (mem_extChartAt_target x))

section IsManifold

variable [IsManifold I 1 M]

/-- On the target of a preferred extended chart, the within-range derivative of
`(extChartAt I α).symm` evaluates as the inverse preferred tangent-bundle trivialization at `α`. -/
theorem mfderivWithin_extChartAt_symm_apply_eq_trivializationAt_symm (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) (v : E) :
    mfderivWithin 𝓘(𝕜, E) I (extChartAt I α).symm (range I) y v =
      (trivializationAt E (TangentSpace I) α).symm ((extChartAt I α).symm y) v := by
  have hx : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hy
  -- `TangentSpace 𝓘(𝕜, E) y` is definitionally `E`.
  rw [← (trivializationAt E (TangentSpace I) α).symmL_apply (R := 𝕜)
    (by rwa [TangentBundle.trivializationAt_baseSet]),
    TangentBundle.symmL_trivializationAt hx, (extChartAt I α).right_inv hy]; rfl

/-- On an overlap of preferred extended charts, the within-range derivative of
`(extChartAt I x₀).symm` factors through `(extChartAt I x).symm` and the within-range derivative of
`extChartAt I x ∘ (extChartAt I x₀).symm`. -/
theorem mfderivWithin_extChartAt_symm_eq_comp_fderivWithin {x₀ x : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) :
    mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) z =
      (mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I)
        (extChartAt I x ((extChartAt I x₀).symm z))).comp
        (fderivWithin 𝕜 (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z) := by
  have hpre : (extChartAt I x₀).symm ⁻¹' (extChartAt I x).source ∈ 𝓝[range I] z :=
    (continuousAt_extChartAt_symm'' hz).continuousWithinAt.preimage_mem_nhdsWithin
      (extChartAt_source_mem_nhds' hx)
  have hcoord : ((extChartAt I x).symm ∘ (extChartAt I x ∘ (extChartAt I x₀).symm))
      =ᶠ[𝓝[range I] z] (extChartAt I x₀).symm :=
    Filter.Eventually.mono hpre fun _ ha ↦ (extChartAt I x).left_inv ha
  have hcomp := mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq
    (I' := 𝓘(𝕜, E)) (I'' := I) (u := range I) z
    (mdifferentiableWithinAt_extChartAt_symm ((extChartAt I x).map_source hx))
    ((contDiffWithinAt_ext_coord_change (𝕜 := 𝕜) (n := 1) x x₀ (by
      rw [PartialEquiv.trans_source]
      exact ⟨by simpa only [PartialEquiv.symm_source] using hz, hx⟩)).differentiableWithinAt
        (by simp)).mdifferentiableWithinAt
    (Filter.Eventually.mono hpre fun _ ha ↦
      extChartAt_target_subset_range x ((extChartAt I x).map_source ha))
    (I.uniqueDiffOn.uniqueDiffWithinAt
      (extChartAt_target_subset_range x₀ hz)).uniqueMDiffWithinAt rfl
  rwa [hcoord.mfderivWithin_eq ((extChartAt I x).left_inv hx),
    mfderivWithin_eq_fderivWithin] at hcomp

end IsManifold

end TauCeti
