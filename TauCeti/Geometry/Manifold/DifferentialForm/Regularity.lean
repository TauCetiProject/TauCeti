/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Regularity of differential forms in charts

The fibre coordinate of a fixed-coefficient form in the alternating-map bundle is its pullback
along the inverse extended chart. This transfers smooth-section regularity to the flat
regularity needed for exterior differentiation, including within subsets at boundary points.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
* Mathlib's alternating-bundle coordinates (`ContinuousAlternatingMap.inCoordinates`) and
  inverse tangent coordinates (`TangentBundle.symmL_trivializationAt`).
-/

public section

noncomputable section

open Set Bundle
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace RoughForm

/-- The alternating-bundle fibre coordinate of a form is its inverse-chart pullback. -/
theorem inCoordinates_eq_inChartAt [IsManifold I 1 M] (φ : RoughForm I M F k)
    {x₀ x : M} (hx : x ∈ (extChartAt I x₀).source) :
    ContinuousAlternatingMap.inCoordinates E F x₀ x x₀ x (φ x) =
      φ.inChartAt x₀ (extChartAt I x₀ x) := by
  simp only [ContinuousAlternatingMap.inCoordinates,
    Bundle.Trivial.eq_trivialization M F (trivializationAt F (Trivial M F) x₀),
    Bundle.Trivial.continuousLinearMapAt_trivialization]
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, inChartAt_apply]
  simp only [Function.comp_apply, ContinuousLinearMap.id_apply]
  rw [TangentBundle.symmL_trivializationAt (by simpa only [extChartAt_source] using hx)]
  -- The model tangent fibre is canonically E; evaluate before identifying the base point.
  change φ x (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
      (range I) (extChartAt I x₀ x) (v i)) = _
  rw [(extChartAt I x₀).left_inv hx]

/-- A differentiable section has a differentiable coordinate expression in the preferred chart,
with derivatives taken within the inverse image of the subset intersected with the model range. -/
theorem differentiableWithinAt_inChartAt [IsManifold I 1 M]
    (φ : RoughForm I M F k) {s : Set M} {x : M}
    (hφ : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) s x) :
    DifferentiableWithinAt ℝ (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x) := by
  have hc := (mdifferentiableWithinAt_section I φ).mp hφ
  have hflat := hc.differentiableWithinAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.comp_def, id_eq,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply] at hflat
  have heq : (fun z ↦ ContinuousAlternatingMap.inCoordinates E F x
      ((extChartAt I x).symm z) x ((extChartAt I x).symm z)
        (φ ((extChartAt I x).symm z))) =ᶠ[𝓝[range I] (extChartAt I x x)] φ.inChartAt x := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    rw [φ.inCoordinates_eq_inChartAt ((extChartAt I x).map_target hz),
      (extChartAt I x).right_inv hz]
  exact hflat.congr_of_eventuallyEq (heq.symm.filter_mono (nhdsWithin_mono _ inter_subset_right))
    (by
      rw [extChartAt_to_inv]
      exact (φ.inCoordinates_eq_inChartAt (mem_extChartAt_source x)).symm)

/-- Section regularity within a subset implies flat regularity in the chart centred at the
point. The derivative set is the inverse image of the subset intersected with the model range. -/
theorem contDiffWithinAt_inChartAt [IsManifold I 1 M] {n : WithTop ℕ∞}
    (φ : RoughForm I M F k) {s : Set M} {x : M}
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) s x) :
    ContDiffWithinAt ℝ n (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x) := by
  have hc := contMDiffWithinAt_section.mp hφ
  rw [contMDiffWithinAt_iff] at hc
  have hflat := hc.2
  simp only [extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.comp_def, id_eq,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply]
    at hflat
  have heq : (fun z ↦ ContinuousAlternatingMap.inCoordinates E F x
      ((extChartAt I x).symm z) x ((extChartAt I x).symm z)
        (φ ((extChartAt I x).symm z))) =ᶠ[𝓝[range I] (extChartAt I x x)] φ.inChartAt x := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    rw [φ.inCoordinates_eq_inChartAt ((extChartAt I x).map_target hz),
      (extChartAt I x).right_inv hz]
  exact hflat.congr_of_eventuallyEq (heq.symm.filter_mono (nhdsWithin_mono _ inter_subset_right))
    (by
      rw [extChartAt_to_inv]
      exact (φ.inCoordinates_eq_inChartAt (mem_extChartAt_source x)).symm)

end RoughForm

end TauCeti
