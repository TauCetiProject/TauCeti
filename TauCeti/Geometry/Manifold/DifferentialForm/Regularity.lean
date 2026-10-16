/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Chart
public import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Regularity of differential forms in charts

The fibre coordinate of a fixed-coefficient form in the alternating-map bundle is its pullback
along the inverse extended chart. This transfers smooth-section regularity to the flat
regularity needed for exterior differentiation, including within subsets at boundary points.

Conversely, flat regularity of a coordinate expression gives regularity of the section. Since the
flat exterior derivative of a `C^(n+1)` form is `C^n`, the manifold exterior derivative takes
`C^(n+1)` sections to `C^n` sections, on any manifold of class `C²` over any model with corners.
In particular it maps smooth `k`-forms to smooth `(k+1)`-forms.

## Main declarations

* `TauCeti.RoughForm.contDiffWithinAt_inChartAt`: a `C^n` section has `C^n` chart expressions.
* `TauCeti.contMDiffOn_mextDerivWithin`, `TauCeti.isSmoothBundleForm_mextDeriv`: the exterior
  derivative lowers regularity by one.
* `TauCeti.mextDeriv_mem_smoothForms`: the exterior derivative preserves smooth forms.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
* Mathlib's alternating-bundle coordinates (`ContinuousAlternatingMap.inCoordinates`) and
  inverse tangent coordinates (`TangentBundle.symmL_trivializationAt`).
-/

public section

noncomputable section

open Set Filter Bundle
open scoped ContDiff Manifold Topology

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

/-- Near the chart point, the coordinate expression of `mextDerivWithin φ s` in the chart centred
at `x` is the flat exterior derivative of the coordinate expression of `φ` within the coordinate
set. The form is `C¹` as a section on `s`, which has unique derivatives and is contained in the
closure of its interior. -/
theorem inChartAt_mextDerivWithin_eventuallyEq [IsManifold I 2 M] (φ : RoughForm I M F k)
    {s : Set M}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 1
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) s)
    (hs : UniqueMDiffOn I s) (hsc : s ⊆ closure (interior s)) (x : M) :
    RoughForm.inChartAt (I := I) (mextDerivWithin φ s) x
      =ᶠ[𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x x)]
        extDerivWithin (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I) := by
  filter_upwards [nhdsWithin_mono _ inter_subset_right
    (extChartAt_target_mem_nhdsWithin (I := I) x), self_mem_nhdsWithin] with z hz hzt
  exact φ.inChartAt_mextDerivWithin hs hz hzt.1 (hsc hzt.1)
    ((φ.contDiffWithinAt_inChartAt (hφ _ hzt.1)).differentiableWithinAt one_ne_zero)

end RoughForm

/-- The exterior derivative within a subset costs one derivative: if `φ` is a `C^(n+1)` section on
`s`, then `mextDerivWithin φ s` is a `C^n` section on `s`. The subset has unique derivatives and is
contained in the closure of its interior; it may contain boundary and corner points. -/
theorem contMDiffOn_mextDerivWithin [IsManifold I 2 M] (φ : RoughForm I M F k) {s : Set M}
    {n : WithTop ℕ∞}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) (n + 1)
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) s)
    (hs : UniqueMDiffOn I s) (hsc : s ⊆ closure (interior s)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) y (mextDerivWithin φ s y)) s := by
  intro x hx
  let t : Set E := (extChartAt I x).symm ⁻¹' s ∩ range I
  let a : Set E := (extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target
  have hxs : (extChartAt I x).symm (extChartAt I x x) ∈ s := by
    simpa only [extChartAt_to_inv] using hx
  have hta : t =ᶠ[𝓝 (extChartAt I x x)] a := by
    filter_upwards [extChartAt_target_eventuallyEqSet_of_mem (mem_extChartAt_target (I := I) x)]
      with z hz
    simp only [t, a, mem_inter_iff, hz]
  -- The flat exterior derivative is `C^n` on the chart image of `s`, which has unique derivatives.
  have ha : ContDiffWithinAt ℝ n (extDerivWithin (φ.inChartAt x) a) a (extChartAt I x x) :=
    contDiffWithinAt_extDerivWithin ((φ.contDiffWithinAt_inChartAt (hφ x hx)).mono
        (inter_subset_inter_right _ (extChartAt_target_subset_range x)))
      (by simpa only [a, inter_comm] using hs.uniqueDiffOn_target_inter x) le_rfl
      ⟨hxs, mem_extChartAt_target x⟩
  have ht : ContDiffWithinAt ℝ n (extDerivWithin (φ.inChartAt x) t) t (extChartAt I x x) := by
    rw [contDiffWithinAt_congr_set hta]
    refine ha.congr_of_eventuallyEq_of_mem ?_ ⟨hxs, mem_extChartAt_target x⟩
    filter_upwards [nhdsWithin_le_nhds hta.eventuallyEq_nhds] with z hz
    exact extDerivWithin_congr_set hz
  -- Read the section in the bundle chart at `x`; there it is the coordinate expression above.
  rw [contMDiffWithinAt_section, contMDiffWithinAt_iff_source,
    contMDiffWithinAt_iff_contDiffWithinAt]
  refine ht.congr_of_eventuallyEq_of_mem ?_ ⟨hxs, mem_range_self _⟩
  filter_upwards [φ.inChartAt_mextDerivWithin_eventuallyEq (hφ.of_le le_add_self) hs hsc x,
    nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin (I := I) x)]
    with z hz hzT
  simp only [Function.comp_apply, FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  rw [RoughForm.inCoordinates_eq_inChartAt _ ((extChartAt I x).map_target hzT),
    (extChartAt I x).right_inv hzT, hz]

/-- The exterior derivative takes `C^(n+1)` fixed-coefficient forms to `C^n` forms, over any model
with corners. -/
theorem isSmoothBundleForm_mextDeriv [IsManifold I 2 M] {n : WithTop ℕ∞} (φ : RoughForm I M F k)
    (hφ : IsSmoothBundleForm (I := I) (F := F) (V := Trivial M F) (n + 1) φ) :
    IsSmoothBundleForm (I := I) (F := F) (V := Trivial M F) n (mextDeriv φ) := by
  rw [isSmoothBundleForm_def] at hφ ⊢
  simp only [← mextDerivWithin_univ, ← contMDiffOn_univ]
  exact contMDiffOn_mextDerivWithin φ hφ.contMDiffOn (uniqueMDiffOn_univ (I := I)) (by simp)

/-- The exterior derivative of a smooth fixed-coefficient form is smooth. -/
theorem mextDeriv_mem_smoothForms [IsManifold I 2 M] {φ : RoughForm I M F k}
    (hφ : φ ∈ smoothForms I M F k) : mextDeriv φ ∈ smoothForms I M F (k + 1) :=
  mem_smoothForms.mpr <| isSmoothBundleForm_mextDeriv (n := ∞) φ <| by
    simpa only [show (∞ : WithTop ℕ∞) + 1 = ∞ by simp] using mem_smoothForms.mp hφ

end TauCeti
