/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
public import TauCeti.Geometry.Manifold.DifferentialForm.Support
import TauCeti.Geometry.Manifold.DifferentialForm.Chart
public import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Chart regularity and support of the manifold exterior derivative

On a `C²` manifold, the exterior derivative of a `C^p` form is `C^r` whenever `r + 1 ≤ p`,
including infinite regularity. Its locality prevents
its topological support from enlarging, so compactly supported forms retain compact support.
Alternating-bundle fibre coordinates identify chart expressions and transfer section regularity
to flat regularity, including within subsets at boundary points.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
* Mathlib's alternating-bundle coordinates and inverse tangent coordinates.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

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
  -- The tangent fibre and model have different bundled instances. Evaluate the derivative
  -- in the model fibre so rewriting its base point does not require dependent transport.
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


/-- Locality of the actual exterior derivative prevents enlargement of a form's support.
No regularity assumption is needed. -/
theorem RoughForm.tsupport_mextDeriv_subset (φ : RoughForm I M F k) :
    _root_.tsupport (α := E [⋀^Fin (k + 1)]→L[ℝ] F) (TauCeti.mextDeriv φ) ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ := by
  -- Expose support as a closure: its dependent form fibres do not match function-support lemmas.
  change closure {x | TauCeti.mextDeriv φ x ≠ 0} ⊆ _
  apply closure_minimal _ (_root_.isClosed_tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)
  intro x hx
  by_contra hnot
  have hz : ∀ᶠ y in 𝓝 x, φ y = (0 : RoughForm I M F k) y := by
    have hn := (_root_.isClosed_tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ).isOpen_compl
    filter_upwards [hn.mem_nhds hnot] with y hy
    exact _root_.image_eq_zero_of_notMem_tsupport (α := E [⋀^Fin _]→L[ℝ] F) hy
  have heq := mextDeriv_congr_of_eventuallyEq hz
  rw [mextDeriv_zero] at heq
  exact hx heq

/-- Compact support is preserved by the actual exterior derivative, without a regularity
assumption. -/
theorem RoughForm.isCompact_tsupport_mextDeriv {φ : RoughForm I M F k}
    (hφ : IsCompact (_root_.tsupport (α := E [⋀^Fin k]→L[ℝ] F) φ)) :
    IsCompact (_root_.tsupport (α := E [⋀^Fin (k + 1)]→L[ℝ] F) (TauCeti.mextDeriv φ)) :=
  hφ.of_isClosed_subset (_root_.isClosed_tsupport (α := E [⋀^Fin _]→L[ℝ] F) _)
    (φ.tsupport_mextDeriv_subset)

section Regularity

/-- In the form's own preferred chart, its section regularity is its coordinate regularity
within the model range at the chart center. -/
theorem IsSmoothForm.contDiffWithinAt_inChartAt_self [IsManifold I 1 M]
    {n : WithTop ℕ∞}
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I n φ) (x : M) :
    ContDiffWithinAt ℝ n (φ.inChartAt x) (range I) (extChartAt I x x) := by
  have hc := φ.contDiffWithinAt_inChartAt (s := univ)
    (hφ.contMDiff x).contMDiffWithinAt
  simpa only [preimage_univ, univ_inter] using hc

/-- On a `C²` manifold, the actual exterior derivative read in any preferred chart is the
flat exterior derivative of the original coordinate expression. -/
theorem IsSmoothForm.inChartAt_mextDeriv_eq [IsManifold I 2 M]
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I 1 φ) (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    (TauCeti.mextDeriv φ).inChartAt α z = extDerivWithin (φ.inChartAt α) (range I) z :=
  φ.inChartAt_mextDeriv hz
    ((hφ.contDiffWithinAt_inChartAt_self _).differentiableWithinAt one_ne_zero)

/-- Regularity of the coordinate expression in each point's own preferred chart implies
regularity of the differential-form section. -/
theorem IsSmoothForm.of_contDiffWithinAt_inChartAt_self [IsManifold I 1 M]
    {r : WithTop ℕ∞} {φ : RoughForm I M F k}
    (hφ : ∀ x, ContDiffWithinAt ℝ r (φ.inChartAt x) (range I) (extChartAt I x x)) :
    IsSmoothForm I r φ := by
  rw [isSmoothForm_def]
  intro x
  rw [contMDiffAt_section x, contMDiffAt_iff_source,
    contMDiffWithinAt_iff_contDiffWithinAt]
  have heq : (fun z ↦ (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
      (fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F) x
        ⟨(extChartAt I x).symm z, φ ((extChartAt I x).symm z)⟩).2) =ᶠ[
          𝓝[range I] (extChartAt I x x)] φ.inChartAt x := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with z hz
    exact (φ.inChartAt_eq_trivializationAt x hz).symm
  exact (hφ x).congr_of_eventuallyEq heq (heq.self_of_nhdsWithin
    (extChartAt_target_subset_range x (mem_extChartAt_target x)))

/-- On a `C²` manifold, the exterior derivative of a `C^p` form is `C^r` when
`r + 1 ≤ p`. This includes smooth and analytic regularity; all form degrees and normed
coefficient spaces are allowed. -/
theorem IsSmoothForm.mextDeriv [IsManifold I 2 M] {p r : WithTop ℕ∞}
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I p φ) (hrp : r + 1 ≤ p) :
    IsSmoothForm I r (TauCeti.mextDeriv φ) := by
  have hp : (1 : WithTop ℕ∞) ≤ p := (le_add_self : (1 : WithTop ℕ∞) ≤ r + 1).trans hrp
  have hφ₁ : IsSmoothForm I 1 φ := (isSmoothForm_def _ _).mpr (hφ.contMDiff.of_le hp)
  apply IsSmoothForm.of_contDiffWithinAt_inChartAt_self
  intro x
  have hx : extChartAt I x x ∈ range I :=
    extChartAt_target_subset_range x (mem_extChartAt_target x)
  have hc := contDiffWithinAt_extDerivWithin
    (hφ.contDiffWithinAt_inChartAt_self x) I.uniqueDiffOn hrp hx
  have heq : (TauCeti.mextDeriv φ).inChartAt x =ᶠ[𝓝[range I] (extChartAt I x x)]
      extDerivWithin (φ.inChartAt x) (range I) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with z hz
    exact hφ₁.inChartAt_mextDeriv_eq x hz
  exact hc.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin hx)

end Regularity

end TauCeti
