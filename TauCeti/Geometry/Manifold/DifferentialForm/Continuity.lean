/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Geometry.Manifold.ContMDiff.ContinuousAlternatingMap

/-!
# Coordinate continuity of regular differential forms

The coordinate expression of a differential form is the fiber coordinate of its section in the
existing alternating tangent-bundle trivialization. Consequently even `C⁰` section regularity
implies coordinate continuity on the extended chart target, including boundary and corner points.
In the trivialization at any point, the fiber coordinate of a form at `y` is the form pulled back
along the inverse tangent trivialization at `y` (`TauCeti.RoughForm.trivializationAt_apply_snd`),
with no chart-domain hypothesis. Hence a form is `C^n` exactly when its values on the frames of
these trivializations are (`TauCeti.isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply`).
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The fiber coordinate of a form in the alternating-bundle trivialization at `x` is the form
pulled back along the inverse tangent trivialization at `x`. -/
theorem RoughForm.trivializationAt_apply_snd (φ : RoughForm I M F k) (x y : M) :
    (trivializationAt (E [⋀^Fin k]→L[ℝ] F) (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F) x
      ⟨y, φ y⟩).2 =
      (φ y).compContinuousLinearMap ((trivializationAt E (TangentSpace I) x).symmL ℝ y) := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  simp only [ContinuousAlternatingMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization]
  -- Composition with the identity of the trivial coefficient bundle is the identity.
  rfl

/-- **Smoothness of a form read in tangent trivializations**: for finite-dimensional model and
coefficient spaces, a form is `C^n` exactly when, near each point `x`, its values on the frame
`e.symmL y ∘ v` of the tangent trivialization `e` at `x`, for each fixed tuple `v` of model
vectors, are `C^n` at `x`. -/
theorem isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {n : WithTop ℕ∞} (φ : RoughForm I M F k) :
    IsSmoothForm I n φ ↔ ∀ (x : M) (v : Fin k → E), ContMDiffAt I 𝓘(ℝ, F) n
      (fun y ↦ φ y ((trivializationAt E (TangentSpace I) x).symmL ℝ y ∘ v)) x := by
  rw [isSmoothForm_def]
  refine forall_congr' fun x ↦ ?_
  simp only [contMDiffAt_section, RoughForm.trivializationAt_apply_snd,
    contMDiffAt_continuousAlternatingMap_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply]

/-- On an extended chart target, the form's coordinate expression is exactly its section's
fiber coordinate in the preferred alternating-bundle trivialization. -/
theorem RoughForm.inChartAt_eq_trivializationAt (φ : RoughForm I M F k) (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    φ.inChartAt α z =
      (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
        (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F) α
          ⟨(extChartAt I α).symm z, φ ((extChartAt I α).symm z)⟩).2 := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  simp only [ContinuousAlternatingMap.inCoordinates, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization]
  have hy : (extChartAt I α).symm z ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hz
  rw [TangentBundle.symmL_trivializationAt hy, (extChartAt I α).right_inv hz]
  ext v
  rw [RoughForm.inChartAt_apply]
  rfl

/-- Every regular fixed-coefficient form, including a `C⁰` form, has continuous coordinate
coefficients on each preferred extended chart target. -/
theorem IsSmoothForm.continuousOn_inChartAt {n : WithTop ℕ∞} {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I n φ) (α : M) :
    ContinuousOn (φ.inChartAt α) (extChartAt I α).target := by
  let e := trivializationAt (E [⋀^Fin k]→L[ℝ] F)
    (fun x ↦ TangentSpace I x [⋀^Fin k]→L[ℝ] F) α
  have hmap : MapsTo (fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) x (φ x))
      (extChartAt I α).source e.source := by
    intro x hx
    rw [e.mem_source]
    -- The section projects to x; reduce that projection before using the base-set formula.
    change x ∈ e.baseSet
    dsimp only [e]
    rw [FiberBundle.trivializationAt_continuousAlternatingMap_baseSet,
      TangentBundle.trivializationAt_baseSet]
    refine ⟨?_, by simp⟩
    simpa only [extChartAt_source] using hx
  have hc : ContinuousOn (fun x ↦ (e ⟨x, φ x⟩).2) (extChartAt I α).source :=
    (e.continuousOn.comp hφ.contMDiff.continuous.continuousOn hmap).snd
  apply (hc.comp (continuousOn_extChartAt_symm α) (extChartAt I α).mapsTo_symm).congr
  intro z hz
  exact φ.inChartAt_eq_trivializationAt α hz

end TauCeti
