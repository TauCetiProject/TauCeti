/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Analysis.Complex.ReImTopology
public import TauCeti.Geometry.Manifold.Boundary.Basic

/-!
# The closed upper half-plane as a model with corners

`ClosedUpperHalfPlane` is the subtype of complex numbers with nonnegative imaginary part.
`closedUpperHalfPlaneModel` is its real model with corners in `ℂ`. Its manifold interior is the
open upper half-plane, and its manifold boundary is the real axis. The inverse of the model
retracts the lower half-plane onto the real axis; it is only a model inverse on the model range.

The real coordinate comparison uses `(Im z, Re z)`: Mathlib's `EuclideanHalfSpace 2` requires
its *first* coordinate to be nonnegative. Thus the normal coordinate precedes the tangential one,
whereas complex coordinates conventionally write `z = s + it`. The comparison is a smooth
real diffeomorphism up to the boundary. Smooth chart changes preserve the real boundary, by
Mathlib's invariance of the manifold interior under local diffeomorphisms.
-/

public section

noncomputable section

open Set Complex
open scoped Manifold ContDiff Topology

namespace TauCeti

/-- The closed upper half-plane, including its real boundary. -/
abbrev ClosedUpperHalfPlane := {z : ℂ // 0 ≤ z.im}

namespace ClosedUpperHalfPlane

/-- A real number as a point on the boundary of the closed upper half-plane. -/
def ofReal (s : ℝ) : ClosedUpperHalfPlane := ⟨s, by simp⟩

@[simp]
theorem coe_ofReal (s : ℝ) : (ofReal s : ℂ) = s := by rw [ofReal]

/-- The imaginary coordinate of every point of the closed upper half-plane is nonnegative. -/
theorem im_nonneg (z : ClosedUpperHalfPlane) : 0 ≤ (z : ℂ).im := z.property

end ClosedUpperHalfPlane

/-- Inclusion of the closed upper half-plane into `ℂ`, with the retraction
`s + it ↦ s + i max(t,0)` as its model inverse. -/
def closedUpperHalfPlaneModel : ModelWithCorners ℝ ℂ ClosedUpperHalfPlane :=
  ModelWithCorners.ofConvexRange
    { toFun := Subtype.val
      invFun := fun z ↦ ⟨(z.re : ℂ) + ((max z.im 0 : ℝ) : ℂ) * I, by simp⟩
      source := univ
      target := {z | 0 ≤ z.im}
      map_source' := fun z _ ↦ z.property
      map_target' := fun _ _ ↦ mem_univ _
      left_inv' := by
        intro z _
        apply Subtype.ext
        simp only [max_eq_left z.property]
        exact Complex.re_add_im _
      right_inv' := by
        intro z hz
        simp only [Set.mem_ofPred_eq] at hz
        simp only [max_eq_left hz]
        exact Complex.re_add_im _ }
    rfl ((convex_Ici (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap)
    continuous_subtype_val (by
      -- The model constructor asks for continuity of a map into the subtype; this unfolds
      -- its bundled partial-equivalence inverse so `fun_prop` can see the clamped coordinate.
      change Continuous (fun z : ℂ ↦ (⟨(z.re : ℂ) + ((max z.im 0 : ℝ) : ℂ) * I,
        by simp⟩ : ClosedUpperHalfPlane))
      fun_prop)
    (by rw [Complex.interior_setOfPred_le_im]; exact ⟨I, by simp⟩)

@[simp, mfld_simps]
theorem closedUpperHalfPlaneModel_apply (z : ClosedUpperHalfPlane) :
    closedUpperHalfPlaneModel z = (z : ℂ) := by
  rw [closedUpperHalfPlaneModel]
  rfl

/-- The model inverse clamps the imaginary coordinate at zero. -/
theorem closedUpperHalfPlaneModel_symm_apply (z : ℂ) :
    (closedUpperHalfPlaneModel.symm z : ℂ) = (z.re : ℂ) + ((max z.im 0 : ℝ) : ℂ) * I := by
  rw [closedUpperHalfPlaneModel]
  rfl

@[simp]
theorem range_closedUpperHalfPlaneModel :
    range closedUpperHalfPlaneModel = {z : ℂ | 0 ≤ z.im} := by
  have h : (closedUpperHalfPlaneModel : ClosedUpperHalfPlane → ℂ) = Subtype.val :=
    funext closedUpperHalfPlaneModel_apply
  rw [h]
  exact Subtype.range_coe_subtype

/-- The manifold interior of the model consists exactly of points with positive imaginary part. -/
@[simp]
theorem closedUpperHalfPlaneModel_isInteriorPoint_iff (z : ClosedUpperHalfPlane) :
    closedUpperHalfPlaneModel.IsInteriorPoint z ↔ 0 < (z : ℂ).im := by
  simp [ModelWithCorners.IsInteriorPoint, mfld_simps]

/-- The manifold boundary of the model is the real axis. -/
@[simp]
theorem closedUpperHalfPlaneModel_isBoundaryPoint_iff (z : ClosedUpperHalfPlane) :
    closedUpperHalfPlaneModel.IsBoundaryPoint z ↔ (z : ℂ).im = 0 := by
  simp [ModelWithCorners.IsBoundaryPoint, mfld_simps]

/-- Real coordinates with the normal coordinate first: `s + it ↦ (t,s)`. -/
def closedUpperHalfPlaneCoordinates : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (Complex.orthonormalBasisOneI.repr.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1))).toContinuousLinearEquiv

/-- The native half-space's first coordinate is the imaginary part. -/
@[simp]
theorem closedUpperHalfPlaneCoordinates_apply_zero (z : ℂ) :
    closedUpperHalfPlaneCoordinates z 0 = z.im := by
  simp [closedUpperHalfPlaneCoordinates, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']

/-- The second native coordinate is the real part. -/
@[simp]
theorem closedUpperHalfPlaneCoordinates_apply_one (z : ℂ) :
    closedUpperHalfPlaneCoordinates z 1 = z.re := by
  simp [closedUpperHalfPlaneCoordinates, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']

/-- Convert real coordinates back to `s + it`. -/
@[simp]
theorem closedUpperHalfPlaneCoordinates_symm_apply (v : EuclideanSpace ℝ (Fin 2)) :
    closedUpperHalfPlaneCoordinates.symm v = v 1 + v 0 * I := by
  simp [closedUpperHalfPlaneCoordinates, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft']

/-- The closed upper half-plane is homeomorphic to Mathlib's native real two-dimensional
half-space, with the normal coordinate first. -/
def ClosedUpperHalfPlane.euclideanHalfSpaceHomeomorph :
    ClosedUpperHalfPlane ≃ₜ EuclideanHalfSpace 2 :=
  closedUpperHalfPlaneCoordinates.toHomeomorph.subtype (fun z ↦ by simp)

@[simp]
theorem ClosedUpperHalfPlane.coe_euclideanHalfSpaceHomeomorph (z : ClosedUpperHalfPlane) :
    (euclideanHalfSpaceHomeomorph z).1 =
      closedUpperHalfPlaneCoordinates z := by
  rw [euclideanHalfSpaceHomeomorph]
  rfl

@[simp]
theorem ClosedUpperHalfPlane.coe_euclideanHalfSpaceHomeomorph_symm (v : EuclideanHalfSpace 2) :
    (euclideanHalfSpaceHomeomorph.symm v : ℂ) = closedUpperHalfPlaneCoordinates.symm v.1 := by
  rw [euclideanHalfSpaceHomeomorph]
  rfl

/-- The native real coordinate comparison is `Cⁿ` up to the boundary for every regularity. -/
def ClosedUpperHalfPlane.euclideanHalfSpaceDiffeomorph (n : ℕ∞ω) :
    Diffeomorph closedUpperHalfPlaneModel (𝓡∂ 2) ClosedUpperHalfPlane
      (EuclideanHalfSpace 2) n where
  toEquiv := euclideanHalfSpaceHomeomorph.toEquiv
  contMDiff_toFun := by
    apply contMDiff_iff.mpr
    refine ⟨euclideanHalfSpaceHomeomorph.continuous, fun x y ↦ ?_⟩
    apply closedUpperHalfPlaneCoordinates.contDiff.contDiffOn.congr
    intro z hz
    simp only [mfld_simps, Function.comp_apply]
    -- The inherited half-space chart and subtype coercion reduce to their ambient model
    -- coordinates; `simp` has already exposed the chart composition, but cannot rewrite
    -- this dependent subtype expression to the public coefficient getter directly.
    change (euclideanHalfSpaceHomeomorph (closedUpperHalfPlaneModel.symm z)).1 =
      closedUpperHalfPlaneCoordinates z
    rw [coe_euclideanHalfSpaceHomeomorph]
    congr 1
    exact closedUpperHalfPlaneModel.right_inv (extChartAt_target_subset_range x hz.1)
  contMDiff_invFun := by
    apply contMDiff_iff.mpr
    refine ⟨euclideanHalfSpaceHomeomorph.symm.continuous, fun x y ↦ ?_⟩
    apply closedUpperHalfPlaneCoordinates.symm.contDiff.contDiffOn.congr
    intro v hv
    simp only [mfld_simps, Function.comp_apply]
    -- Likewise, reduce the self chart and inverse model coercions to the ambient complex
    -- coordinate of the subtype; the remaining equality uses only the public inverse getter.
    change (euclideanHalfSpaceHomeomorph.symm ((𝓡∂ 2).symm v) : ℂ) =
      closedUpperHalfPlaneCoordinates.symm v
    rw [coe_euclideanHalfSpaceHomeomorph_symm]
    congr 1
    exact (𝓡∂ 2).right_inv (extChartAt_target_subset_range x hv.1)

@[simp]
theorem ClosedUpperHalfPlane.coe_euclideanHalfSpaceDiffeomorph (n : ℕ∞ω)
    (z : ClosedUpperHalfPlane) :
    (euclideanHalfSpaceDiffeomorph n z).1 = closedUpperHalfPlaneCoordinates z := by
  rw [euclideanHalfSpaceDiffeomorph]
  exact coe_euclideanHalfSpaceHomeomorph z

@[simp]
theorem ClosedUpperHalfPlane.coe_euclideanHalfSpaceDiffeomorph_symm (n : ℕ∞ω)
    (v : EuclideanHalfSpace 2) :
    ((euclideanHalfSpaceDiffeomorph n).symm v : ℂ) = closedUpperHalfPlaneCoordinates.symm v.1 := by
  rw [euclideanHalfSpaceDiffeomorph]
  exact coe_euclideanHalfSpaceHomeomorph_symm v

/-- Smooth changes of closed-upper-half-plane charts preserve the manifold interior. -/
theorem ClosedUpperHalfPlane.im_pos_iff_of_mem_contDiffGroupoid {n : ℕ∞ω}
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (he : e ∈ contDiffGroupoid n closedUpperHalfPlaneModel) (hn : n ≠ 0)
    {z : ClosedUpperHalfPlane} (hz : z ∈ e.source) :
    0 < (z : ℂ).im ↔ 0 < (e z : ℂ).im := by
  simpa only [closedUpperHalfPlaneModel_isInteriorPoint_iff] using
    ModelWithCorners.isInteriorPoint_iff_of_mem_contDiffGroupoid he hn hz

/-- Smooth changes of closed-upper-half-plane charts send real boundary points to real boundary
points, in both directions. -/
theorem ClosedUpperHalfPlane.im_eq_zero_iff_of_mem_contDiffGroupoid {n : ℕ∞ω}
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (he : e ∈ contDiffGroupoid n closedUpperHalfPlaneModel) (hn : n ≠ 0)
    {z : ClosedUpperHalfPlane} (hz : z ∈ e.source) :
    (z : ℂ).im = 0 ↔ (e z : ℂ).im = 0 := by
  simpa only [closedUpperHalfPlaneModel_isBoundaryPoint_iff] using
    ModelWithCorners.isBoundaryPoint_iff_of_mem_contDiffGroupoid he hn hz

end TauCeti
