/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Analysis.Complex.ReImTopology
public import TauCeti.Geometry.Manifold.Boundary.Basic
public import TauCeti.Geometry.Manifold.Boundary.Model
public import TauCeti.Analysis.Convex.Cone.StrictInward
public import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph

/-!
# The closed upper half-plane as a model with corners

`ClosedUpperHalfPlane` is the subtype of complex numbers with nonnegative imaginary part.
`closedUpperHalfPlaneModel` is its real model with corners in `ℂ`. Its manifold interior is the
open upper half-plane, and its manifold boundary is the real axis. The inverse of the model
retracts the lower half-plane onto the real axis; it is only a model inverse on the model range.

`ClosedUpperHalfPlane.upperHalfPlaneChart` is the inclusion of the open upper half-plane into `ℂ`,
as an open partial homeomorphism. A chart change that is `C^n` up to the boundary, read in `ℂ`
through it, is `C^n`; see
`ClosedUpperHalfPlane.upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid_of_mem_contDiffGroupoid`.

The real coordinate comparison uses `(Im z, Re z)`: Mathlib's `EuclideanHalfSpace 2` requires
its *first* coordinate to be nonnegative. Thus the normal coordinate precedes the tangential one,
whereas complex coordinates conventionally write `z = s + it`. The comparison is a smooth
real diffeomorphism up to the boundary. Smooth chart changes preserve the real boundary, by
Mathlib's invariance of the manifold interior under local diffeomorphisms. Reading the charts of a
`C^n` manifold modelled on the closed upper half-plane through the comparison makes it a `C^n`
manifold modelled on `𝓡∂ 2` (`ClosedUpperHalfPlane.isManifold_euclideanHalfSpace`).

The fold `ClosedUpperHalfPlane.fold` sends `z` to `re z + |im z| i`; it identifies `z` with
`conj z` and agrees with the model inverse on the closed upper half-plane. An open partial
homeomorphism of the closed upper half-plane satisfies `ClosedUpperHalfPlane.PreservesRealAxis`
when it sends real points, and only those, to real points; smooth chart changes do so.
The explicit constructor `ClosedUpperHalfPlane.euclideanHalfSpaceChartedSpace` transports any
bordered atlas to the native real half-space model. Its preferred chart law fixes the chosen
structure for boundary constructions. The strict inward cone at the real axis has positive
imaginary component; the native boundary parametrization has range `Complex.imCLM.ker`.

-/

public section

noncomputable section

open Set Complex
open scoped Manifold ContDiff Topology ComplexConjugate

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
    continuous_subtypeVal (by
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

/-- At a point of nonnegative imaginary part, the model inverse is the inverse of the inclusion. -/
theorem coe_closedUpperHalfPlaneModel_symm_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) :
    (closedUpperHalfPlaneModel.symm z : ℂ) = z := by
  rw [closedUpperHalfPlaneModel_symm_apply, max_eq_left hz, re_add_im]

/-- The model inverse is a left inverse of the inclusion. -/
@[simp]
theorem closedUpperHalfPlaneModel_symm_coe (z : ClosedUpperHalfPlane) :
    closedUpperHalfPlaneModel.symm (z : ℂ) = z :=
  Subtype.ext (coe_closedUpperHalfPlaneModel_symm_of_im_nonneg z.property)

/-- Near a point of positive imaginary part, the model inverse is the inverse of the inclusion. -/
theorem eventually_coe_closedUpperHalfPlaneModel_symm {z : ℂ} (hz : 0 < z.im) :
    ∀ᶠ w in 𝓝 z, (closedUpperHalfPlaneModel.symm w : ℂ) = w :=
  Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_im).mem_nhds hz) fun _ hw ↦
    coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (le_of_lt hw)

@[simp]
theorem range_closedUpperHalfPlaneModel :
    range closedUpperHalfPlaneModel = {z : ℂ | 0 ≤ z.im} := by
  have h : (closedUpperHalfPlaneModel : ClosedUpperHalfPlane → ℂ) = Subtype.val :=
    funext closedUpperHalfPlaneModel_apply
  rw [h]
  exact Subtype.range_coe_subtype

/-- The part of the extended target of a chart into the closed upper half-plane lying over an
open set is relatively open in the closed upper half-plane: it is `Ω ∩ {z | 0 ≤ z.im}` for an
open `Ω ⊆ ℂ`. -/
theorem _root_.OpenPartialHomeomorph.exists_isOpen_extend_target_inter_preimage {X : Type*}
    [TopologicalSpace X] (φ : OpenPartialHomeomorph X ClosedUpperHalfPlane) {W : Set X}
    (hW : IsOpen W) :
    ∃ Ω : Set ℂ, IsOpen Ω ∧ (φ.extend closedUpperHalfPlaneModel).target ∩
      (φ.extend closedUpperHalfPlaneModel).symm ⁻¹' W = Ω ∩ {z | 0 ≤ z.im} := by
  have hcont : ContinuousOn (φ.symm ∘ closedUpperHalfPlaneModel.symm)
      (closedUpperHalfPlaneModel.symm ⁻¹' φ.target) :=
    φ.continuousOn_symm.comp closedUpperHalfPlaneModel.continuous_symm.continuousOn
      fun _ hz ↦ hz
  refine ⟨_, hcont.isOpen_inter_preimage
    (φ.open_target.preimage closedUpperHalfPlaneModel.continuous_symm) hW, ?_⟩
  ext z
  simp only [OpenPartialHomeomorph.extend_target, OpenPartialHomeomorph.extend_coe_symm,
    range_closedUpperHalfPlaneModel, mem_inter_iff, mem_preimage, mem_ofPred_eq]
  tauto

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

namespace ClosedUpperHalfPlane

/-- The inclusion of the open upper half-plane into `ℂ`, as an open partial homeomorphism from the
closed upper half-plane. Its source is the set of points of positive imaginary part, and its
inverse is the model inverse `closedUpperHalfPlaneModel.symm`. -/
def upperHalfPlaneChart : OpenPartialHomeomorph ClosedUpperHalfPlane ℂ where
  toFun := Subtype.val
  invFun := closedUpperHalfPlaneModel.symm
  source := {z | 0 < (z : ℂ).im}
  target := {z | 0 < z.im}
  map_source' {_} hz := hz
  map_target' {z} hz := by
    simpa only [mem_ofPred_eq, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (le_of_lt hz)]
      using hz
  left_inv' z _ := closedUpperHalfPlaneModel_symm_coe z
  right_inv' _ hz := coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (le_of_lt hz)
  open_source := isOpen_lt continuous_const (continuous_im.comp continuous_subtypeVal)
  open_target := isOpen_lt continuous_const continuous_im
  continuousOn_toFun := continuous_subtypeVal.continuousOn
  continuousOn_invFun := closedUpperHalfPlaneModel.continuous_symm.continuousOn

/-- `upperHalfPlaneChart` is the inclusion into `ℂ`. -/
@[simp, mfld_simps]
theorem upperHalfPlaneChart_apply (z : ClosedUpperHalfPlane) : upperHalfPlaneChart z = z :=
  (rfl)

/-- The inverse of `upperHalfPlaneChart` is the model inverse. -/
@[simp, mfld_simps]
theorem upperHalfPlaneChart_symm_apply (z : ℂ) :
    upperHalfPlaneChart.symm z = closedUpperHalfPlaneModel.symm z :=
  (rfl)

/-- `upperHalfPlaneChart` is defined at the points of positive imaginary part. -/
@[simp, mfld_simps]
theorem upperHalfPlaneChart_source :
    upperHalfPlaneChart.source = {z : ClosedUpperHalfPlane | 0 < (z : ℂ).im} :=
  (rfl)

/-- `upperHalfPlaneChart` takes values in the open upper half-plane. -/
@[simp, mfld_simps]
theorem upperHalfPlaneChart_target : upperHalfPlaneChart.target = {z : ℂ | 0 < z.im} :=
  (rfl)

/-- A chart change of the closed upper half-plane, read in `ℂ` through the open upper half-plane,
is in `contDiffGroupoid n 𝓘(𝕜, ℂ)` when it and its inverse, so read, are `C^n` over `𝕜` on their
sources. -/
theorem upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid_of_contDiffOn
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 ℂ] {n : ℕ∞ω}
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (h : ContDiffOn 𝕜 n (upperHalfPlaneChart.symm ≫ₕ e ≫ₕ upperHalfPlaneChart)
      (upperHalfPlaneChart.symm ≫ₕ e ≫ₕ upperHalfPlaneChart).source)
    (h_symm : ContDiffOn 𝕜 n (upperHalfPlaneChart.symm ≫ₕ e.symm ≫ₕ upperHalfPlaneChart)
      (upperHalfPlaneChart.symm ≫ₕ e.symm ≫ₕ upperHalfPlaneChart).source) :
    upperHalfPlaneChart.symm ≫ₕ e ≫ₕ upperHalfPlaneChart ∈ contDiffGroupoid n 𝓘(𝕜, ℂ) := by
  have hsymm : (upperHalfPlaneChart.symm ≫ₕ e ≫ₕ upperHalfPlaneChart).symm =
      upperHalfPlaneChart.symm ≫ₕ e.symm ≫ₕ upperHalfPlaneChart := by
    simp only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, hsymm]
  constructor
  · simpa [contDiffPregroupoid, inter_assoc] using h
  · simpa [contDiffPregroupoid, inter_assoc] using h_symm

/-- A chart change of the closed upper half-plane that is `C^n` up to the boundary, read in `ℂ`
through the open upper half-plane, is `C^n`. -/
theorem upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid_of_mem_contDiffGroupoid {n : ℕ∞ω}
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (he : e ∈ contDiffGroupoid n closedUpperHalfPlaneModel) :
    upperHalfPlaneChart.symm ≫ₕ e ≫ₕ upperHalfPlaneChart ∈ contDiffGroupoid n 𝓘(ℝ, ℂ) := by
  have hconj : ∀ {f : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane},
      f ∈ contDiffGroupoid n closedUpperHalfPlaneModel →
        ContDiffOn ℝ n (upperHalfPlaneChart.symm ≫ₕ f ≫ₕ upperHalfPlaneChart)
          (upperHalfPlaneChart.symm ≫ₕ f ≫ₕ upperHalfPlaneChart).source := by
    intro f hf
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hf
    refine (hf.1.mono fun z hz ↦ ?_).congr fun z _ ↦ ?_
    · simp only [mfld_simps] at hz
      exact ⟨hz.2.1, by simpa using le_of_lt hz.1⟩
    · simp
  exact upperHalfPlaneChart_symm_trans_mem_contDiffGroupoid_of_contDiffOn (hconj he)
    (hconj ((contDiffGroupoid _ _).symm he))

end ClosedUpperHalfPlane

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
    (euclideanHalfSpaceHomeomorph z).val =
      closedUpperHalfPlaneCoordinates z := by
  rw [euclideanHalfSpaceHomeomorph]
  rfl

@[simp]
theorem ClosedUpperHalfPlane.coe_euclideanHalfSpaceHomeomorph_symm (v : EuclideanHalfSpace 2) :
    (euclideanHalfSpaceHomeomorph.symm v : ℂ) = closedUpperHalfPlaneCoordinates.symm v.val := by
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
    change (euclideanHalfSpaceHomeomorph (closedUpperHalfPlaneModel.symm z)).val =
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
    (euclideanHalfSpaceDiffeomorph n z).val = closedUpperHalfPlaneCoordinates z := by
  rw [euclideanHalfSpaceDiffeomorph]
  exact coe_euclideanHalfSpaceHomeomorph z

@[simp]
theorem ClosedUpperHalfPlane.coe_euclideanHalfSpaceDiffeomorph_symm (n : ℕ∞ω)
    (v : EuclideanHalfSpace 2) :
    ((euclideanHalfSpaceDiffeomorph n).symm v : ℂ) = closedUpperHalfPlaneCoordinates.symm v.val
        := by
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

/-- At a boundary point, the strict inward cone of the closed upper half-plane consists
of the vectors with positive imaginary part. -/
theorem mem_strictInwardCone_closedUpperHalfPlaneModel_iff (z v : ℂ) (hz : z.im = 0) :
    v ∈ strictInwardCone (range closedUpperHalfPlaneModel) z ↔ 0 < v.im := by
  rw [closedUpperHalfPlaneModel.convex_range.mem_strictInwardCone_iff
    (by simp [range_closedUpperHalfPlaneModel, hz])]
  rw [range_closedUpperHalfPlaneModel, Complex.interior_setOfPred_le_im]
  simp only [mem_ofPred_eq, add_im, real_smul, mul_im, ofReal_re, ofReal_im,
    zero_mul, add_zero, hz, zero_add]
  constructor
  · rintro ⟨t, ht, hv⟩
    exact (mul_pos_iff_of_pos_left ht).1 hv
  · intro hv
    exact ⟨1, one_pos, by simpa using hv⟩

/-- The native one-dimensional boundary parametrization reads as the real axis in complex
coordinates. -/
theorem closedUpperHalfPlaneCoordinates_symm_boundaryParam
    (u : EuclideanSpace ℝ (Fin 1)) :
    closedUpperHalfPlaneCoordinates.symm (euclideanHalfSpaceBoundaryParam 1 u) = (u 0 : ℂ) := by
  rw [closedUpperHalfPlaneCoordinates_symm_apply, euclideanHalfSpaceBoundaryParam_apply_zero]
  simp only [ofReal_zero, zero_mul, add_zero]
  exact congrArg (fun t : ℝ ↦ (t : ℂ))
    (euclideanHalfSpaceBoundaryParam_apply_succ u (0 : Fin 1))

/-- The native real boundary parametrization in complex coordinates has real-axis range. -/
theorem range_closedUpperHalfPlaneCoordinates_symm_boundaryParam :
    LinearMap.range (closedUpperHalfPlaneCoordinates.symm.toLinearMap.comp
      (euclideanHalfSpaceBoundaryParam 1).toLinearMap) = Complex.imCLM.ker := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    -- Evaluate the linear-map composite and the kernel condition on this boundary vector.
    change (closedUpperHalfPlaneCoordinates.symm (euclideanHalfSpaceBoundaryParam 1 u)).im = 0
    rw [closedUpperHalfPlaneCoordinates_symm_boundaryParam]
    simp
  · intro hz
    have hz' : z.im = 0 := by
      simpa only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, Complex.imCLM_apply] using hz
    refine ⟨WithLp.toLp 2 (fun _ : Fin 1 ↦ z.re), ?_⟩
    -- Evaluate the composite on the chosen real-coordinate preimage.
    change closedUpperHalfPlaneCoordinates.symm
      (euclideanHalfSpaceBoundaryParam 1 (WithLp.toLp 2 (fun _ : Fin 1 ↦ z.re))) = z
    rw [closedUpperHalfPlaneCoordinates_symm_boundaryParam]
    exact Complex.ext rfl (by simpa using hz'.symm)

/-- The native coordinate comparison, as a homeomorphism, is the underlying homeomorphism of the
diffeomorphism `ClosedUpperHalfPlane.euclideanHalfSpaceDiffeomorph n`. -/
theorem ClosedUpperHalfPlane.toHomeomorph_euclideanHalfSpaceDiffeomorph (n : ℕ∞ω) :
    (euclideanHalfSpaceDiffeomorph n).toHomeomorph = euclideanHalfSpaceHomeomorph :=
  Homeomorph.ext fun z ↦ Subtype.ext (by simp)

/-- The canonical native half-space charts of a closed-upper-half-plane charted space.
The original charts are followed by the existing real coordinate homeomorphism
(`Homeomorph.chartedSpaceComp`). This is an explicitly chosen charted-space structure, rather
than a global instance on every `M`. -/
@[instance_reducible]
def ClosedUpperHalfPlane.euclideanHalfSpaceChartedSpace (M : Type*)
    [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M] :
    ChartedSpace (EuclideanHalfSpace (1 + 1)) M :=
  euclideanHalfSpaceHomeomorph.chartedSpaceComp M

/-- The preferred chart of the native half-space transfer is the original chart followed by
the existing real coordinate homeomorphism. -/
theorem ClosedUpperHalfPlane.chartAt_euclideanHalfSpace (M : Type*)
    [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M] (x : M) :
    letI := euclideanHalfSpaceChartedSpace M
    chartAt (EuclideanHalfSpace (1 + 1)) x =
      (chartAt ClosedUpperHalfPlane x).trans
        euclideanHalfSpaceHomeomorph.toOpenPartialHomeomorph :=
  euclideanHalfSpaceHomeomorph.chartAt_chartedSpaceComp x

/-- Evaluation of the preferred chart in the native half-space transfer. -/
@[simp]
theorem ClosedUpperHalfPlane.chartAt_euclideanHalfSpace_apply (M : Type*)
    [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M] (x y : M) :
    letI := euclideanHalfSpaceChartedSpace M
    chartAt (EuclideanHalfSpace (1 + 1)) x y =
      euclideanHalfSpaceHomeomorph (chartAt ClosedUpperHalfPlane x y) := by
  rw [chartAt_euclideanHalfSpace]
  rfl

/-- The inverse preferred chart undoes the half-space coordinate homeomorphism first. -/
@[simp]
theorem ClosedUpperHalfPlane.chartAt_euclideanHalfSpace_symm_apply (M : Type*)
    [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M] (x : M)
    (v : EuclideanHalfSpace (1 + 1)) :
    letI := euclideanHalfSpaceChartedSpace M
    (chartAt (EuclideanHalfSpace (1 + 1)) x).symm v =
      (chartAt ClosedUpperHalfPlane x).symm (euclideanHalfSpaceHomeomorph.symm v) := by
  rw [chartAt_euclideanHalfSpace]
  rfl

/-- Membership in the transferred chart target is membership after undoing the coordinate
homeomorphism, which is defined on the whole half-space. -/
@[simp]
theorem ClosedUpperHalfPlane.mem_chartAt_euclideanHalfSpace_target (M : Type*)
    [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M] (x : M)
    (v : EuclideanHalfSpace (1 + 1)) :
    letI := euclideanHalfSpaceChartedSpace M
    v ∈ (chartAt (EuclideanHalfSpace (1 + 1)) x).target ↔
      euclideanHalfSpaceHomeomorph.symm v ∈ (chartAt ClosedUpperHalfPlane x).target := by
  rw [chartAt_euclideanHalfSpace]
  simp

/-- A `C^n` manifold modelled on the closed upper half-plane is a `C^n` manifold modelled on
`𝓡∂ 2`, for its charts read in the native half-space coordinates `s + it ↦ (t, s)`. -/
theorem ClosedUpperHalfPlane.isManifold_euclideanHalfSpace {n : ℕ∞ω} (M : Type*)
    [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
    [IsManifold closedUpperHalfPlaneModel n M] :
    letI := euclideanHalfSpaceChartedSpace M
    IsManifold (𝓡∂ (1 + 1)) n M := by
  have h := (euclideanHalfSpaceDiffeomorph n).isManifold_chartedSpaceComp M
  rwa [toHomeomorph_euclideanHalfSpaceDiffeomorph] at h

namespace ClosedUpperHalfPlane

/-! ### The fold of the plane onto the closed upper half-plane -/

/-- The fold `z ↦ re z + |im z| i` of the plane onto the closed upper half-plane. It identifies
`z` with `conj z` and is the identity on the closed upper half-plane. -/
def fold (z : ℂ) : ClosedUpperHalfPlane :=
  ⟨(z.re : ℂ) + (|z.im| : ℝ) * I, by simp⟩

theorem coe_fold (z : ℂ) : (fold z : ℂ) = (z.re : ℂ) + (|z.im| : ℝ) * I :=
  (rfl)

@[simp]
theorem re_fold (z : ℂ) : (fold z : ℂ).re = z.re := by
  simp [coe_fold]

@[simp]
theorem im_fold (z : ℂ) : (fold z : ℂ).im = |z.im| := by
  simp [coe_fold]

theorem continuous_fold : Continuous fold :=
  Continuous.subtype_mk (by fun_prop) _

@[simp]
theorem fold_conj (z : ℂ) : fold (conj z) = fold z :=
  Subtype.ext (Complex.ext (by simp) (by simp))

@[simp]
theorem fold_coe (z : ClosedUpperHalfPlane) : fold z = z :=
  Subtype.ext (Complex.ext (by simp) (by simp [abs_of_nonneg z.property]))

theorem coe_fold_of_im_nonneg {z : ℂ} (hz : 0 ≤ z.im) : (fold z : ℂ) = z :=
  congrArg Subtype.val (fold_coe ⟨z, hz⟩)

theorem coe_fold_of_im_nonpos {z : ℂ} (hz : z.im ≤ 0) : (fold z : ℂ) = conj z := by
  rw [← fold_conj, coe_fold_of_im_nonneg (by simpa using hz)]

/-- On the closed upper half-plane, the model inverse is the fold. -/
theorem closedUpperHalfPlaneModel_symm_eq_fold {z : ℂ} (hz : 0 ≤ z.im) :
    closedUpperHalfPlaneModel.symm z = fold z :=
  Subtype.ext ((coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz).trans
    (coe_fold_of_im_nonneg hz).symm)

/-! ### Chart changes that preserve the real axis -/

/-- An open partial homeomorphism of the closed upper half-plane preserves the real axis if it
sends a point of its source to the real axis exactly when the point is real. Members of
`contDiffGroupoid n closedUpperHalfPlaneModel` with `n ≠ 0` do so
(`ClosedUpperHalfPlane.preservesRealAxis_of_mem_contDiffGroupoid`). -/
def PreservesRealAxis (e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane) :
    Prop :=
  ∀ z ∈ e.source, (z : ℂ).im = 0 ↔ (e z : ℂ).im = 0

variable {e e' : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}

theorem preservesRealAxis_iff :
    PreservesRealAxis e ↔ ∀ z ∈ e.source, (z : ℂ).im = 0 ↔ (e z : ℂ).im = 0 :=
  Iff.rfl

theorem preservesRealAxis_of_mem_contDiffGroupoid {n : ℕ∞ω}
    (he : e ∈ contDiffGroupoid n closedUpperHalfPlaneModel) (hn : n ≠ 0) :
    PreservesRealAxis e := fun _ hz ↦ im_eq_zero_iff_of_mem_contDiffGroupoid he hn hz


namespace PreservesRealAxis

/-- A chart change preserving the real axis sends a point of its source to the real axis exactly
when the point is real. -/
theorem im_eq_zero_iff (he : PreservesRealAxis e) {z : ClosedUpperHalfPlane}
    (hz : z ∈ e.source) : (z : ℂ).im = 0 ↔ (e z : ℂ).im = 0 :=
  he z hz

/-- A chart change preserving the real axis sends points of positive imaginary part, and only
those, to points of positive imaginary part. -/
theorem im_pos_iff (he : PreservesRealAxis e) {z : ClosedUpperHalfPlane} (hz : z ∈ e.source) :
    0 < (z : ℂ).im ↔ 0 < (e z : ℂ).im := by
  rw [(z.property).lt_iff_ne', (e z).property.lt_iff_ne', Ne, Ne, he z hz]

protected theorem symm (he : PreservesRealAxis e) : PreservesRealAxis e.symm := fun w hw ↦ by
  simpa [e.right_inv hw] using (he _ (e.map_target hw)).symm

protected theorem trans (he : PreservesRealAxis e) (he' : PreservesRealAxis e') :
    PreservesRealAxis (e.trans e') := fun _ hz ↦ (he _ hz.1).trans (he' _ hz.2)

end PreservesRealAxis

theorem preservesRealAxis_refl :
    PreservesRealAxis (OpenPartialHomeomorph.refl ClosedUpperHalfPlane) := fun _ _ ↦ Iff.rfl

end ClosedUpperHalfPlane

end TauCeti
