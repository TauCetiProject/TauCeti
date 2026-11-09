/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure

/-!
# The almost complex structure of a Riemann surface with boundary

A Riemann surface with boundary is a charted space `M` modelled on the closed upper half-plane
whose transition maps lie in `TauCeti.borderedHolomorphicGroupoid`. Its tangent spaces are `ℂ`,
and multiplication by `i` on them is a smooth almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofBorderedHolomorphic M`, smooth up to the boundary.

The point is that the real derivative of a member of the bordered holomorphic groupoid is complex
linear also at real boundary points
(`TauCeti.ClosedUpperHalfPlane.fderivWithin_I_smul_of_mem_borderedHolomorphicGroupoid`). At points
of positive imaginary part the member is complex differentiable. Since the member is smooth up to
the boundary, its derivative within the closed upper half-plane is continuous there, and a boundary
point is a limit of points of positive imaginary part; commuting with multiplication by `i` is a
closed condition. Consequently the tangent coordinate changes of `M` are complex linear
(`TauCeti.ClosedUpperHalfPlane.tangentCoordChange_I_smul`), and in the tangent coordinates of every
chart the structure is multiplication by `i` again
(`TauCeti.SmoothAlmostComplexStructure.inTangentCoordinates_ofBorderedHolomorphic`).

On the closed upper half-plane itself, the inclusion into `ℂ` is pseudoholomorphic from this
structure to the almost complex structure of `ℂ` as a complex manifold
(`TauCeti.SmoothAlmostComplexStructure.isPseudoholomorphic_coe_ofBorderedHolomorphic`), so the
induced structure is the standard one.

## Main declarations

* `TauCeti.SmoothAlmostComplexStructure.ofBorderedHolomorphic`: the induced almost complex
  structure of a Riemann surface with boundary.
* `TauCeti.SmoothAlmostComplexStructure.ofBorderedHolomorphic_apply`: it is multiplication by `i`
  on every tangent space.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 2.4.
-/

public section

open Bundle Set Complex Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti

namespace ClosedUpperHalfPlane

/-- The real derivative, within the closed upper half-plane, of a member of the bordered
holomorphic groupoid commutes with multiplication by `i` at every point of its source, including
the real boundary points. -/
theorem fderivWithin_I_smul_of_mem_borderedHolomorphicGroupoid
    {e : OpenPartialHomeomorph ClosedUpperHalfPlane ClosedUpperHalfPlane}
    (he : e ∈ borderedHolomorphicGroupoid) {z : ℂ}
    (hz : z ∈ closedUpperHalfPlaneModel.symm ⁻¹' e.source ∩ range closedUpperHalfPlaneModel)
    (v : ℂ) :
    fderivWithin ℝ (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm)
        (range closedUpperHalfPlaneModel) z (I • v) =
      I • fderivWithin ℝ (closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm)
        (range closedUpperHalfPlaneModel) z v := by
  set f := closedUpperHalfPlaneModel ∘ e ∘ closedUpperHalfPlaneModel.symm
  set U := closedUpperHalfPlaneModel.symm ⁻¹' e.source
  set S := U ∩ range closedUpperHalfPlaneModel
  have hU : IsOpen U := e.open_source.preimage closedUpperHalfPlaneModel.continuous_symm
  obtain ⟨⟨hc, -⟩, hd, -⟩ := mem_borderedHolomorphicGroupoid_iff.1 he
  have hcd : ContDiffOn ℝ ∞ f S := hc
  have hS : UniqueDiffOn ℝ S := closedUpperHalfPlaneModel.uniqueDiffOn_preimage e.open_source
  -- The maps commuting with multiplication by `i` form a closed set.
  let P : Set (ℂ →L[ℝ] ℂ) := {L | ∀ w, L (I • w) = I • L w}
  have hP : IsClosed P := by
    simp only [P, ofPred_forall]
    exact isClosed_iInter fun w ↦
      isClosed_eq (by fun_prop) (by fun_prop)
  -- At points of positive imaginary part, the derivative is complex linear.
  have hint : fderivWithin ℝ f S '' (U ∩ {w | 0 < w.im}) ⊆ P := by
    rintro _ ⟨w, hw, rfl⟩ u
    have hopen : IsOpen (U ∩ {w : ℂ | 0 < w.im}) :=
      hU.inter (isOpen_lt continuous_const continuous_im)
    have hSw : S ∈ 𝓝 w := mem_of_superset (hopen.mem_nhds hw) fun y hy ↦
      ⟨hy.1, by simpa using le_of_lt hy.2⟩
    have hdw : DifferentiableAt ℂ f w := hd.differentiableAt (hopen.mem_nhds hw)
    rw [fderivWithin_of_mem_nhds hSw, hdw.fderiv_restrictScalars ℝ,
      ContinuousLinearMap.coe_restrictScalars', map_smul]
  -- Every point of the source is a limit of points of positive imaginary part.
  have hcl : z ∈ closure (U ∩ {w | 0 < w.im}) :=
    hU.inter_closure ⟨hz.1, by simpa using hz.2⟩
  have hcont : ContinuousWithinAt (fderivWithin ℝ f S) (U ∩ {w | 0 < w.im}) z :=
    ((hcd.continuousOn_fderivWithin hS (by simp)) z hz).mono fun y hy ↦
      ⟨hy.1, by simpa using le_of_lt hy.2⟩
  have hmem : fderivWithin ℝ f S z ∈ P :=
    hP.closure_subset_iff.2 hint (hcont.mem_closure_image hcl)
  have hfd : fderivWithin ℝ f (range closedUpperHalfPlaneModel) z = fderivWithin ℝ f S z := by
    rw [show S = range closedUpperHalfPlaneModel ∩ U from inter_comm _ _,
      fderivWithin_inter (hU.mem_nhds hz.1)]
  rw [hfd]
  exact hmem v

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid]

/-- On a Riemann surface with boundary, the tangent coordinate changes are complex linear, also
at boundary points. -/
theorem tangentCoordChange_I_smul {x y z : M}
    (h : z ∈ (chartAt ClosedUpperHalfPlane x).source ∩ (chartAt ClosedUpperHalfPlane y).source)
    (v : ℂ) :
    tangentCoordChange closedUpperHalfPlaneModel x y z (I • v) =
      I • tangentCoordChange closedUpperHalfPlaneModel x y z v := by
  have he : (chartAt ClosedUpperHalfPlane x).symm.trans (chartAt ClosedUpperHalfPlane y) ∈
      borderedHolomorphicGroupoid :=
    HasGroupoid.compatible (chart_mem_atlas _ x) (chart_mem_atlas _ y)
  have hz : extChartAt closedUpperHalfPlaneModel x z ∈
      closedUpperHalfPlaneModel.symm ⁻¹'
          ((chartAt ClosedUpperHalfPlane x).symm.trans (chartAt ClosedUpperHalfPlane y)).source ∩
        range closedUpperHalfPlaneModel := by
    refine ⟨?_, mem_range_self _⟩
    simp only [mem_preimage, extChartAt, OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      ModelWithCorners.left_inv, OpenPartialHomeomorph.trans_source, mem_inter_iff,
      OpenPartialHomeomorph.symm_source]
    exact ⟨(chartAt _ x).map_source h.1, by simpa [(chartAt _ x).left_inv h.1] using h.2⟩
  exact fderivWithin_I_smul_of_mem_borderedHolomorphicGroupoid he hz v

end ClosedUpperHalfPlane

namespace SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid]

/-- In the tangent coordinates of the chart at `x₀`, multiplication by `i` on the tangent spaces
of a Riemann surface with boundary is multiplication by `i`, on the whole chart domain. -/
private theorem inTangentCoordinates_I_smul_id {x₀ x : M}
    (hx : x ∈ (chartAt ClosedUpperHalfPlane x₀).source) :
    inTangentCoordinates closedUpperHalfPlaneModel closedUpperHalfPlaneModel id id
        (fun x : M ↦ (I • ContinuousLinearMap.id ℝ ℂ :
          TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace closedUpperHalfPlaneModel x))
        x₀ x =
      I • ContinuousLinearMap.id ℝ ℂ := by
  refine (inTangentCoordinates_eq (I := closedUpperHalfPlaneModel)
    (I' := closedUpperHalfPlaneModel) id id _ hx hx).trans
    (ContinuousLinearMap.ext fun v ↦ ?_)
  have hx' : x ∈ (extChartAt closedUpperHalfPlaneModel x₀).source ∩
      (extChartAt closedUpperHalfPlaneModel x).source ∩
        (extChartAt closedUpperHalfPlaneModel x₀).source := by
    simp [hx]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
  exact (ClosedUpperHalfPlane.tangentCoordChange_I_smul ⟨mem_chart_source _ x, hx⟩ _).trans
    (congrArg (I • ·)
      ((tangentCoordChange_comp hx').trans (tangentCoordChange_self (by simp [hx]))))

variable (M) in
/-- The almost complex structure induced on a Riemann surface with boundary: multiplication by `i`
on every tangent space, which is `ℂ`. It is smooth up to the boundary because the tangent
coordinate changes are complex linear. -/
def ofBorderedHolomorphic : SmoothAlmostComplexStructure closedUpperHalfPlaneModel M where
  toEndomorphism :=
    ⟨fun _ ↦ I • ContinuousLinearMap.id ℝ ℂ, fun x₀ ↦ by
      rw [contMDiffAt_hom_bundle]
      refine ⟨contMDiffAt_id, (contMDiffAt_const (c := I • ContinuousLinearMap.id ℝ ℂ))
        |>.congr_of_eventuallyEq ?_⟩
      filter_upwards [(chartAt ClosedUpperHalfPlane x₀).open_source.mem_nhds
        (mem_chart_source ClosedUpperHalfPlane x₀)] with x hx
      exact inTangentCoordinates_I_smul_id hx⟩
  square_neg x := ContinuousLinearMap.ext fun v ↦ by
    simp only [ContinuousLinearMap.comp_apply]
    -- The tangent space at `x` is `ℂ`, where `I • I • w = -w`.
    have h (w : ℂ) : I • I • w = -w := by
      rw [smul_smul, I_mul_I, neg_one_smul]
    exact h v

/-- The induced almost complex structure of a Riemann surface with boundary is multiplication by
`i` on every tangent space. -/
@[simp]
theorem ofBorderedHolomorphic_apply (x : M) (v : ℂ) : ofBorderedHolomorphic M x v = I • v :=
  (rfl)

/-- The induced almost complex structure of a Riemann surface with boundary is multiplication by
`i` on every tangent space, as an endomorphism. -/
theorem toEndomorphism_ofBorderedHolomorphic (x : M) :
    (ofBorderedHolomorphic M).toEndomorphism x =
      (I • ContinuousLinearMap.id ℝ ℂ :
        TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace closedUpperHalfPlaneModel x) :=
  ContinuousLinearMap.ext fun v ↦ ofBorderedHolomorphic_apply x v

/-- In the tangent coordinates of the chart at any point `x₀`, the induced almost complex
structure of a Riemann surface with boundary is multiplication by `i` on the whole chart domain,
boundary points included. -/
theorem inTangentCoordinates_ofBorderedHolomorphic {x₀ x : M}
    (hx : x ∈ (chartAt ClosedUpperHalfPlane x₀).source) :
    inTangentCoordinates closedUpperHalfPlaneModel closedUpperHalfPlaneModel id id
        (fun x ↦ (ofBorderedHolomorphic M).toEndomorphism x) x₀ x =
      I • ContinuousLinearMap.id ℝ ℂ :=
  inTangentCoordinates_I_smul_id hx

/-! ### Check: the closed upper half-plane -/

/-- On the closed upper half-plane, the inclusion into `ℂ` is pseudoholomorphic from the induced
almost complex structure to the almost complex structure of `ℂ` as a complex manifold, at boundary
points as well as interior points. -/
theorem isPseudoholomorphic_coe_ofBorderedHolomorphic :
    IsPseudoholomorphic (ofBorderedHolomorphic ClosedUpperHalfPlane) (ofComplexManifold ℂ ℂ)
      ((↑) : ClosedUpperHalfPlane → ℂ) := by
  refine isPseudoholomorphic_iff.2 fun z ↦ ?_
  refine isPseudoholomorphicAt_of_hasMFDerivAt (u' := ContinuousLinearMap.id ℝ ℂ)
    ⟨continuous_subtype_val.continuousAt, ?_⟩ fun w ↦
      (ofBorderedHolomorphic_apply z w).trans (ofComplexManifold_apply (E := ℂ) (z : ℂ) w).symm
  -- In the self charts, the inclusion reads as the identity on the closed upper half-plane.
  refine (hasFDerivWithinAt_id (𝕜 := ℝ) _ _).congr (fun w hw ↦ ?_) ?_
  · simp only [mfld_simps, writtenInExtChartAt, Function.comp_apply]
    exact coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (by simpa using hw)
  · simp [writtenInExtChartAt]

end SmoothAlmostComplexStructure

end TauCeti
