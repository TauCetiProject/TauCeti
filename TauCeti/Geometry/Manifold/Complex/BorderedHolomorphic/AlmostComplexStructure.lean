/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
import TauCeti.Geometry.Manifold.Diffeomorph.MaximalAtlas

/-!
# The almost complex structure of a Riemann surface with boundary

A Riemann surface with boundary is a charted space `M` modelled on the closed upper half-plane
whose transition maps lie in `TauCeti.borderedHolomorphicGroupoid`. Its tangent spaces are `ℂ`,
and multiplication by `i` on them is a smooth almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofBorderedHolomorphic M`, smooth up to the boundary.

The point, proved in `TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Basic`, is that the
real derivative of a member of the bordered holomorphic groupoid is complex linear also at real
boundary points
(`TauCeti.ClosedUpperHalfPlane.fderivWithin_apply_smul_of_mem_borderedHolomorphicGroupoid`). At
points of positive imaginary part the member is complex differentiable. Since the member is smooth
up to the boundary, its derivative within the closed upper half-plane is continuous there, and a
boundary point is a limit of points of positive imaginary part; commuting with multiplication by a
complex scalar is a closed condition. Consequently the tangent coordinate changes of `M` are
complex linear (`TauCeti.ClosedUpperHalfPlane.tangentCoordChange_smul`), so the structure is an
instance of `TauCeti.SmoothAlmostComplexStructure.ofTangentCoordChangeISMul`, and in the tangent
coordinates of every chart it is multiplication by `i` again
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
* `TauCeti.SmoothAlmostComplexStructure.mfderiv_extend_symm_I_mul_of_mem_maximalAtlas`: off the
  real axis, the inverse of a bordered holomorphic chart intertwines multiplication by `i` with it.
* `Structomorph.contMDiff_borderedHolomorphic`: a biholomorphism of Riemann surfaces with
  boundary is smooth up to the boundary.
* `Structomorph.mfderiv_ofBorderedHolomorphic_apply`: the differential of a biholomorphism of
  Riemann surfaces with boundary, a structomorphism for `TauCeti.borderedHolomorphicGroupoid`, is
  complex linear.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 2.4.
-/

public section

open Bundle Set Complex Filter
open scoped Manifold ContDiff Topology

noncomputable section

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid]

variable (M) in
/-- The almost complex structure induced on a Riemann surface with boundary: multiplication by `i`
on every tangent space, which is `ℂ`. It is smooth up to the boundary because the tangent
coordinate changes are complex linear. -/
def ofBorderedHolomorphic : SmoothAlmostComplexStructure closedUpperHalfPlaneModel M :=
  ofTangentCoordChangeISMul closedUpperHalfPlaneModel M fun h v ↦
    ClosedUpperHalfPlane.tangentCoordChange_smul h I v

/-- The induced almost complex structure of a Riemann surface with boundary is multiplication by
`i` on every tangent space. -/
@[simp]
theorem ofBorderedHolomorphic_apply (x : M) (v : ℂ) : ofBorderedHolomorphic M x v = I • v :=
  ofTangentCoordChangeISMul_apply _ x v

/-- The induced almost complex structure of a Riemann surface with boundary is multiplication by
`i` on every tangent space, as an endomorphism. -/
theorem toEndomorphism_ofBorderedHolomorphic (x : M) :
    (ofBorderedHolomorphic M).toEndomorphism x =
      (I • ContinuousLinearMap.id ℝ ℂ :
        TangentSpace closedUpperHalfPlaneModel x →L[ℝ] TangentSpace closedUpperHalfPlaneModel x) :=
  toEndomorphism_ofTangentCoordChangeISMul _ x

/-- In the tangent coordinates of the chart at any point `x₀`, the induced almost complex
structure of a Riemann surface with boundary is multiplication by `i` on the whole chart domain,
boundary points included. -/
theorem inTangentCoordinates_ofBorderedHolomorphic {x₀ x : M}
    (hx : x ∈ (chartAt ClosedUpperHalfPlane x₀).source) :
    inTangentCoordinates closedUpperHalfPlaneModel closedUpperHalfPlaneModel id id
        (fun x ↦ (ofBorderedHolomorphic M).toEndomorphism x) x₀ x =
      I • ContinuousLinearMap.id ℝ ℂ :=
  inTangentCoordinates_ofTangentCoordChangeISMul _ hx

open ClosedUpperHalfPlane in
/-- **Inverse bordered holomorphic charts are holomorphic off the real axis.** For a bordered
holomorphic chart `φ` of a Riemann surface with boundary and a point `z` of positive imaginary part
in its extended target, the derivative of the inverse chart at `z` intertwines multiplication by
`i` with the induced almost complex structure: in the chart at `φ⁻¹ z` it is the derivative of a
holomorphic chart change. -/
theorem mfderiv_extend_symm_I_mul_of_mem_maximalAtlas
    {φ : OpenPartialHomeomorph M ClosedUpperHalfPlane}
    (hφ : φ ∈ borderedHolomorphicGroupoid.maximalAtlas M) {z : ℂ}
    (hz : z ∈ (φ.extend closedUpperHalfPlaneModel).target) (hzim : 0 < z.im) (w : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel (φ.extend closedUpperHalfPlaneModel).symm z
        (I * w) =
      ofBorderedHolomorphic M ((φ.extend closedUpperHalfPlaneModel).symm z)
        (mfderiv 𝓘(ℝ, ℂ) closedUpperHalfPlaneModel (φ.extend closedUpperHalfPlaneModel).symm z
          w) := by
  set x := (φ.extend closedUpperHalfPlaneModel).symm z
  set χ := chartAt ClosedUpperHalfPlane x
  have hzT : closedUpperHalfPlaneModel.symm z ∈ φ.target := by
    rw [OpenPartialHomeomorph.extend_target] at hz
    exact hz.1
  have hφs := mdifferentiableAt_extend_symm_of_im_pos one_ne_zero
    (borderedHolomorphicGroupoid_maximalAtlas_subset (n := 1) (by exact_mod_cast le_top) hφ) hz hzim
  -- The chart change `χ ∘ φ⁻¹`, read in `ℂ`, is holomorphic at `z`.
  have he : φ.symm ≫ₕ χ ∈ borderedHolomorphicGroupoid := (hφ χ (chart_mem_atlas _ x)).1
  have hD : IsOpen (closedUpperHalfPlaneModel.symm ⁻¹' (φ.symm ≫ₕ χ).source ∩
      {v : ℂ | 0 < v.im}) :=
    ((φ.symm ≫ₕ χ).open_source.preimage closedUpperHalfPlaneModel.continuous_symm).inter
      (isOpen_lt continuous_const continuous_im)
  have hτ := ((mem_borderedHolomorphicGroupoid_iff.1 he).2.1).differentiableAt
    (hD.mem_nhds ⟨⟨hzT, mem_chart_source ClosedUpperHalfPlane x⟩, hzim⟩)
  have key : fderiv ℝ (closedUpperHalfPlaneModel ∘ (φ.symm ≫ₕ χ) ∘
      closedUpperHalfPlaneModel.symm) z (I * w) =
        I • fderiv ℝ (closedUpperHalfPlaneModel ∘ (φ.symm ≫ₕ χ) ∘
          closedUpperHalfPlaneModel.symm) z w := by
    rw [hτ.fderiv_restrictScalars ℝ, ContinuousLinearMap.coe_restrictScalars', ← smul_eq_mul,
      map_smul]
  -- `j` is multiplication by `i`, and in the chart at `x` the derivative of the inverse chart is
  -- the derivative of the chart change; the tangent spaces at `z` and `x` are `ℂ` by definition.
  refine Eq.trans ?_ (ofBorderedHolomorphic_apply x _).symm
  -- `simpa` cannot close this: the goal is an equation in `TangentSpace`, which is `ℂ` only up to
  -- unfolding at default transparency, so the coordinate identifications are rewritten explicitly.
  rw [hφs.mfderiv_eq_fderiv_extChartAt_conj rfl, extChartAt_model_space_eq_id, extChartAt,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, Function.comp_id]
  rwa [OpenPartialHomeomorph.coe_trans] at key

omit [HasGroupoid M borderedHolomorphicGroupoid] in
/-- A biholomorphism of Riemann surfaces with boundary, a structomorphism for
`TauCeti.borderedHolomorphicGroupoid`, is `C^n` up to the boundary for every `n ≤ ∞`. -/
theorem _root_.Structomorph.contMDiff_borderedHolomorphic {M' : Type*} [TopologicalSpace M']
    [ChartedSpace ClosedUpperHalfPlane M'] (e : Structomorph borderedHolomorphicGroupoid M M')
    {n : WithTop ℕ∞} (hn : n ≤ ∞) :
    ContMDiff closedUpperHalfPlaneModel closedUpperHalfPlaneModel n e.toHomeomorph :=
  (e.contMDiff borderedHolomorphicGroupoid_le_contDiffGroupoid).of_le hn

/-- **Biholomorphisms are complex linear.** The differential of a bordered holomorphic
structomorphism `e : M → M'` intertwines the induced almost complex structures, at boundary points
as well as interior points: read in the preferred charts, `e` is a member of
`TauCeti.borderedHolomorphicGroupoid`, whose derivatives within the closed upper half-plane are
complex linear. -/
theorem _root_.Structomorph.mfderiv_ofBorderedHolomorphic_apply {M' : Type*} [TopologicalSpace M']
    [ChartedSpace ClosedUpperHalfPlane M'] [HasGroupoid M' borderedHolomorphicGroupoid]
    (e : Structomorph borderedHolomorphicGroupoid M M') (x : M) (v : ℂ) :
    mfderiv closedUpperHalfPlaneModel closedUpperHalfPlaneModel e.toHomeomorph x
        (ofBorderedHolomorphic M x v) =
      ofBorderedHolomorphic M' (e.toHomeomorph x)
        (mfderiv closedUpperHalfPlaneModel closedUpperHalfPlaneModel e.toHomeomorph x v) := by
  rw [ofBorderedHolomorphic_apply]
  refine Eq.trans ?_ (ofBorderedHolomorphic_apply (M := M') _ _).symm
  by_cases hd : MDifferentiableAt closedUpperHalfPlaneModel closedUpperHalfPlaneModel
    e.toHomeomorph x
  · have hz : extChartAt closedUpperHalfPlaneModel x x ∈
        closedUpperHalfPlaneModel.symm ⁻¹' ((chartAt ClosedUpperHalfPlane x).symm ≫ₕ
          e.toHomeomorph.toOpenPartialHomeomorph ≫ₕ
            chartAt ClosedUpperHalfPlane (e.toHomeomorph x)).source ∩
        range closedUpperHalfPlaneModel :=
      ⟨by simp [mem_chart_source], mem_range_self _⟩
    rw [hd.mfderiv, e.toHomeomorph.writtenInExtChartAt_eq]
    exact ClosedUpperHalfPlane.fderivWithin_apply_smul_of_mem_borderedHolomorphicGroupoid
      (e.mem_groupoid _ _ (chart_mem_atlas _ x) (chart_mem_atlas _ _)) hz I v
  · rw [mfderiv_zero_of_not_mdifferentiableAt hd]
    exact (smul_zero (A := ℂ) I).symm

/-! ### Check: the closed upper half-plane -/

/-- On the closed upper half-plane, the inclusion into `ℂ` is pseudoholomorphic from the induced
almost complex structure to the almost complex structure of `ℂ` as a complex manifold, at boundary
points as well as interior points. -/
theorem isPseudoholomorphic_coe_ofBorderedHolomorphic :
    IsPseudoholomorphic (ofBorderedHolomorphic ClosedUpperHalfPlane) (ofComplexManifold ℂ ℂ)
      ((↑) : ClosedUpperHalfPlane → ℂ) := by
  refine isPseudoholomorphic_iff.2 fun z ↦ ?_
  refine isPseudoholomorphicAt_of_hasMFDerivAt (u' := ContinuousLinearMap.id ℝ ℂ)
    ⟨continuous_subtypeVal.continuousAt, ?_⟩ fun w ↦
      (ofBorderedHolomorphic_apply z w).trans (ofComplexManifold_apply (E := ℂ) (z : ℂ) w).symm
  -- In the self charts, the inclusion reads as the identity on the closed upper half-plane.
  refine (hasFDerivWithinAt_id (𝕜 := ℝ) _ _).congr (fun w hw ↦ ?_) ?_
  · simp only [mfld_simps, writtenInExtChartAt, Function.comp_apply]
    exact coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (by simpa using hw)
  · simp [writtenInExtChartAt]

end SmoothAlmostComplexStructure

end TauCeti
