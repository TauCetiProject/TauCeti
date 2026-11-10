/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure

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
