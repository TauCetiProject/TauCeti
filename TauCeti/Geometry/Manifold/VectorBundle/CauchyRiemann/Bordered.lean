/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.HalfPlane
import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart

/-!
# Chart readings of `(0,1)`-forms on Riemann surfaces with boundary

Let `M` be a Riemann surface with boundary, a charted space modelled on `ClosedUpperHalfPlane` whose
transition maps lie in `TauCeti.borderedHolomorphicGroupoid`, and let `V → M` be a complex vector
bundle with model fibre `F`, regarded as a real vector bundle with a finite bundle atlas
`A : TauCeti.FiniteBundleAtlas ClosedUpperHalfPlane M F V`.

Because the canonical almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofBorderedHolomorphic M` reads as `i • id` in tangent
coordinates on the whole domain of every chart, boundary points included
(`TauCeti.SmoothAlmostComplexStructure.inTangentCoordinates_ofBorderedHolomorphic`), the general
chart-reading criteria of `TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart` specialize to
charts of `A` both on `ClosedUpperHalfPlane` (`coord`) and in `ℂ` (`halfCoord`), up to and on the
real boundary.

## Main results

* `TauCeti.FiniteBundleAtlas.coord_tangentHom_ofBorderedHolomorphic_zeroOnePart`,
  `TauCeti.FiniteBundleAtlas.halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart`: the
  `(0,1)`-part of a one-form is read in `ClosedUpperHalfPlane` and in `ℂ` as
  `ContinuousLinearMap.complexAntilinearPartL` of its chart reading, including on the real axis.
* `TauCeti.FiniteBundleAtlas.isZeroOneForm_ofBorderedHolomorphic_iff_coord_tangentHom`,
  `TauCeti.FiniteBundleAtlas.isZeroOneForm_ofBorderedHolomorphic_iff_halfCoord_tangentHom`,
  `TauCeti.FiniteBundleAtlas.isZeroOneForm_ofBorderedHolomorphic_chart_iff_halfCoord`: on the image
  or domain of chart `i`, boundary points included, a one-form is a `(0,1)`-form iff its chart
  reading is complex antilinear.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.4 and Appendix C.1–C.2.
-/

public section

noncomputable section

open Bundle
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold

namespace TauCeti

namespace FiniteBundleAtlas

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

variable [IsScalarTower ℝ ℂ F] [∀ x, IsScalarTower ℝ ℂ (V x)] in
/-- The `(0,1)`-part of a one-form on a Riemann surface with boundary is read in a chart on
`ClosedUpperHalfPlane` as `ContinuousLinearMap.complexAntilinearPartL` of its reading. -/
theorem coord_tangentHom_ofBorderedHolomorphic_zeroOnePart (i : Fin A.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) (y : ClosedUpperHalfPlane) :
    letI := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
    (A.tangentHom closedUpperHalfPlaneModel).coord i
        (fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x)) y =
      complexAntilinearPartL ((A.tangentHom closedUpperHalfPlaneModel).coord i θ y) :=
  A.coord_tangentHom_zeroOnePart_of_inTangentCoordinates (ofBorderedHolomorphic M) i
    (fun _ hx ↦ inTangentCoordinates_ofBorderedHolomorphic hx) θ y

variable [IsScalarTower ℝ ℂ F] [∀ x, IsScalarTower ℝ ℂ (V x)] in
/-- The `(0,1)`-part of a one-form on a Riemann surface with boundary is read in `ℂ` as
`ContinuousLinearMap.complexAntilinearPartL` of its reading `halfCoord`, including on the real
axis. -/
theorem halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart (i : Fin A.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) (z : ℂ) :
    letI := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
    (A.tangentHom closedUpperHalfPlaneModel).halfCoord i
        (fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x)) z =
      complexAntilinearPartL ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ z) := by
  have := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  exact ((A.tangentHom closedUpperHalfPlaneModel).halfCoord_def i _ z).trans <|
    (A.coord_tangentHom_ofBorderedHolomorphic_zeroOnePart i θ
      (closedUpperHalfPlaneModel.symm z)).trans <|
        congrArg complexAntilinearPartL
          ((A.tangentHom closedUpperHalfPlaneModel).halfCoord_def i θ z).symm

/-- On the image of a chart on a Riemann surface with boundary, boundary points included, a
one-form is read as a complex antilinear map iff it is a `(0,1)`-form at the corresponding point. -/
theorem isZeroOneForm_ofBorderedHolomorphic_iff_coord_tangentHom (i : Fin A.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x)
    {y : ClosedUpperHalfPlane} (hy : y ∈ A.image i) :
    (ofBorderedHolomorphic M).IsZeroOneForm (θ ((A.chart i).symm y)) ↔
      ∀ v : ℂ,
        (A.tangentHom closedUpperHalfPlaneModel).coord i θ y (Complex.I • v) =
          -(Complex.I • (A.tangentHom closedUpperHalfPlaneModel).coord i θ y v) :=
  A.isZeroOneForm_iff_coord_tangentHom_of_inTangentCoordinates (ofBorderedHolomorphic M) i θ hy
    (inTangentCoordinates_ofBorderedHolomorphic (A.dom_subset_chart_source i (A.symm_mem_dom hy)))

/-- At any point `z : ℂ` whose clamped point lies in the image of chart `i`, including points of
`A.halfImage i` and real boundary points in `A.halfClosedImage i`, a one-form is read in `ℂ` as a
complex antilinear map iff it is a `(0,1)`-form at the corresponding point of `M`. -/
theorem isZeroOneForm_ofBorderedHolomorphic_iff_halfCoord_tangentHom (i : Fin A.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x)
    {z : ℂ} (hz : closedUpperHalfPlaneModel.symm z ∈ A.image i) :
    (ofBorderedHolomorphic M).IsZeroOneForm
        (θ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))) ↔
      ∀ v : ℂ,
        (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ z (Complex.I • v) =
          -(Complex.I • (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ z v) :=
  (A.isZeroOneForm_ofBorderedHolomorphic_iff_coord_tangentHom i θ hz).trans <|
    Iff.of_eq <| congrArg (fun f : ℂ →L[ℝ] F ↦ ∀ v : ℂ, f (Complex.I • v) = -(Complex.I • f v))
      ((A.tangentHom closedUpperHalfPlaneModel).halfCoord_def i θ z).symm

/-- At any point `x ∈ A.dom i`, boundary points included, a one-form `θ` is a `(0,1)`-form at `x`
iff its reading in `ℂ` at `A.chart i x` is complex antilinear. -/
theorem isZeroOneForm_ofBorderedHolomorphic_chart_iff_halfCoord {i : Fin A.n}
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) {x : M} (hx : x ∈ A.dom i) :
    (ofBorderedHolomorphic M).IsZeroOneForm (θ x) ↔
      ∀ v : ℂ,
        (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ (A.chart i x : ℂ) (Complex.I • v) =
          -(Complex.I •
            (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ (A.chart i x : ℂ) v) := by
  have himg : closedUpperHalfPlaneModel.symm (A.chart i x : ℂ) ∈ A.image i := by
    simpa using A.mem_image.2 ⟨x, hx, rfl⟩
  have hsymm : (A.chart i).symm (closedUpperHalfPlaneModel.symm (A.chart i x : ℂ)) = x := by
    rw [closedUpperHalfPlaneModel_symm_coe, (A.chart i).left_inv (A.dom_subset_chart_source i hx)]
  have h := A.isZeroOneForm_ofBorderedHolomorphic_iff_halfCoord_tangentHom i θ himg
  rwa [hsymm] at h

end FiniteBundleAtlas

end TauCeti
