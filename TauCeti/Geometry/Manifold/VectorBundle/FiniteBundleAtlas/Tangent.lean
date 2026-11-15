/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.HalfPlane
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom

/-!
# Finite bundle atlases of tangent and one-form bundles for models with corners

`TauCeti.FiniteBundleAtlas.tangent` and `TauCeti.FiniteBundleAtlas.tangentHom` construct atlases of
the tangent bundle and of the bundle of `V`-valued one-forms on the charts of a finite bundle atlas
`A` of `V` when the base manifold has no boundary (`I = 𝓘(ℝ, E)`). Because the preferred
trivialization of `TangentSpace I` at a point `x₀` has `(chartAt H x₀).source` as its base set for
every model with corners `I : ModelWithCorners 𝕜 E H`, the same construction works without change on
manifolds with boundary or corners (`TauCeti.FiniteBundleAtlas.modelTangent`,
`TauCeti.FiniteBundleAtlas.modelTangentHom`).

When `M` carries a smooth almost complex structure `j` that reads as multiplication by `i` in the
tangent coordinates of chart `i`, the `(0,1)`-part of a `V`-valued one-form is read in chart `i` as
the complex antilinear part `ContinuousLinearMap.complexAntilinearPartL` of its reading
(`TauCeti.FiniteBundleAtlas.coord_modelTangentHom_zeroOnePart`), and a one-form is a `(0,1)`-form
at a chart point exactly when its reading is complex antilinear
(`TauCeti.FiniteBundleAtlas.isZeroOneForm_iff_coord_modelTangentHom`).

Specializing to the closed upper half-plane model `closedUpperHalfPlaneModel` gives
`TauCeti.FiniteBundleAtlas.halfTangent` and `TauCeti.FiniteBundleAtlas.halfTangentHom`, whose planar
chart images, overlaps and transitions agree with those of `A`. On a Riemann surface with boundary
(`[HasGroupoid M borderedHolomorphicGroupoid]`), the induced almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofBorderedHolomorphic M` reads as multiplication by `i` in
every chart up to and including the real boundary, yielding
`TauCeti.FiniteBundleAtlas.halfCoord_halfTangentHom_zeroOnePart` and
`TauCeti.FiniteBundleAtlas.isZeroOneForm_iff_halfCoord_halfTangentHom`.

## Main definitions

* `TauCeti.FiniteBundleAtlas.modelTangent`: the charts of `A` as a finite bundle atlas of
  `TangentSpace I` for any `ModelWithCorners 𝕜 E H`.
* `TauCeti.FiniteBundleAtlas.modelTangentHom`: the finite bundle atlas of
  `x ↦ TangentSpace I x →L[𝕜] V x` on the charts of `A`.
* `TauCeti.FiniteBundleAtlas.halfTangent`, `TauCeti.FiniteBundleAtlas.halfTangentHom`: the
  specializations to manifolds modelled on `ClosedUpperHalfPlane`.

## Main results

* `TauCeti.FiniteBundleAtlas.coord_modelTangentHom`,
  `TauCeti.FiniteBundleAtlas.coord_modelTangentHom_apply`: chart readings of `V`-valued one-forms
  and pointwise evaluation on vector fields.
* `TauCeti.FiniteBundleAtlas.coord_modelTangentHom_zeroOnePart`,
  `TauCeti.FiniteBundleAtlas.isZeroOneForm_iff_coord_modelTangentHom`: chart readings of the
  `(0,1)`-projection and `(0,1)`-form condition for any almost complex structure reading as `i • id`
  in tangent coordinates.
* `TauCeti.FiniteBundleAtlas.halfCoord_halfTangentHom_zeroOnePart`,
  `TauCeti.FiniteBundleAtlas.isZeroOneForm_iff_halfCoord_halfTangentHom`: planar half-plane readings
  of `(0,1)`-forms over a Riemann surface with boundary, valid up to the real axis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.4 and Appendix C.1.
-/

public section

noncomputable section

open Bundle Set ContinuousLinearMap
open scoped Manifold ContDiff

universe u

namespace TauCeti

namespace FiniteBundleAtlas

section ModelTangent

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type u} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

/-- The charts of a finite bundle atlas of `V` as a finite bundle atlas of `TangentSpace I` for a
general model with corners `I : ModelWithCorners 𝕜 E H`. -/
abbrev modelTangent (A : FiniteBundleAtlas H M F V) :
    FiniteBundleAtlas H M E (TangentSpace I) :=
  A.ofBaseSet fun i ↦ by
    rw [TangentBundle.trivializationAt_baseSet]
    exact A.closure_dom_subset_source i

end ModelTangent

section ModelTangentHom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type u} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

variable (A : FiniteBundleAtlas H M F V)

/-- The finite bundle atlas of the bundle `x ↦ TangentSpace I x →L[𝕜] V x` of `V`-valued one-forms
on the charts of a finite bundle atlas of `V`, for any model with corners `I`. -/
abbrev modelTangentHom :
    FiniteBundleAtlas H M (E →L[𝕜] F) (fun x ↦ TangentSpace I x →L[𝕜] V x) :=
  (A.modelTangent I).hom A.closure_dom_subset_baseSet

section ModelTangentHomImage

variable {I A}

@[simp]
theorem chart_modelTangentHom (i : Fin A.n) : (A.modelTangentHom I).chart i = A.chart i :=
  (rfl)

@[simp]
theorem image_modelTangentHom (i : Fin A.n) : (A.modelTangentHom I).image i = A.image i :=
  (image_hom (A := A.modelTangent I) i).trans (image_ofBaseSet i)

@[simp]
theorem overlap_modelTangentHom (i i' : Fin A.n) :
    (A.modelTangentHom I).overlap i i' = A.overlap i i' :=
  (overlap_hom (A := A.modelTangent I) i i').trans (overlap_ofBaseSet i i')

end ModelTangentHomImage

/-- A `V`-valued one-form read in chart `i` of `A.modelTangentHom I` is its value at the
corresponding point of `M` expressed in the preferred trivializations of `TangentSpace I` and of `V`
at the centre of the chart. -/
theorem coord_modelTangentHom (i : Fin A.n) (θ : ∀ x, TangentSpace I x →L[𝕜] V x) (y : H) :
    (A.modelTangentHom I).coord i θ y =
      ContinuousLinearMap.inCoordinates E (TangentSpace I) F V (A.center i)
        ((A.chart i).symm y) (A.center i) ((A.chart i).symm y) (θ ((A.chart i).symm y)) :=
  (A.modelTangent I).coord_hom A.closure_dom_subset_baseSet i θ y

/-- On the image of chart `i`, applying the chart reading of a `V`-valued one-form `θ` to the chart
reading of a vector field `v` gives the chart reading of `x ↦ θ x (v x)`. -/
theorem coord_modelTangentHom_apply (i : Fin A.n) (θ : ∀ x, TangentSpace I x →L[𝕜] V x)
    (v : ∀ x, TangentSpace I x) {y : H} (hy : y ∈ A.image i) :
    (A.modelTangentHom I).coord i θ y ((A.modelTangent I).coord i v y) =
      A.coord i (fun x ↦ θ x (v x)) y :=
  (A.modelTangent I).coord_hom_apply A.closure_dom_subset_baseSet i θ v
    ((A.modelTangent I).mem_image.2 (A.mem_image.1 hy))

end ModelTangentHom

section AlmostComplex

open SmoothAlmostComplexStructure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  {H : Type u} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  (A : FiniteBundleAtlas H M F V) {j : SmoothAlmostComplexStructure I M}

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] in
/-- Where an almost complex structure `j` reads as multiplication by `i` in the tangent coordinates
of chart `i`, the `(0,1)`-part of a `V`-valued one-form is read in chart `i` as the complex
antilinear part `ContinuousLinearMap.complexAntilinearPartL` of its reading. -/
theorem coord_modelTangentHom_zeroOnePart (i : Fin A.n)
    (hj : ∀ ⦃x⦄, x ∈ (A.chart i).source →
      inTangentCoordinates I I id id (fun x ↦ j.toEndomorphism x) (A.center i) x =
        Complex.I • ContinuousLinearMap.id ℝ E)
    (θ : ∀ x, TangentSpace I x →L[ℝ] V x) (y : H) :
    (A.modelTangentHom I).coord i (fun x ↦ j.zeroOnePart (θ x)) y =
      complexAntilinearPartL ((A.modelTangentHom I).coord i θ y) := by
  rw [A.coord_modelTangentHom I, A.coord_modelTangentHom I]
  by_cases hx : (A.chart i).symm y ∈ (A.chart i).source
  · exact inCoordinates_zeroOnePart _ (hj hx) _
  · -- Outside the chart source the tangent trivialization vanishes, so both readings vanish.
    have hx' : (A.chart i).symm y ∉
        (trivializationAt E (TangentSpace I) (A.center i)).baseSet := by
      rwa [TangentBundle.trivializationAt_baseSet]
    ext v
    simp [ContinuousLinearMap.inCoordinates, Trivialization.symmL_apply_of_notMem _ hx']

/-- On the image of chart `i`, where `j` reads as multiplication by `i` in tangent coordinates, a
one-form is a `(0,1)`-form at `(A.chart i).symm y` exactly when its chart reading is complex
antilinear. -/
theorem isZeroOneForm_iff_coord_modelTangentHom (i : Fin A.n)
    (hj : ∀ ⦃x⦄, x ∈ (A.chart i).source →
      inTangentCoordinates I I id id (fun x ↦ j.toEndomorphism x) (A.center i) x =
        Complex.I • ContinuousLinearMap.id ℝ E)
    (θ : ∀ x, TangentSpace I x →L[ℝ] V x) {y : H} (hy : y ∈ A.image i) :
    j.IsZeroOneForm (θ ((A.chart i).symm y)) ↔
      ∀ v, (A.modelTangentHom I).coord i θ y (Complex.I • v) =
        -(Complex.I • (A.modelTangentHom I).coord i θ y v) := by
  rw [A.coord_modelTangentHom I]
  exact isZeroOneForm_iff_inCoordinates
    (hj (A.dom_subset_chart_source i (A.symm_mem_dom hy)))
    (A.dom_subset_baseSet i (A.symm_mem_dom hy))

end AlmostComplex

section HalfPlane

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]

section RealBundle

variable [IsManifold closedUpperHalfPlaneModel 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

/-- The charts of a finite bundle atlas over a base modelled on `ClosedUpperHalfPlane`, viewed as a
finite bundle atlas of `TangentSpace closedUpperHalfPlaneModel`. -/
abbrev halfTangent :
    FiniteBundleAtlas ClosedUpperHalfPlane M ℂ (TangentSpace closedUpperHalfPlaneModel) :=
  A.modelTangent closedUpperHalfPlaneModel

/-- The finite bundle atlas of the bundle of `V`-valued one-forms
`x ↦ TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x` on the charts of a finite bundle atlas `A`
over a base modelled on `ClosedUpperHalfPlane`. -/
abbrev halfTangentHom :
    FiniteBundleAtlas ClosedUpperHalfPlane M (ℂ →L[ℝ] F)
      (fun x ↦ TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) :=
  A.modelTangentHom closedUpperHalfPlaneModel

section HalfGeometry

variable {A}

@[simp]
theorem halfImage_halfTangentHom (i : Fin A.n) :
    A.halfTangentHom.halfImage i = A.halfImage i :=
  SetLike.ext fun z ↦ by
    rw [mem_halfImage (A := A.halfTangentHom) (i := i), mem_halfImage (A := A) (i := i),
      image_modelTangentHom]

@[simp]
theorem halfClosedImage_halfTangentHom (i : Fin A.n) :
    A.halfTangentHom.halfClosedImage i = A.halfClosedImage i := by
  rw [halfClosedImage_eq_image_val A.halfTangentHom i, halfClosedImage_eq_image_val A i,
    image_modelTangentHom]

@[simp]
theorem halfOverlap_halfTangentHom (i i' : Fin A.n) :
    A.halfTangentHom.halfOverlap i i' = A.halfOverlap i i' :=
  Set.ext fun z ↦ by
    rw [mem_halfOverlap (A := A.halfTangentHom) (i := i) (i' := i'),
      mem_halfOverlap (A := A) (i := i) (i' := i'), overlap_modelTangentHom]

end HalfGeometry

/-- A `V`-valued one-form read in `ℂ` in chart `i` of `A.halfTangentHom` is its value at the
corresponding point of `M` expressed in the preferred trivializations of the tangent bundle and of
`V` at `A.center i`. -/
theorem halfCoord_halfTangentHom (i : Fin A.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) (z : ℂ) :
    A.halfTangentHom.halfCoord i θ z =
      ContinuousLinearMap.inCoordinates ℂ (TangentSpace closedUpperHalfPlaneModel) F V
        (A.center i) ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) (A.center i)
        ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))
        (θ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))) :=
  (halfCoord_def A.halfTangentHom i θ z).trans
    (A.coord_modelTangentHom closedUpperHalfPlaneModel i θ (closedUpperHalfPlaneModel.symm z))

/-- On the image of chart `i`, including boundary points on the real axis, applying the planar chart
reading of a `V`-valued one-form `θ` to that of a vector field `v` gives the planar chart reading
of `x ↦ θ x (v x)`. -/
theorem halfCoord_halfTangentHom_apply (i : Fin A.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x)
    (v : ∀ x, TangentSpace closedUpperHalfPlaneModel x) {z : ℂ}
    (hz : closedUpperHalfPlaneModel.symm z ∈ A.image i) :
    A.halfTangentHom.halfCoord i θ z (A.halfTangent.halfCoord i v z) =
      A.halfCoord i (fun x ↦ θ x (v x)) z := by
  rw [halfCoord_def A.halfTangentHom i, halfCoord_def A.halfTangent i, halfCoord_def A i]
  exact A.coord_modelTangentHom_apply closedUpperHalfPlaneModel i θ v hz

end RealBundle

section BorderedHolomorphic

open SmoothAlmostComplexStructure

variable [HasGroupoid M borderedHolomorphicGroupoid]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] in
/-- On a Riemann surface with boundary, the `(0,1)`-part of a `V`-valued one-form with respect to
`ofBorderedHolomorphic M` is read in `ℂ` in chart `i` as the complex antilinear part
`ContinuousLinearMap.complexAntilinearPartL` of its reading, at boundary points as well as interior
points. -/
theorem halfCoord_halfTangentHom_zeroOnePart (i : Fin A.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) (z : ℂ) :
    A.halfTangentHom.halfCoord i (fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x)) z =
      complexAntilinearPartL (A.halfTangentHom.halfCoord i θ z) := by
  rw [halfCoord_def A.halfTangentHom i, halfCoord_def A.halfTangentHom i]
  exact coord_modelTangentHom_zeroOnePart A i
    (fun _ hx ↦ inTangentCoordinates_ofBorderedHolomorphic hx) θ (closedUpperHalfPlaneModel.symm z)

/-- On the image of chart `i` of a Riemann surface with boundary, including its points on the real
axis, a one-form is a `(0,1)`-form at the corresponding point of `M` exactly when its planar chart
reading is complex antilinear. -/
theorem isZeroOneForm_iff_halfCoord_halfTangentHom (i : Fin A.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) {z : ℂ}
    (hz : closedUpperHalfPlaneModel.symm z ∈ A.image i) :
    (ofBorderedHolomorphic M).IsZeroOneForm
        (θ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))) ↔
      ∀ v, A.halfTangentHom.halfCoord i θ z (Complex.I • v) =
        -(Complex.I • A.halfTangentHom.halfCoord i θ z v) := by
  rw [halfCoord_def A.halfTangentHom i]
  exact isZeroOneForm_iff_coord_modelTangentHom A i
    (fun _ hx ↦ inTangentCoordinates_ofBorderedHolomorphic hx) θ hz

end BorderedHolomorphic

end HalfPlane

end FiniteBundleAtlas

end TauCeti
