/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.SMul
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm
import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.ClosedAnnulus

/-!
# Sobolev `(0,1)`-forms over a Riemann surface with boundary

Let `M` be a Riemann surface with boundary, a charted space modelled on `ClosedUpperHalfPlane` whose
transition maps lie in `TauCeti.borderedHolomorphicGroupoid`, and let `V → M` be a complex vector
bundle with finite-dimensional model fibre `F`, regarded as a real vector bundle. Equipped with the
canonical almost complex structure `TauCeti.SmoothAlmostComplexStructure.ofBorderedHolomorphic M`,
which is smooth up to the real boundary, a `V`-valued one-form `η : T_x M → V x` is a `(0,1)`-form
when `η (j x v) = -(i • η v)` (`TauCeti.SmoothAlmostComplexStructure.IsZeroOneForm`). This file
constructs the target space `W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)` of real Cauchy–Riemann operators on a
compact Riemann surface with boundary as a closed complemented Banach subspace
`TauCeti.borderedZeroOneSobolevSections A p k` of the Sobolev space
`TauCeti.BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k` of `V`-valued
one-forms, for a finite bundle atlas `A` of `V`.

Because the real derivative within the closed upper half-plane of every member of
`TauCeti.borderedHolomorphicGroupoid` is complex linear up to and on the real boundary, the tangent
coordinate changes of `M` are complex linear
(`TauCeti.ClosedUpperHalfPlane.tangentCoordChange_smul`) and `ofBorderedHolomorphic M` reads as
`i • id` in tangent coordinates on the whole domain of every chart, boundary points included
(`TauCeti.SmoothAlmostComplexStructure.inTangentCoordinates_ofBorderedHolomorphic`). Feeding this
coordinate identity into the general chart-reading lemmas of
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ZeroOneForm` shows that in every chart `i`:
* the `(0,1)`-part of a one-form is read in `ℂ` as `ContinuousLinearMap.complexAntilinearPartL` of
  its chart reading
  (`TauCeti.FiniteBundleAtlas.halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart`), and
* at every point of `A.dom i`, boundary points included, a one-form is a `(0,1)`-form iff its chart
  reading in `ℂ` is complex antilinear
  (`TauCeti.FiniteBundleAtlas.isZeroOneForm_ofBorderedHolomorphic_chart_iff_halfCoord`).

Instantiating the `SectionChartData`-level complex-antilinear subspace theory on
`(A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData` then yields
`TauCeti.borderedZeroOneSobolevSections A p k`, its continuous `(0,1)`-projection
`TauCeti.borderedZeroOnePartSobolevL`, the order and exponent inclusions
`TauCeti.borderedZeroOneLowerOrderL` and `TauCeti.borderedZeroOneOfExponentLEL`, and multiplication
by smooth real functions up to the boundary `TauCeti.borderedZeroOneContMDiffSMulL`.

Two boundary-specific results connect the interior `Lᵖ` definition on `A.halfImage i` (`0 < im z`)
back to the real boundary (`im z = 0`), which has Lebesgue measure zero:
* **Smooth `(0,1)`-forms up to the boundary**
  (`TauCeti.ofContMDiffSection_mem_borderedZeroOneSobolevSections_iff`,
  `TauCeti.borderedZeroOneOfContMDiffSection`): a `Cᵏ` one-form up to the boundary defines an
  element of `borderedZeroOneSobolevSections A p k` iff it is a `(0,1)`-form at *every* point of
  `M`, boundary points included, because its chart coordinates are continuous on `A.halfChartSet i`
  and every boundary point in `A.halfClosedImage i` is a limit of interior points in
  `A.halfImage i`. Likewise its `(0,1)`-projection vanishes iff it is complex linear at every point
  of `M` (`TauCeti.borderedZeroOnePartSobolevL_ofContMDiffSection_eq_zero_iff`).
* **Localization up to the boundary** (`TauCeti.exists_isZeroOneForm_memWkpLoc`): every element of
  `borderedZeroOneSobolevSections A p k` is represented by a global `(0,1)`-form `θ` on `M` (at
  boundary points as well as interior points) whose chart reading in every chart `i` belongs to the
  local Sobolev class `TauCeti.MemWkpLoc p (A.halfClosedImage i) k` on the full chart image in the
  closed upper half-plane.

## Main definitions

* `TauCeti.borderedZeroOneSobolevSections A p k`: the subspace `W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)` of
  `BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k`.
* `TauCeti.borderedZeroOnePartSobolevL A p k`: the continuous `(0,1)`-projection onto it.
* `TauCeti.borderedZeroOneLowerOrderL`, `TauCeti.borderedZeroOneOfExponentLEL`,
  `TauCeti.borderedZeroOneContMDiffSMulL`: the order and exponent inclusions and multiplication by
  smooth real functions up to the boundary.
* `TauCeti.isZeroOneFormContMDiffSubmodule M F V k` and
  `TauCeti.borderedZeroOneOfContMDiffSection A p k`: the submodule of `Cᵏ` `(0,1)`-forms up to the
  boundary and its injective linear embedding into `borderedZeroOneSobolevSections A p k`.

## Main results

* `TauCeti.FiniteBundleAtlas.halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart`,
  `TauCeti.FiniteBundleAtlas.isZeroOneForm_ofBorderedHolomorphic_iff_halfCoord_tangentHom`,
  `TauCeti.FiniteBundleAtlas.isZeroOneForm_ofBorderedHolomorphic_chart_iff_halfCoord`: chart
  readings of `(0,1)`-forms and `(0,1)`-projections up to and on the real boundary.
* `TauCeti.mem_borderedZeroOneSobolevSections_iff`,
  `TauCeti.mem_borderedZeroOneSobolevSections_iff_isZeroOneForm`,
  `TauCeti.isClosed_borderedZeroOneSobolevSections`,
  `TauCeti.borderedZeroOneSobolevSections.instCompleteSpace`,
  `TauCeti.closedComplemented_borderedZeroOneSobolevSections`: membership, closedness, completeness,
  and complementedness.
* `TauCeti.ofContMDiffSection_mem_borderedZeroOneSobolevSections_iff`,
  `TauCeti.borderedZeroOnePartSobolevL_ofContMDiffSection_eq_zero_iff`,
  `TauCeti.borderedZeroOneOfContMDiffSection_injective`: `Cᵏ` one-forms up to the boundary.
* `TauCeti.exists_isZeroOneForm_memWkpLoc`: representation by global `(0,1)`-forms in
  `MemWkpLoc p (A.halfClosedImage i) k` up to the boundary.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.4 and Appendix C.1–C.2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL complexAntilinearPartL_eq_self_iff
  complexAntilinearPartL_eq_zero_iff)
open scoped Manifold ENNReal ContDiff

namespace TauCeti

open SmoothAlmostComplexStructure

/-! ### Chart readings of `(0,1)`-forms up to the boundary -/

namespace FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

variable [IsScalarTower ℝ ℂ F] [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] in
/-- The `(0,1)`-part of a one-form on a Riemann surface with boundary is read in a chart on
`ClosedUpperHalfPlane` as `ContinuousLinearMap.complexAntilinearPartL` of its reading. -/
theorem coord_tangentHom_ofBorderedHolomorphic_zeroOnePart (i : Fin A.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) (y : ClosedUpperHalfPlane) :
    (A.tangentHom closedUpperHalfPlaneModel).coord i
        (fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x)) y =
      complexAntilinearPartL ((A.tangentHom closedUpperHalfPlaneModel).coord i θ y) :=
  A.coord_tangentHom_zeroOnePart_of_inTangentCoordinates (ofBorderedHolomorphic M) i
    (fun _ hx ↦ inTangentCoordinates_ofBorderedHolomorphic hx) θ y

variable [IsScalarTower ℝ ℂ F] [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] in
/-- The `(0,1)`-part of a one-form on a Riemann surface with boundary is read in `ℂ` as
`ContinuousLinearMap.complexAntilinearPartL` of its reading `halfCoord`, including on the real
axis. -/
theorem halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart (i : Fin A.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) (z : ℂ) :
    (A.tangentHom closedUpperHalfPlaneModel).halfCoord i
        (fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x)) z =
      complexAntilinearPartL ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ z) :=
  ((A.tangentHom closedUpperHalfPlaneModel).halfCoord_def i _ z).trans <|
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
    forall_congr' fun v ↦ by
      let B := A.tangentHom closedUpperHalfPlaneModel
      let j : Fin B.n := i
      change B.coord j θ (closedUpperHalfPlaneModel.symm z) (Complex.I • v) =
          -(Complex.I • B.coord j θ (closedUpperHalfPlaneModel.symm z) v) ↔
        B.halfCoord j θ z (Complex.I • v) = -(Complex.I • B.halfCoord j θ z v)
      rw [B.halfCoord_def j θ z]

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
    rw [closedUpperHalfPlaneModel_symm_coe]
    exact A.mem_image.2 ⟨x, hx, rfl⟩
  have hsymm : (A.chart i).symm (closedUpperHalfPlaneModel.symm (A.chart i x : ℂ)) = x := by
    rw [closedUpperHalfPlaneModel_symm_coe, (A.chart i).left_inv (A.dom_subset_chart_source i hx)]
  have h := A.isZeroOneForm_ofBorderedHolomorphic_iff_halfCoord_tangentHom i θ himg
  rwa [hsymm] at h

omit [NormedSpace ℂ F] [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V] in
/-- An almost everywhere statement on the chart image in `ℂ` of `A.tangentHom` is one on
`A.halfImage i`. -/
private theorem ae_restrict_halfImage_tangentHom_iff' {i : Fin A.n} {P : ℂ → Prop} :
    (∀ᵐ z ∂volume.restrict ((A.tangentHom closedUpperHalfPlaneModel).halfImage i : Set ℂ),
        P z) ↔
      ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ), P z := by
  rw [halfImage_tangentHom]

omit [NormedSpace ℂ F] [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V] in
/-- An almost everywhere statement on the `halfSectionChartData` image of `A.tangentHom` is one on
`A.halfImage i`. -/
private theorem ae_restrict_halfSectionChartData_image_tangentHom_iff
    {i : Fin A.n} {P : ℂ → Prop} :
    (∀ᵐ z ∂volume.restrict
        ((A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.image i : Set ℂ), P z) ↔
      ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ), P z := by
  rw [(A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData_image i, halfImage_tangentHom]

end FiniteBundleAtlas

/-! ### The Sobolev space of `(0,1)`-forms over a Riemann surface with boundary -/

section BorderedZeroOne

open FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealBorderedZeroOneForm : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

omit [FiniteDimensional ℝ F] in
private theorem halfSectionChartData_coord_zeroOnePart [∀ x, ContinuousSMul ℂ (V x)]
    (i : Fin (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) {z : ℂ}
    (hz : z ∈ (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.image i) :
    (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.coord i
        (fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x)) z =
      complexAntilinearPartL
        ((A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.coord i θ z) := by
  rw [(A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData_coord_of_mem _ hz,
    (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData_coord_of_mem _ hz]
  exact A.halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart i θ z

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The `(0,1)`-forms in the Sobolev space `W^{k,p}` of `V`-valued one-forms on a Riemann surface
with boundary, the space `W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)`: the elements whose chart data are complex
antilinear almost everywhere on the interior `A.halfImage i` of every chart image
(`TauCeti.mem_borderedZeroOneSobolevSections_iff`). -/
def borderedZeroOneSobolevSections :
    Submodule ℝ (BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) :=
  (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.antilinearSobolevSections
    volume p k

instance borderedZeroOneSobolevSections.instNormedAddCommGroup :
    NormedAddCommGroup (borderedZeroOneSobolevSections A p k) :=
  (borderedZeroOneSobolevSections A p k).normedAddCommGroup

instance borderedZeroOneSobolevSections.instNormedSpace :
    NormedSpace ℝ (borderedZeroOneSobolevSections A p k) :=
  (borderedZeroOneSobolevSections A p k).normedSpace

instance borderedZeroOneSobolevSections.instIsTopologicalAddGroup :
    IsTopologicalAddGroup (borderedZeroOneSobolevSections A p k) :=
  Submodule.isTopologicalAddGroup (borderedZeroOneSobolevSections A p k)

variable {A p k}

/-- An element of `W^{k,p}` of `V`-valued one-forms over a Riemann surface with boundary is a
`(0,1)`-form iff its chart data are complex antilinear almost everywhere on the interior
`A.halfImage i` of every chart image. -/
theorem mem_borderedZeroOneSobolevSections_iff
    {w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k} :
    w ∈ borderedZeroOneSobolevSections A p k ↔
      ∀ i : Fin A.n, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ), ∀ v : ℂ,
        (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL
            volume p k i w z (Complex.I • v) =
          -(Complex.I •
            (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL
              volume p k i w z v) := by
  rw [borderedZeroOneSobolevSections, SectionChartData.mem_antilinearSobolevSections_iff]
  exact forall_congr' fun i ↦ ae_restrict_halfSectionChartData_image_tangentHom_iff A

/-- An element of `W^{k,p}` of `V`-valued one-forms whose chart data on `A.halfImage i` are the
coordinates `halfCoord` of a one-form `θ` belongs to `borderedZeroOneSobolevSections A p k` iff
`θ` is a `(0,1)`-form almost everywhere on the interior of every chart image. -/
theorem mem_borderedZeroOneSobolevSections_iff_isZeroOneForm
    {w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k}
    {θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x}
    (hw : ∀ i : Fin A.n,
      (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
          (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ) :
    w ∈ borderedZeroOneSobolevSections A p k ↔
      ∀ i : Fin A.n, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
        (ofBorderedHolomorphic M).IsZeroOneForm
          (θ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))) := by
  rw [mem_borderedZeroOneSobolevSections_iff]
  refine forall_congr' fun i ↦ Filter.eventually_congr ?_
  filter_upwards [hw i, ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z h hz
  rw [h, A.isZeroOneForm_ofBorderedHolomorphic_iff_halfCoord_tangentHom i θ
    (A.mem_halfImage.1 hz).1]

/-- An element of `W^{k,p}` of `V`-valued one-forms whose chart data are the coordinates of a
`(0,1)`-form belongs to `borderedZeroOneSobolevSections A p k`. -/
theorem mem_borderedZeroOneSobolevSections_of_isZeroOneForm
    {w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k}
    {θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x}
    (hw : ∀ i : Fin A.n,
      (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
          (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ)
    (hθ : ∀ x, (ofBorderedHolomorphic M).IsZeroOneForm (θ x)) :
    w ∈ borderedZeroOneSobolevSections A p k :=
  (mem_borderedZeroOneSobolevSections_iff_isZeroOneForm hw).2 fun _ ↦
    Filter.Eventually.of_forall fun _ ↦ hθ _

/-- The `(0,1)`-forms over a Riemann surface with boundary form a closed subspace of
`BorderedSobolevSection`. -/
theorem isClosed_borderedZeroOneSobolevSections :
    IsClosed (borderedZeroOneSobolevSections A p k :
      Set (BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k)) :=
  SectionChartData.isClosed_antilinearSobolevSections

/-- **Completeness.** The Sobolev `(0,1)`-forms over a Riemann surface with boundary form a Banach
space. -/
instance borderedZeroOneSobolevSections.instCompleteSpace :
    CompleteSpace (borderedZeroOneSobolevSections A p k) :=
  SectionChartData.antilinearSobolevSections.instCompleteSpace

/-! ### The `(0,1)`-projection -/

variable (A p k) in
/-- **The `(0,1)`-projection.** The continuous projection of `W^{k,p}` of `V`-valued one-forms over
a Riemann surface with boundary onto `borderedZeroOneSobolevSections A p k`, applying
`ContinuousLinearMap.complexAntilinearPartL` to the chart data. It lifts the pointwise
`(0,1)`-projection `TauCeti.SmoothAlmostComplexStructure.zeroOnePart`
(`TauCeti.chartValueL_borderedZeroOnePartSobolevL_ae_halfCoord`) and fixes the `(0,1)`-forms
(`TauCeti.borderedZeroOnePartSobolevL_coe`). -/
def borderedZeroOnePartSobolevL :
    BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k →L[ℝ]
      borderedZeroOneSobolevSections A p k :=
  have (x : M) : ContinuousSMul ℂ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.antilinearPartSobolevL volume p k
    (fun θ x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x))
    (fun i θ _ hz ↦ halfSectionChartData_coord_zeroOnePart A i θ hz)

/-- The components of the `(0,1)`-projection of `w` are those of `w` transformed by the matrix of
`ContinuousLinearMap.complexAntilinearPartL`. -/
@[simp]
theorem coe_coe_borderedZeroOnePartSobolevL
    (w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) :
    ((borderedZeroOnePartSobolevL A p k w :
        BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) :
      (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.SobolevData volume p k) =
      (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.constMapData volume p k
        complexAntilinearPartL w :=
  SectionChartData.coe_coe_antilinearPartSobolevL _ _ w

/-- The chart data of the `(0,1)`-projection of `w` on `A.halfImage i` are the complex antilinear
parts of the chart data of `w`. -/
theorem chartValueL_borderedZeroOnePartSobolevL_ae
    (w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) (i : Fin A.n) :
    (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL volume p k i
        (borderedZeroOnePartSobolevL A p k w)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] fun z ↦
        complexAntilinearPartL
          ((A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL
            volume p k i w z) := by
  rw [borderedZeroOnePartSobolevL]
  exact (ae_restrict_halfSectionChartData_image_tangentHom_iff A).1
    (SectionChartData.chartValueL_antilinearPartSobolevL_ae _ _ w i)

/-- The `(0,1)`-projection of `w` vanishes iff the chart data of `w` are complex linear almost
everywhere on `A.halfImage i` for every chart `i`. -/
theorem borderedZeroOnePartSobolevL_eq_zero_iff
    {w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k} :
    borderedZeroOnePartSobolevL A p k w = 0 ↔
      ∀ i : Fin A.n, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ), ∀ v : ℂ,
        (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL
            volume p k i w z (Complex.I • v) =
          Complex.I •
            (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL
              volume p k i w z v :=
  have (x : M) : ContinuousSMul ℂ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  (SectionChartData.antilinearPartSobolevL_eq_zero_iff
    (fun θ x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x))
    (fun i θ _ hz ↦ halfSectionChartData_coord_zeroOnePart A i θ hz)).trans <|
      forall_congr' fun _ ↦ ae_restrict_halfSectionChartData_image_tangentHom_iff A

variable [∀ x, ContinuousSMul ℂ (V x)] in
/-- **Lifting the pointwise projection.** If the chart data of `w` in chart `i` equal the
coordinates `halfCoord` of a one-form `θ`, the chart data of its `(0,1)`-projection in chart `i`
equal the coordinates of the `(0,1)`-part of `θ`. -/
theorem chartValueL_borderedZeroOnePartSobolevL_ae_halfCoord
    {w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k}
    {θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x} {i : Fin A.n}
    (hw : (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ) :
    (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL volume p k i
        (borderedZeroOnePartSobolevL A p k w)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        (A.tangentHom closedUpperHalfPlaneModel).halfCoord i
          fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x) := by
  filter_upwards [chartValueL_borderedZeroOnePartSobolevL_ae w i, hw] with z h₁ h₂
  exact h₁.trans ((congrArg complexAntilinearPartL h₂).trans
    (A.halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart i θ z).symm)

/-- The `(0,1)`-projection fixes elements of `borderedZeroOneSobolevSections A p k`. -/
@[simp]
theorem borderedZeroOnePartSobolevL_coe (w : borderedZeroOneSobolevSections A p k) :
    borderedZeroOnePartSobolevL A p k w = w :=
  SectionChartData.antilinearPartSobolevL_coe _ _ w

/-- An element of `W^{k,p}` of `V`-valued one-forms is fixed by the `(0,1)`-projection iff it
belongs to `borderedZeroOneSobolevSections A p k`. -/
theorem coe_borderedZeroOnePartSobolevL_eq_self_iff
    {w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k} :
    (borderedZeroOnePartSobolevL A p k w :
        BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) = w ↔
      w ∈ borderedZeroOneSobolevSections A p k :=
  SectionChartData.coe_antilinearPartSobolevL_eq_self_iff _ _

/-- The `(0,1)`-projection is surjective onto `borderedZeroOneSobolevSections A p k`. -/
theorem borderedZeroOnePartSobolevL_surjective :
    Function.Surjective (borderedZeroOnePartSobolevL A p k) :=
  SectionChartData.antilinearPartSobolevL_surjective _ _

/-- **Complemented.** The `(0,1)`-forms are a complemented subspace of `W^{k,p}` of `V`-valued
one-forms over a Riemann surface with boundary. -/
theorem closedComplemented_borderedZeroOneSobolevSections :
    (borderedZeroOneSobolevSections A p k).ClosedComplemented :=
  ⟨borderedZeroOnePartSobolevL A p k, borderedZeroOnePartSobolevL_coe⟩

/-! ### Lowering the order -/

/-- Forgetting the highest derivative of a `(0,1)`-form gives a `(0,1)`-form. -/
theorem lowerOrderL_mem_borderedZeroOneSobolevSections
    {w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p (k + 1)}
    (hw : w ∈ borderedZeroOneSobolevSections A p (k + 1)) :
    (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.lowerOrderL volume p k w ∈
      borderedZeroOneSobolevSections A p k :=
  SectionChartData.lowerOrderL_mem_antilinearSobolevSections hw

variable (A p k) in
/-- The continuous inclusion of the bordered Sobolev `(0,1)`-forms of order `k + 1` into those of
order `k`. -/
def borderedZeroOneLowerOrderL :
    borderedZeroOneSobolevSections A p (k + 1) →L[ℝ] borderedZeroOneSobolevSections A p k :=
  (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.antilinearLowerOrderL volume p k

@[simp]
theorem coe_borderedZeroOneLowerOrderL (w : borderedZeroOneSobolevSections A p (k + 1)) :
    (borderedZeroOneLowerOrderL A p k w :
        BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) =
      (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.lowerOrderL volume p k w :=
  SectionChartData.coe_antilinearLowerOrderL w

/-- The `(0,1)`-projection commutes with forgetting the highest derivative. -/
theorem borderedZeroOneLowerOrderL_borderedZeroOnePartSobolevL
    (w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p (k + 1)) :
    borderedZeroOneLowerOrderL A p k (borderedZeroOnePartSobolevL A p (k + 1) w) =
      borderedZeroOnePartSobolevL A p k
        ((A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.lowerOrderL volume p k w) :=
  SectionChartData.antilinearLowerOrderL_antilinearPartSobolevL _ _ w

/-! ### Lowering the integrability exponent -/

section Exponent

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

variable (A k) in
/-- For `p ≤ q`, the continuous inclusion of the bordered Sobolev `(0,1)`-forms of exponent `q`
into those of exponent `p`. -/
def borderedZeroOneOfExponentLEL (hpq : p ≤ q) :
    borderedZeroOneSobolevSections A q k →L[ℝ] borderedZeroOneSobolevSections A p k :=
  (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.antilinearOfExponentLEL
    volume k hpq

@[simp]
theorem coe_borderedZeroOneOfExponentLEL (hpq : p ≤ q)
    (w : borderedZeroOneSobolevSections A q k) :
    (borderedZeroOneOfExponentLEL A k hpq w :
        BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) =
      (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.ofExponentLEL volume k hpq w :=
  SectionChartData.coe_antilinearOfExponentLEL hpq w

/-- Lowering the integrability exponent on bordered Sobolev `(0,1)`-forms is injective. -/
theorem borderedZeroOneOfExponentLEL_injective (hpq : p ≤ q) :
    Function.Injective (borderedZeroOneOfExponentLEL A k hpq) :=
  SectionChartData.antilinearOfExponentLEL_injective hpq

omit [Fact (1 ≤ q)] in
@[simp]
theorem borderedZeroOneOfExponentLEL_self (w : borderedZeroOneSobolevSections A p k) :
    borderedZeroOneOfExponentLEL A k le_rfl w = w :=
  SectionChartData.antilinearOfExponentLEL_self w

@[simp]
theorem borderedZeroOneOfExponentLEL_borderedZeroOneOfExponentLEL {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hpq : p ≤ q) (hqr : q ≤ r) (w : borderedZeroOneSobolevSections A r k) :
    borderedZeroOneOfExponentLEL A k hpq (borderedZeroOneOfExponentLEL A k hqr w) =
      borderedZeroOneOfExponentLEL A k (hpq.trans hqr) w :=
  SectionChartData.antilinearOfExponentLEL_antilinearOfExponentLEL hpq hqr w

/-- Lowering the exponent commutes with forgetting the highest derivative on bordered Sobolev
`(0,1)`-forms. -/
theorem borderedZeroOneLowerOrderL_borderedZeroOneOfExponentLEL (hpq : p ≤ q)
    (w : borderedZeroOneSobolevSections A q (k + 1)) :
    borderedZeroOneLowerOrderL A p k (borderedZeroOneOfExponentLEL A (k + 1) hpq w) =
      borderedZeroOneOfExponentLEL A k hpq (borderedZeroOneLowerOrderL A q k w) :=
  SectionChartData.antilinearLowerOrderL_antilinearOfExponentLEL hpq w

/-- Lowering the exponent commutes with the `(0,1)`-projection. -/
theorem borderedZeroOneOfExponentLEL_borderedZeroOnePartSobolevL (hpq : p ≤ q)
    (w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) q k) :
    borderedZeroOneOfExponentLEL A k hpq (borderedZeroOnePartSobolevL A q k w) =
      borderedZeroOnePartSobolevL A p k
        ((A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.ofExponentLEL
          volume k hpq w) :=
  SectionChartData.antilinearOfExponentLEL_antilinearPartSobolevL _ _ hpq w

end Exponent

/-! ### Multiplication by smooth real functions up to the boundary -/

section SMul

variable {φ ψ : M → ℝ}

variable (A p k) in
/-- Multiplication by a real function `φ : M → ℝ` smooth up to the boundary on the Sobolev
`(0,1)`-forms `borderedZeroOneSobolevSections A p k`. -/
def borderedZeroOneContMDiffSMulL (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ) :
    borderedZeroOneSobolevSections A p k →L[ℝ] borderedZeroOneSobolevSections A p k :=
  (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.antilinearSMulL
    (BorderedSobolevSection.contMDiffSMulL (A.tangentHom closedUpperHalfPlaneModel) p k hφ)
    (BorderedSobolevSection.chartValueL_contMDiffSMulL_ae hφ)

@[simp]
theorem coe_borderedZeroOneContMDiffSMulL (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : borderedZeroOneSobolevSections A p k) :
    (borderedZeroOneContMDiffSMulL A p k hφ w :
        BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) =
      BorderedSobolevSection.contMDiffSMulL (A.tangentHom closedUpperHalfPlaneModel) p k hφ w :=
  SectionChartData.coe_antilinearSMulL _ _ w

@[simp]
theorem borderedZeroOneContMDiffSMulL_const (c : ℝ) :
    borderedZeroOneContMDiffSMulL A p k (contMDiff_const (c := c)) =
      c • ContinuousLinearMap.id ℝ _ :=
  SectionChartData.antilinearSMulL_eq_const _ (BorderedSobolevSection.contMDiffSMulL_const c)

theorem borderedZeroOneContMDiffSMulL_add (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ ψ) :
    borderedZeroOneContMDiffSMulL A p k (hφ.add hψ) =
      borderedZeroOneContMDiffSMulL A p k hφ + borderedZeroOneContMDiffSMulL A p k hψ :=
  SectionChartData.antilinearSMulL_eq_add _ _ _ (BorderedSobolevSection.contMDiffSMulL_add hφ hψ)

theorem borderedZeroOneContMDiffSMulL_mul (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ ψ) :
    borderedZeroOneContMDiffSMulL A p k (hφ.mul hψ) =
      (borderedZeroOneContMDiffSMulL A p k hφ).comp (borderedZeroOneContMDiffSMulL A p k hψ) :=
  SectionChartData.antilinearSMulL_eq_comp _ _ _ (BorderedSobolevSection.contMDiffSMulL_mul hφ hψ)

/-- Smooth real multiplication up to the boundary commutes with forgetting the highest derivative
on `(0,1)`-forms. -/
theorem borderedZeroOneLowerOrderL_borderedZeroOneContMDiffSMulL
    (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : borderedZeroOneSobolevSections A p (k + 1)) :
    borderedZeroOneLowerOrderL A p k (borderedZeroOneContMDiffSMulL A p (k + 1) hφ w) =
      borderedZeroOneContMDiffSMulL A p k hφ (borderedZeroOneLowerOrderL A p k w) :=
  SectionChartData.antilinearLowerOrderL_antilinearSMulL _ _
    (BorderedSobolevSection.lowerOrderL_contMDiffSMulL hφ) w

/-- Smooth real multiplication up to the boundary commutes with the `(0,1)`-projection. -/
theorem borderedZeroOneContMDiffSMulL_borderedZeroOnePartSobolevL
    (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) :
    borderedZeroOneContMDiffSMulL A p k hφ (borderedZeroOnePartSobolevL A p k w) =
      borderedZeroOnePartSobolevL A p k
        (BorderedSobolevSection.contMDiffSMulL
          (A.tangentHom closedUpperHalfPlaneModel) p k hφ w) :=
  SectionChartData.antilinearSMulL_antilinearPartSobolevL _ _ _ _ w

end SMul

/-! ### Localization up to the real boundary -/

/-- **Localization up to the boundary.** Every element `w` of
`borderedZeroOneSobolevSections A p k` is represented by a global `(0,1)`-form `θ` on `M` (at
boundary points as well as interior points) whose chart expression
`(A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ` in every chart `i` lies in the local
Sobolev class `MemWkpLoc p (A.halfClosedImage i) k` on the full chart image in the closed upper
half-plane. -/
theorem exists_isZeroOneForm_memWkpLoc (w : borderedZeroOneSobolevSections A p k) :
    ∃ θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x,
      (∀ x, (ofBorderedHolomorphic M).IsZeroOneForm (θ x)) ∧
      (∀ i : Fin A.n, (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL
          volume p k i w
        =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
          (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ) ∧
      ∀ i : Fin A.n, MemWkpLoc p (A.halfClosedImage i) k
        ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ) := by
  have (x : M) : ContinuousSMul ℂ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  obtain ⟨θ₀, hθ₀, hloc₀⟩ := BorderedSobolevSection.exists_section_memWkpLoc w.1
  let θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x :=
    fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ₀ x)
  refine ⟨θ, fun x ↦ isZeroOneForm_zeroOnePart (θ₀ x), fun i ↦ ?_, fun i ↦ ?_⟩
  · have hproj := chartValueL_borderedZeroOnePartSobolevL_ae_halfCoord (w := w.1) (i := i)
      ((ae_restrict_halfImage_tangentHom_iff' A).1 (hθ₀ i))
    rwa [borderedZeroOnePartSobolevL_coe] at hproj
  · have hloc : MemWkpLoc p (A.halfClosedImage i) k
        ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ₀) := by
      simpa only [halfClosedImage_tangentHom] using hloc₀ i
    have heq : (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ =
        fun z ↦ complexAntilinearPartL
          ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ₀ z) :=
      funext (A.halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart i θ₀)
    rw [heq]
    exact hloc.clm_comp complexAntilinearPartL

end BorderedZeroOne

/-! ### `Cᵏ` `(0,1)`-forms up to the boundary and non-degeneracy -/

section RealChartZero

open FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) (k : ℕ)
  [ContMDiffVectorBundle k F V closedUpperHalfPlaneModel]

/-- If a continuous linear observable `L` vanishes almost everywhere on the interior `A.halfImage i`
along the chart reading of a `Cᵏ` one-form `θ`, then it vanishes at `A.chart i x` for every
`x ∈ A.dom i`, boundary points included. -/
private theorem clm_halfCoord_chart_eq_zero_of_ae_eq_zero
    (L : (ℂ →L[ℝ] F) →L[ℝ] (ℂ →L[ℝ] F))
    (θ : Cₛ^k⟮closedUpperHalfPlaneModel; ℂ →L[ℝ] F,
      fun x ↦ TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x⟯)
    (hae : ∀ i : Fin A.n, (fun z ↦ L ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ z))
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] 0)
    {i : Fin A.n} {x : M} (hx : x ∈ A.dom i) :
    L ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ (A.chart i x : ℂ)) = 0 := by
  let f : ℂ → ℂ →L[ℝ] F :=
    fun z ↦ L ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ z)
  have hcont : ContinuousOn f ((A.tangentHom closedUpperHalfPlaneModel).halfChartSet i) :=
    L.continuous.comp_continuousOn
      ((A.tangentHom closedUpperHalfPlaneModel).contDiffOn_halfCoord θ.contMDiff i).continuousOn
  have hae' : f =ᵐ[volume.restrict
      ((A.tangentHom closedUpperHalfPlaneModel).halfImage i : Set ℂ)] 0 :=
    (ae_restrict_halfImage_tangentHom_iff' A).2 (hae i)
  have hzero : EqOn f 0 ((A.tangentHom closedUpperHalfPlaneModel).halfImage i) :=
    Measure.eqOn_open_of_ae_eq hae'
      ((A.tangentHom closedUpperHalfPlaneModel).halfImage i).isOpen
      (hcont.mono ((A.tangentHom closedUpperHalfPlaneModel).halfImage_subset_halfChartSet i))
      continuousOn_const
  have hmem : (A.chart i x : ℂ) ∈ A.halfClosedImage i := by
    rw [halfClosedImage_eq_image_val]
    exact mem_image_of_mem _ (A.mem_image.2 ⟨x, hx, rfl⟩)
  have hK : (A.chart i x : ℂ) ∈ (A.tangentHom closedUpperHalfPlaneModel).halfChartSet i :=
    (A.tangentHom closedUpperHalfPlaneModel).extChartAt_image_closure_dom_subset_halfChartSet i
      ⟨x, subset_closure hx, A.extChartAt_center_apply i x⟩
  have hcl := ((hcont (A.chart i x : ℂ) hK).mono
    ((A.tangentHom closedUpperHalfPlaneModel).halfImage_subset_halfChartSet i)).mem_closure_image
      (by simpa only [halfImage_tangentHom] using A.halfClosedImage_subset_closure_halfImage i hmem)
  have himage : f '' (A.tangentHom closedUpperHalfPlaneModel).halfImage i ⊆ {0} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hzero hz
  have hval := closure_mono himage hcl
  rwa [closure_singleton, mem_singleton_iff] at hval

end RealChartZero

section Smooth

open FiniteBundleAtlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealBorderedZeroOneFormSmooth : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)
  [ContMDiffVectorBundle k F V closedUpperHalfPlaneModel]

variable {A p k} in
/-- **Smooth `(0,1)`-forms up to the boundary.** The Sobolev section of a `Cᵏ` one-form `θ` belongs
to `borderedZeroOneSobolevSections A p k` iff `θ` is a `(0,1)`-form at *every* point of `M`,
boundary points included. -/
theorem ofContMDiffSection_mem_borderedZeroOneSobolevSections_iff
    (θ : Cₛ^k⟮closedUpperHalfPlaneModel; ℂ →L[ℝ] F,
      fun x ↦ TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x⟯) :
    BorderedSobolevSection.ofContMDiffSection (A.tangentHom closedUpperHalfPlaneModel) p k θ ∈
        borderedZeroOneSobolevSections A p k ↔
      ∀ x, (ofBorderedHolomorphic M).IsZeroOneForm (θ x) := by
  have hchart (i : Fin A.n) :
      (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL volume p k i
          (BorderedSobolevSection.ofContMDiffSection (A.tangentHom closedUpperHalfPlaneModel) p k θ)
        =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
          (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ :=
    (ae_restrict_halfImage_tangentHom_iff' A).1 <|
      BorderedSobolevSection.chartValueL_ofContMDiffSection_ae
        (A.tangentHom closedUpperHalfPlaneModel) p k θ i
  refine ⟨fun hw x ↦ ?_, mem_borderedZeroOneSobolevSections_of_isZeroOneForm hchart⟩
  obtain ⟨i, hx⟩ := A.exists_mem_dom x
  let L : (ℂ →L[ℝ] F) →L[ℝ] (ℂ →L[ℝ] F) :=
    complexAntilinearPartL - ContinuousLinearMap.id ℝ (ℂ →L[ℝ] F)
  have hae (j : Fin A.n) :
      (fun z ↦ L ((A.tangentHom closedUpperHalfPlaneModel).halfCoord j θ z))
        =ᵐ[volume.restrict (A.halfImage j : Set ℂ)] 0 := by
    filter_upwards [hchart j, mem_borderedZeroOneSobolevSections_iff.1 hw j] with z hz h01
    simpa only [L, _root_.sub_apply, ContinuousLinearMap.id_apply, Pi.zero_apply, sub_eq_zero,
      complexAntilinearPartL_eq_self_iff, ← hz] using h01
  have hval := clm_halfCoord_chart_eq_zero_of_ae_eq_zero A k L θ hae hx
  rw [A.isZeroOneForm_ofBorderedHolomorphic_chart_iff_halfCoord θ hx]
  exact complexAntilinearPartL_eq_self_iff.1 (sub_eq_zero.1 hval)

variable {A p k} in
/-- The `(0,1)`-projection of the Sobolev section of a `Cᵏ` one-form `θ` vanishes iff `θ` is complex
linear (`θ x (j x v) = i • θ x v`) at *every* point of `M`, boundary points included. -/
theorem borderedZeroOnePartSobolevL_ofContMDiffSection_eq_zero_iff
    (θ : Cₛ^k⟮closedUpperHalfPlaneModel; ℂ →L[ℝ] F,
      fun x ↦ TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x⟯) :
    borderedZeroOnePartSobolevL A p k
        (BorderedSobolevSection.ofContMDiffSection
          (A.tangentHom closedUpperHalfPlaneModel) p k θ) = 0 ↔
      ∀ x (v : TangentSpace closedUpperHalfPlaneModel x),
        θ x (ofBorderedHolomorphic M x v) = Complex.I • θ x v := by
  have (x : M) : ContinuousSMul ℂ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  have hchart (i : Fin A.n) :
      (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL volume p k i
          (BorderedSobolevSection.ofContMDiffSection (A.tangentHom closedUpperHalfPlaneModel) p k θ)
        =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
          (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ :=
    (ae_restrict_halfImage_tangentHom_iff' A).1 <|
      BorderedSobolevSection.chartValueL_ofContMDiffSection_ae
        (A.tangentHom closedUpperHalfPlaneModel) p k θ i
  rw [borderedZeroOnePartSobolevL_eq_zero_iff]
  refine ⟨fun hw x ↦ zeroOnePart_eq_zero_iff.1 ?_, fun hθ i ↦ ?_⟩
  · obtain ⟨i, hx⟩ := A.exists_mem_dom x
    have hae (j : Fin A.n) :
        (fun z ↦ complexAntilinearPartL ((A.tangentHom closedUpperHalfPlaneModel).halfCoord j θ z))
          =ᵐ[volume.restrict (A.halfImage j : Set ℂ)] 0 := by
      filter_upwards [hchart j, hw j] with z hz hlin
      simpa only [Pi.zero_apply, complexAntilinearPartL_eq_zero_iff, ← hz] using hlin
    have hval := clm_halfCoord_chart_eq_zero_of_ae_eq_zero A k complexAntilinearPartL θ hae hx
    have hchart_val :
        (A.tangentHom closedUpperHalfPlaneModel).halfCoord i
            (fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x)) (A.chart i x : ℂ) =
          ((A.tangentHom closedUpperHalfPlaneModel).triv i
            ⟨x, (ofBorderedHolomorphic M).zeroOnePart (θ x)⟩).2 :=
      (A.tangentHom closedUpperHalfPlaneModel).halfCoord_coe_chart _ hx
    rw [← A.halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart i θ, hchart_val] at hval
    have hb := (A.tangentHom closedUpperHalfPlaneModel).dom_subset_baseSet i hx
    rwa [← (((A.tangentHom closedUpperHalfPlaneModel).triv i).continuousLinearEquivAt
      ℝ x hb).map_eq_zero_iff]
  · filter_upwards [hchart i, ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z hz hzmem
    let B := A.tangentHom closedUpperHalfPlaneModel
    let j : Fin B.n := i
    have hzB : closedUpperHalfPlaneModel.symm z ∈ B.image j :=
      (B.mem_halfImage.1 ((A.halfImage_tangentHom i).symm ▸ hzmem)).1
    have hzero : (fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x)) = 0 :=
      funext fun x ↦ zeroOnePart_eq_zero_iff.2 (hθ x)
    have h0 : complexAntilinearPartL (B.halfCoord j θ z) = 0 :=
      (A.halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart i θ z).symm.trans <|
        (congrArg (fun s ↦ B.halfCoord j s z) hzero).trans <|
          (B.halfCoord_def j 0 z).trans (B.coord_zero j hzB)
    intro v
    exact (congrArg (fun f : ℂ →L[ℝ] F ↦ f (Complex.I • v)) hz).trans <|
      (complexAntilinearPartL_eq_zero_iff.1 h0 v).trans
        (congrArg (fun f : ℂ →L[ℝ] F ↦ Complex.I • f v) hz.symm)

omit [FiniteDimensional ℝ F] in
variable (M F V) in
/-- The real submodule of `Cᵏ` one-forms up to the boundary consisting of pointwise `(0,1)`-forms
on `M`. -/
def isZeroOneFormContMDiffSubmodule :
    Submodule ℝ Cₛ^k⟮closedUpperHalfPlaneModel; ℂ →L[ℝ] F,
      fun x ↦ TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x⟯ where
  carrier := {θ | ∀ x, (ofBorderedHolomorphic M).IsZeroOneForm (θ x)}
  zero_mem' _ := by simp [isZeroOneForm_iff]
  add_mem' {θ₁ θ₂} h₁ h₂ x := isZeroOneForm_iff.2 fun v ↦ by
    simp only [ContMDiffSection.coe_add, Pi.add_apply, _root_.add_apply,
      isZeroOneForm_iff.1 (h₁ x) v, isZeroOneForm_iff.1 (h₂ x) v, smul_add, neg_add]
  smul_mem' c {θ} h x := isZeroOneForm_iff.2 fun v ↦ by
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply, _root_.smul_apply,
      isZeroOneForm_iff.1 (h x) v, smul_neg, smul_comm c Complex.I]

/-- **`Cᵏ` `(0,1)`-forms are Sobolev `(0,1)`-forms.** The linear map sending a `Cᵏ` `(0,1)`-form up
to the boundary to its class in `borderedZeroOneSobolevSections A p k`. -/
def borderedZeroOneOfContMDiffSection :
    isZeroOneFormContMDiffSubmodule M F V k →ₗ[ℝ] borderedZeroOneSobolevSections A p k :=
  ((BorderedSobolevSection.ofContMDiffSection
    (A.tangentHom closedUpperHalfPlaneModel) p k).comp
      (isZeroOneFormContMDiffSubmodule M F V k).subtype).codRestrict _
    fun θ ↦ (ofContMDiffSection_mem_borderedZeroOneSobolevSections_iff θ.1).2 θ.2

@[simp]
theorem coe_borderedZeroOneOfContMDiffSection
    (θ : isZeroOneFormContMDiffSubmodule M F V k) :
    (borderedZeroOneOfContMDiffSection A p k θ :
        BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) =
      BorderedSobolevSection.ofContMDiffSection
        (A.tangentHom closedUpperHalfPlaneModel) p k θ.1 :=
  LinearMap.codRestrict_apply _ _ _

/-- The chart data of `borderedZeroOneOfContMDiffSection A p k θ` on `A.halfImage i` equal the
coordinates `halfCoord` of `θ`. -/
theorem chartValueL_borderedZeroOneOfContMDiffSection_ae
    (θ : isZeroOneFormContMDiffSubmodule M F V k) (i : Fin A.n) :
    (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL volume p k i
        (borderedZeroOneOfContMDiffSection A p k θ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        (A.tangentHom closedUpperHalfPlaneModel).halfCoord i ⇑θ.1 := by
  rw [coe_borderedZeroOneOfContMDiffSection]
  exact (ae_restrict_halfImage_tangentHom_iff' A).1 <|
    BorderedSobolevSection.chartValueL_ofContMDiffSection_ae
      (A.tangentHom closedUpperHalfPlaneModel) p k θ.1 i

/-- **Norm bound.** The norm of `borderedZeroOneOfContMDiffSection A p k θ` is bounded by the sum
of the `Lᵖ` norms on `A.halfImage i` of the classical derivatives of orders `0` through `k` of the
chart components of `θ`. -/
theorem norm_borderedZeroOneOfContMDiffSection_le
    (θ : isZeroOneFormContMDiffSubmodule M F V k) :
    ‖borderedZeroOneOfContMDiffSection A p k θ‖ ≤
      ∑ i : Fin A.n, ∑ j, ∑ l ∈ Finset.range (k + 1),
        lpNorm (iteratedFDeriv ℝ l fun z ↦ (finBasis ℝ (ℂ →L[ℝ] F)).coord j
          ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i ⇑θ.1 z)) p
            (volume.restrict (A.halfImage i : Set ℂ)) :=
  calc ‖borderedZeroOneOfContMDiffSection A p k θ‖
      = ‖BorderedSobolevSection.ofContMDiffSection
          (A.tangentHom closedUpperHalfPlaneModel) p k θ.1‖ :=
        (Submodule.norm_coe _).trans
          (congrArg Norm.norm (coe_borderedZeroOneOfContMDiffSection A p k θ))
    _ ≤ _ := BorderedSobolevSection.norm_ofContMDiffSection_le
          (A.tangentHom closedUpperHalfPlaneModel) p k θ.1
    _ = _ := Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun _ _ ↦
          Finset.sum_congr rfl fun _ _ ↦
            congrArg (fun U : Opens ℂ ↦ lpNorm _ p (volume.restrict (U : Set ℂ)))
              (A.halfImage_tangentHom i)

/-- **Injectivity.** Two `Cᵏ` `(0,1)`-forms up to the boundary defining the same Sobolev
`(0,1)`-form are equal everywhere on `M`, boundary points included. -/
theorem borderedZeroOneOfContMDiffSection_injective :
    Function.Injective (borderedZeroOneOfContMDiffSection A p k) := fun _ _ h ↦
  Subtype.ext <| BorderedSobolevSection.ofContMDiffSection_injective
    (A.tangentHom closedUpperHalfPlaneModel) p k <| by
      simpa only [coe_borderedZeroOneOfContMDiffSection] using congrArg Subtype.val h

/-! #### Concrete witness: the closed annulus -/

section ClosedAnnulusCheck

-- Verify simultaneously on the closed annulus `Complex.closedAnnulus r₁ r₂` with its trivial
-- complex line bundle that a finite bundle atlas exists and that all hypotheses of the Banach
-- space, complementedness, and `Cᵏ` embedding theorems are inhabited.
private example (r₁ r₂ : ℝ) [hr₁ : Fact (0 < r₁)] [hr₁₂ : Fact (r₁ < r₂)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ) :
    ∃ A : FiniteBundleAtlas ClosedUpperHalfPlane (Complex.closedAnnulus r₁ r₂) ℂ
        (Bundle.Trivial (Complex.closedAnnulus r₁ r₂) ℂ),
      CompleteSpace (borderedZeroOneSobolevSections A p k) ∧
      (borderedZeroOneSobolevSections A p k).ClosedComplemented ∧
      Function.Injective (borderedZeroOneOfContMDiffSection A p k) := by
  let M := Complex.closedAnnulus r₁ r₂
  have : LocallyCompactSpace ClosedUpperHalfPlane :=
    (isClosed_le continuous_const Complex.continuous_im).locallyCompactSpace
  have : Nonempty M := ⟨⟨(r₁ : ℂ), Complex.mem_closedAnnulus.2
    ⟨by simp [abs_of_pos hr₁.out], by simp [abs_of_pos hr₁.out, hr₁₂.out.le]⟩⟩⟩
  obtain ⟨A⟩ := FiniteBundleAtlas.nonempty (E := ClosedUpperHalfPlane) (M := M) (F := ℂ)
    (V := Bundle.Trivial M ℂ)
  exact ⟨A, inferInstance, closedComplemented_borderedZeroOneSobolevSections,
    borderedZeroOneOfContMDiffSection_injective A p k⟩

end ClosedAnnulusCheck

end Smooth

end TauCeti
