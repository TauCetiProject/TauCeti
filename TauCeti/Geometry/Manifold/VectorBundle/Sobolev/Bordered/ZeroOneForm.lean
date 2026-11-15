/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Tangent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.SMul
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent
public import TauCeti.Topology.VectorBundle.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.FixedSubmodule

/-!
# Sobolev `(0,1)`-forms over a Riemann surface with boundary

Let `M` be a Riemann surface with boundary, a charted space modelled on `ClosedUpperHalfPlane`
with transitions in `TauCeti.borderedHolomorphicGroupoid`, and let `V → M` be a complex vector
bundle with finite-dimensional model fibre `F`, regarded as a real vector bundle. A `V`-valued
one-form `η : T_x M → V x` is a `(0,1)`-form when it is complex antilinear for the induced almost
complex structure `TauCeti.SmoothAlmostComplexStructure.ofBorderedHolomorphic M`, `η (i v) =
-(i • η v)` (`TauCeti.SmoothAlmostComplexStructure.IsZeroOneForm`). This file constructs the
target space `W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)` of real Cauchy–Riemann operators over a surface with
boundary as a closed, complete, complemented subspace of the bordered Sobolev space
`TauCeti.BorderedSobolevSection A.halfTangentHom p k` of `V`-valued one-forms, built on the charts
of a finite bundle atlas `A` of `V`.

In chart `i`, sections are read on the interior `A.halfImage i` of the planar chart image
`A.halfClosedImage i`, which differs from `A.halfClosedImage i` by a subset of the real axis, a
Lebesgue null set. Because `ofBorderedHolomorphic M` reads as multiplication by `i` in the tangent
coordinates of every chart up to and including the real axis, a one-form is a `(0,1)`-form on the
chart image exactly when its planar reading `η : ℂ →L[ℝ] F` is complex antilinear, and the
`(0,1)`-projection `η ↦ ½ (η + i • η ∘ i)` acts on chart readings as the constant idempotent
operator `ContinuousLinearMap.complexAntilinearPartL`
(`TauCeti.FiniteBundleAtlas.isZeroOneForm_iff_halfCoord_halfTangentHom`,
`TauCeti.FiniteBundleAtlas.halfCoord_halfTangentHom_zeroOnePart`). Specializing
`TauCeti.SectionChartData.fixedSubmodule` and `TauCeti.SectionChartData.projFixedL` to
`A.halfTangentHom.halfSectionChartData` yields:

* the Banach space `TauCeti.borderedZeroOneSobolevSections A p k` and the continuous retraction
  `TauCeti.borderedZeroOnePartSobolevL A p k`, proving
  `TauCeti.closedComplemented_borderedZeroOneSobolevSections`;
* localization up to the boundary (`TauCeti.exists_isZeroOneForm_memWkpLoc`): every element is
  represented by a global `(0,1)`-form — complex antilinear at boundary points as well as interior
  points — whose planar chart expression lies in `MemWkpLoc p (A.halfClosedImage i) k`;
* the order inclusion `TauCeti.borderedZeroOneLowerOrderL`, the exponent inclusion
  `TauCeti.borderedZeroOneOfExponentLEL`, and multiplication by smooth real-valued functions up to
  the boundary `TauCeti.borderedZeroOneContMDiffSMulL`, together with their compatibilities with
  `borderedZeroOnePartSobolevL`.

## Main definitions

* `TauCeti.borderedZeroOneSobolevSections A p k`: the `(0,1)`-forms in
  `BorderedSobolevSection A.halfTangentHom p k`.
* `TauCeti.borderedZeroOnePartSobolevL`: the continuous `(0,1)`-projection onto it.
* `TauCeti.borderedZeroOneLowerOrderL`: the inclusion of order `k + 1` into order `k`.
* `TauCeti.borderedZeroOneOfExponentLEL`: the inclusion of exponent `q` into exponent `p` for
  `p ≤ q`.
* `TauCeti.borderedZeroOneContMDiffSMulL`: multiplication by a smooth function `φ : M → ℝ`.

## Main results

* `TauCeti.mem_borderedZeroOneSobolevSections_iff`,
  `TauCeti.mem_borderedZeroOneSobolevSections_iff_isZeroOneForm`,
  `TauCeti.mem_borderedZeroOneSobolevSections_of_isZeroOneForm`: characterizations by chart data
  and by pointwise `(0,1)`-forms.
* `TauCeti.isClosed_borderedZeroOneSobolevSections`,
  `TauCeti.borderedZeroOneSobolevSections.instCompleteSpace`,
  `TauCeti.closedComplemented_borderedZeroOneSobolevSections`: closedness, completeness, and
  complementation.
* `TauCeti.chartValueL_borderedZeroOnePartSobolevL_ae`,
  `TauCeti.borderedZeroOnePartSobolevL_eq_zero_iff`,
  `TauCeti.chartValueL_borderedZeroOnePartSobolevL_ae_halfCoord`,
  `TauCeti.borderedZeroOnePartSobolevL_coe`: chart action, kernel, lifting of the pointwise
  `(0,1)`-projection, and retraction property.
* `TauCeti.exists_isZeroOneForm_memWkpLoc`: representation by a global `(0,1)`-form with local
  Sobolev regularity up to the real boundary.
* `TauCeti.borderedZeroOneLowerOrderL_borderedZeroOnePartSobolevL`,
  `TauCeti.borderedZeroOneOfExponentLEL_borderedZeroOnePartSobolevL`,
  `TauCeti.borderedZeroOneContMDiffSMulL_borderedZeroOnePartSobolevL`: the `(0,1)`-projection
  commutes with order lowering, exponent lowering, and smooth multiplication.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.4, Appendix B.1, and Appendix C.1.
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL complexAntilinearPartL_complexAntilinearPartL
  complexAntilinearPartL_eq_self_iff complexAntilinearPartL_eq_zero_iff)
open scoped Manifold ENNReal ContDiff

namespace TauCeti

open SmoothAlmostComplexStructure

section BorderedZeroOne

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [HasGroupoid M borderedHolomorphicGroupoid]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealBorderedZeroOneForm : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-! ### The bordered Sobolev space of `(0,1)`-forms -/

/-- The `(0,1)`-forms in the bordered Sobolev space `W^{k,p}` of `V`-valued one-forms over a
Riemann surface with boundary, the space `W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)`: the elements whose chart data
are complex antilinear almost everywhere on the interior `A.halfImage i` of every chart image
(`TauCeti.mem_borderedZeroOneSobolevSections_iff`). -/
def borderedZeroOneSobolevSections :
    Submodule ℝ (BorderedSobolevSection A.halfTangentHom p k) :=
  A.halfTangentHom.halfSectionChartData.fixedSubmodule volume p k complexAntilinearPartL

variable {A p k}

omit [FiniteDimensional ℝ F] in
private theorem ae_restrict_halfTangentHom
    (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) (i : Fin A.n) :
    ae (volume.restrict (A.halfTangentHom.halfSectionChartData.image i : Set ℂ)) =
      ae (volume.restrict (A.halfImage i : Set ℂ)) :=
  congrArg (fun U : Opens ℂ ↦ ae (volume.restrict (U : Set ℂ)))
    (A.halfImage_halfTangentHom i)

/-- An element of `BorderedSobolevSection A.halfTangentHom p k` belongs to
`borderedZeroOneSobolevSections A p k` if and only if its chart data are complex antilinear almost
everywhere on `A.halfImage i` for every chart `i`. -/
theorem mem_borderedZeroOneSobolevSections_iff
    {w : BorderedSobolevSection A.halfTangentHom p k} :
    w ∈ borderedZeroOneSobolevSections A p k ↔
      ∀ i, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ), ∀ v : ℂ,
        A.halfTangentHom.halfSectionChartData.chartValueL volume p k i w z (Complex.I • v) =
          -(Complex.I • A.halfTangentHom.halfSectionChartData.chartValueL volume p k i w z v) := by
  refine SectionChartData.mem_fixedSubmodule_iff.trans (forall_congr' fun i ↦ ?_)
  rw [ae_restrict_halfTangentHom A i]
  exact Filter.eventually_congr
    (Filter.Eventually.of_forall fun _ ↦ complexAntilinearPartL_eq_self_iff)

/-- An element whose chart data equal the planar readings of a one-form `θ` almost everywhere on
`A.halfImage i` belongs to `borderedZeroOneSobolevSections A p k` if and only if `θ` is a
`(0,1)`-form almost everywhere in every chart. -/
theorem mem_borderedZeroOneSobolevSections_iff_isZeroOneForm
    {w : BorderedSobolevSection A.halfTangentHom p k}
    {θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x}
    (hw : ∀ i, A.halfTangentHom.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfTangentHom.halfCoord i θ) :
    w ∈ borderedZeroOneSobolevSections A p k ↔
      ∀ i, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
        (ofBorderedHolomorphic M).IsZeroOneForm
          (θ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))) := by
  rw [mem_borderedZeroOneSobolevSections_iff]
  refine forall_congr' fun i ↦ Filter.eventually_congr ?_
  filter_upwards [hw i, ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z h hz
  rw [h, A.isZeroOneForm_iff_halfCoord_halfTangentHom i θ (A.mem_halfImage.1 hz).1]

/-- An element whose chart data equal the planar readings of a `(0,1)`-form almost everywhere on
`A.halfImage i` belongs to `borderedZeroOneSobolevSections A p k`. -/
theorem mem_borderedZeroOneSobolevSections_of_isZeroOneForm
    {w : BorderedSobolevSection A.halfTangentHom p k}
    {θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x}
    (hw : ∀ i, A.halfTangentHom.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfTangentHom.halfCoord i θ)
    (hθ : ∀ x, (ofBorderedHolomorphic M).IsZeroOneForm (θ x)) :
    w ∈ borderedZeroOneSobolevSections A p k :=
  (mem_borderedZeroOneSobolevSections_iff_isZeroOneForm hw).2 fun _ ↦
    Filter.Eventually.of_forall fun _ ↦ hθ _

/-- `borderedZeroOneSobolevSections A p k` is closed in
`BorderedSobolevSection A.halfTangentHom p k`. -/
theorem isClosed_borderedZeroOneSobolevSections :
    IsClosed (borderedZeroOneSobolevSections A p k :
      Set (BorderedSobolevSection A.halfTangentHom p k)) :=
  A.halfTangentHom.halfSectionChartData.isClosed_fixedSubmodule volume p k complexAntilinearPartL

variable (A p k) in
/-- Normed additive group structure on `borderedZeroOneSobolevSections A p k`, registered directly
on the head symbol so continuous linear operator spaces on `borderedZeroOneSobolevSections A p k` do
not time out searching across nested `Submodule` coercions. -/
noncomputable instance borderedZeroOneSobolevSections.instNormedAddCommGroup :
    NormedAddCommGroup (borderedZeroOneSobolevSections A p k) :=
  Submodule.normedAddCommGroup _

variable (A p k) in
/-- Real normed space structure on `borderedZeroOneSobolevSections A p k`. -/
noncomputable instance borderedZeroOneSobolevSections.instNormedSpace :
    NormedSpace ℝ (borderedZeroOneSobolevSections A p k) :=
  Submodule.normedSpace _

/-- **Completeness.** The bordered Sobolev `(0,1)`-forms form a Banach space. -/
instance borderedZeroOneSobolevSections.instCompleteSpace :
    CompleteSpace (borderedZeroOneSobolevSections A p k) :=
  isClosed_borderedZeroOneSobolevSections.completeSpace_coe

/-! ### The `(0,1)`-projection -/

variable (F) in
omit [FiniteDimensional ℝ F] in
private def borderedZeroOnePartSection
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) :
    ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x :=
  letI (x' : M) : ContinuousSMul ℂ (V x') :=
    (VectorBundle.continuousLinearEquivAt ℂ F V x').continuousSMul
  fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x)

omit [FiniteDimensional ℝ F] in
private theorem halfSectionChartData_coord_zeroOnePart
    (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) (i : Fin A.n)
    (θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x) (z : ℂ) :
    A.halfTangentHom.halfSectionChartData.coord i (borderedZeroOnePartSection F θ) z =
      complexAntilinearPartL (A.halfTangentHom.halfSectionChartData.coord i θ z) :=
  letI (x : M) : ContinuousSMul ℂ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  have h : A.halfTangentHom.halfCoord i (borderedZeroOnePartSection F θ) =
      complexAntilinearPartL ∘ A.halfTangentHom.halfCoord i θ :=
    funext (A.halfCoord_halfTangentHom_zeroOnePart i θ)
  (congrFun (congrArg (indicator _) h) z).trans
    (congrFun (indicator_comp_of_zero complexAntilinearPartL.map_zero) z)

variable (A p k) in
/-- **The `(0,1)`-projection.** The continuous projection of
`BorderedSobolevSection A.halfTangentHom p k` onto `borderedZeroOneSobolevSections A p k`, applying
`η ↦ ½ (η + i • η ∘ i)` to the chart data. It lifts the pointwise `(0,1)`-projection
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart`
(`TauCeti.chartValueL_borderedZeroOnePartSobolevL_ae_halfCoord`) and fixes the `(0,1)`-forms
(`TauCeti.borderedZeroOnePartSobolevL_coe`). -/
def borderedZeroOnePartSobolevL :
    BorderedSobolevSection A.halfTangentHom p k →L[ℝ] borderedZeroOneSobolevSections A p k :=
  A.halfTangentHom.halfSectionChartData.projFixedL volume p k
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ z _ ↦ halfSectionChartData_coord_zeroOnePart A i θ z)

/-- The components of `borderedZeroOnePartSobolevL A p k w` are those of `w` transformed by the
matrix of `ContinuousLinearMap.complexAntilinearPartL`. -/
@[simp]
theorem coe_coe_borderedZeroOnePartSobolevL (w : BorderedSobolevSection A.halfTangentHom p k) :
    ((borderedZeroOnePartSobolevL A p k w : BorderedSobolevSection A.halfTangentHom p k) :
        A.halfTangentHom.halfSectionChartData.SobolevData volume p k) =
      A.halfTangentHom.halfSectionChartData.constMapData volume p k complexAntilinearPartL w :=
  A.halfTangentHom.halfSectionChartData.coe_coe_projFixedL
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ z _ ↦ halfSectionChartData_coord_zeroOnePart A i θ z) w

/-- The chart data of `borderedZeroOnePartSobolevL A p k w` are the complex antilinear parts of
those of `w`, almost everywhere on `A.halfImage i`. -/
theorem chartValueL_borderedZeroOnePartSobolevL_ae
    (w : BorderedSobolevSection A.halfTangentHom p k) (i : Fin A.n) :
    A.halfTangentHom.halfSectionChartData.chartValueL volume p k i
        (borderedZeroOnePartSobolevL A p k w)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] fun z ↦
        complexAntilinearPartL
          (A.halfTangentHom.halfSectionChartData.chartValueL volume p k i w z) := by
  rw [borderedZeroOnePartSobolevL, ← ae_restrict_halfTangentHom A i]
  exact A.halfTangentHom.halfSectionChartData.chartValueL_projFixedL_ae
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ z _ ↦ halfSectionChartData_coord_zeroOnePart A i θ z) w i

/-- `borderedZeroOnePartSobolevL A p k w` vanishes if and only if the chart data of `w` are complex
linear almost everywhere on `A.halfImage i` for every chart `i`. -/
theorem borderedZeroOnePartSobolevL_eq_zero_iff
    {w : BorderedSobolevSection A.halfTangentHom p k} :
    borderedZeroOnePartSobolevL A p k w = 0 ↔
      ∀ i, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ), ∀ v : ℂ,
        A.halfTangentHom.halfSectionChartData.chartValueL volume p k i w z (Complex.I • v) =
          Complex.I • A.halfTangentHom.halfSectionChartData.chartValueL volume p k i w z v := by
  refine (A.halfTangentHom.halfSectionChartData.projFixedL_eq_zero_iff volume p k
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ z _ ↦ halfSectionChartData_coord_zeroOnePart A i θ z)).trans (forall_congr' fun i ↦ ?_)
  rw [ae_restrict_halfTangentHom A i]
  exact Filter.eventually_congr
    (Filter.Eventually.of_forall fun _ ↦ complexAntilinearPartL_eq_zero_iff)

variable [∀ x, ContinuousSMul ℂ (V x)] in
/-- **Lifting the pointwise projection.** If the chart data of `w` in chart `i` are the planar
readings of a one-form `θ`, then the chart data of `borderedZeroOnePartSobolevL A p k w` in chart
`i` are the planar readings of the `(0,1)`-part of `θ`. -/
theorem chartValueL_borderedZeroOnePartSobolevL_ae_halfCoord
    {w : BorderedSobolevSection A.halfTangentHom p k}
    {θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x} {i : Fin A.n}
    (hw : A.halfTangentHom.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfTangentHom.halfCoord i θ) :
    A.halfTangentHom.halfSectionChartData.chartValueL volume p k i
        (borderedZeroOnePartSobolevL A p k w)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        A.halfTangentHom.halfCoord i fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x) := by
  filter_upwards [chartValueL_borderedZeroOnePartSobolevL_ae w i, hw] with z hz hwz
  rw [hz, hwz, ← A.halfCoord_halfTangentHom_zeroOnePart i θ z]

/-- The `(0,1)`-projection fixes every element of `borderedZeroOneSobolevSections A p k`. -/
@[simp]
theorem borderedZeroOnePartSobolevL_coe (w : borderedZeroOneSobolevSections A p k) :
    borderedZeroOnePartSobolevL A p k w = w :=
  A.halfTangentHom.halfSectionChartData.projFixedL_coe
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ z _ ↦ halfSectionChartData_coord_zeroOnePart A i θ z) w

/-- An element of `BorderedSobolevSection A.halfTangentHom p k` is fixed by the `(0,1)`-projection
if and only if it belongs to `borderedZeroOneSobolevSections A p k`. -/
theorem coe_borderedZeroOnePartSobolevL_eq_self_iff
    {w : BorderedSobolevSection A.halfTangentHom p k} :
    (borderedZeroOnePartSobolevL A p k w : BorderedSobolevSection A.halfTangentHom p k) = w ↔
      w ∈ borderedZeroOneSobolevSections A p k :=
  A.halfTangentHom.halfSectionChartData.coe_projFixedL_eq_self_iff volume p k
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ z _ ↦ halfSectionChartData_coord_zeroOnePart A i θ z)

/-- The `(0,1)`-projection is surjective onto `borderedZeroOneSobolevSections A p k`. -/
theorem borderedZeroOnePartSobolevL_surjective :
    Function.Surjective (borderedZeroOnePartSobolevL A p k) :=
  A.halfTangentHom.halfSectionChartData.projFixedL_surjective volume p k
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ z _ ↦ halfSectionChartData_coord_zeroOnePart A i θ z)

/-- **Complemented subspace.** The `(0,1)`-forms are a complemented subspace of
`BorderedSobolevSection A.halfTangentHom p k`, with `borderedZeroOnePartSobolevL A p k` as a
continuous linear retraction. -/
theorem closedComplemented_borderedZeroOneSobolevSections :
    (borderedZeroOneSobolevSections A p k).ClosedComplemented :=
  ⟨borderedZeroOnePartSobolevL A p k, borderedZeroOnePartSobolevL_coe⟩

/-! ### Localization to the local Sobolev classes up to the boundary -/

/-- **Localization up to the boundary.** Every element of `borderedZeroOneSobolevSections A p k` is
represented by a global `(0,1)`-form `θ` — complex antilinear at boundary points as well as
interior points — whose planar expression `A.halfTangentHom.halfCoord i θ` in every chart `i` lies
in the local Sobolev class `MemWkpLoc p (A.halfClosedImage i) k` up to the real axis. -/
theorem exists_isZeroOneForm_memWkpLoc (w : borderedZeroOneSobolevSections A p k) :
    ∃ θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x,
      (∀ x, (ofBorderedHolomorphic M).IsZeroOneForm (θ x)) ∧
      (∀ i, A.halfTangentHom.halfSectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfTangentHom.halfCoord i θ) ∧
      ∀ i, MemWkpLoc p (A.halfClosedImage i) k (A.halfTangentHom.halfCoord i θ) := by
  have _ (x : M) : ContinuousSMul ℂ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  obtain ⟨θ₀, hθ₀⟩ := A.halfTangentHom.halfSectionChartData.exists_section volume p k
    (w : BorderedSobolevSection A.halfTangentHom p k)
  let θ := borderedZeroOnePartSection F θ₀
  have hθ_ae (i : Fin A.n) :
      A.halfTangentHom.halfSectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.halfTangentHom.halfImage i : Set ℂ)]
          A.halfTangentHom.halfCoord i θ := by
    have hw_eq : (borderedZeroOnePartSobolevL A p k w :
        BorderedSobolevSection A.halfTangentHom p k) = w :=
      congrArg Subtype.val (borderedZeroOnePartSobolevL_coe w)
    rw [← hw_eq]
    exact (A.halfTangentHom.halfSectionChartData.chartValueL_projFixedL_ae_coord
      (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
      (fun i θ z _ ↦ halfSectionChartData_coord_zeroOnePart A i θ z) (hθ₀ i)).trans
      (A.halfTangentHom.halfSectionChartData_coord_ae_eq i θ)
  refine ⟨θ, fun x ↦ (ofBorderedHolomorphic M).isZeroOneForm_zeroOnePart (θ₀ x),
    fun i ↦ ?_, fun i ↦ ?_⟩
  · simpa only [A.halfImage_halfTangentHom i] using hθ_ae i
  · simpa only [A.halfClosedImage_halfTangentHom i] using
      BorderedSobolevSection.memWkpLoc_halfCoord
        (w : BorderedSobolevSection A.halfTangentHom p k) hθ_ae i

/-! ### Lowering the Sobolev order -/

/-- Forgetting the highest derivative of a bordered Sobolev `(0,1)`-form gives a `(0,1)`-form. -/
theorem lowerOrderL_mem_borderedZeroOneSobolevSections
    {w : BorderedSobolevSection A.halfTangentHom p (k + 1)}
    (hw : w ∈ borderedZeroOneSobolevSections A p (k + 1)) :
    A.halfTangentHom.halfSectionChartData.lowerOrderL volume p k w ∈
      borderedZeroOneSobolevSections A p k :=
  SectionChartData.lowerOrderL_mem_fixedSubmodule hw

variable (A p k) in
/-- The continuous inclusion of `borderedZeroOneSobolevSections A p (k + 1)` into
`borderedZeroOneSobolevSections A p k`. -/
def borderedZeroOneLowerOrderL :
    borderedZeroOneSobolevSections A p (k + 1) →L[ℝ] borderedZeroOneSobolevSections A p k :=
  A.halfTangentHom.halfSectionChartData.fixedLowerOrderL volume p k complexAntilinearPartL

@[simp]
theorem coe_borderedZeroOneLowerOrderL (w : borderedZeroOneSobolevSections A p (k + 1)) :
    (borderedZeroOneLowerOrderL A p k w : BorderedSobolevSection A.halfTangentHom p k) =
      A.halfTangentHom.halfSectionChartData.lowerOrderL volume p k w :=
  SectionChartData.coe_fixedLowerOrderL _ w

/-- The `(0,1)`-projection commutes with lowering the Sobolev order. -/
theorem borderedZeroOneLowerOrderL_borderedZeroOnePartSobolevL
    (w : BorderedSobolevSection A.halfTangentHom p (k + 1)) :
    borderedZeroOneLowerOrderL A p k (borderedZeroOnePartSobolevL A p (k + 1) w) =
      borderedZeroOnePartSobolevL A p k
        (A.halfTangentHom.halfSectionChartData.lowerOrderL volume p k w) :=
  A.halfTangentHom.halfSectionChartData.fixedLowerOrderL_projFixedL
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ z _ ↦ halfSectionChartData_coord_zeroOnePart A i θ z) w

/-! ### Lowering the integrability exponent -/

section Exponent

variable {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- Lowering the integrability exponent of a bordered Sobolev `(0,1)`-form gives a
`(0,1)`-form. -/
theorem ofExponentLEL_mem_borderedZeroOneSobolevSections (hpq : p ≤ q)
    {w : BorderedSobolevSection A.halfTangentHom q k}
    (hw : w ∈ borderedZeroOneSobolevSections A q k) :
    A.halfTangentHom.halfSectionChartData.ofExponentLEL volume k hpq w ∈
      borderedZeroOneSobolevSections A p k :=
  SectionChartData.ofExponentLEL_mem_fixedSubmodule hpq hw

variable (A k) in
/-- For `p ≤ q`, the continuous inclusion of `borderedZeroOneSobolevSections A q k` into
`borderedZeroOneSobolevSections A p k`. -/
def borderedZeroOneOfExponentLEL (hpq : p ≤ q) :
    borderedZeroOneSobolevSections A q k →L[ℝ] borderedZeroOneSobolevSections A p k :=
  A.halfTangentHom.halfSectionChartData.fixedOfExponentLEL volume k complexAntilinearPartL hpq

@[simp]
theorem coe_borderedZeroOneOfExponentLEL (hpq : p ≤ q)
    (w : borderedZeroOneSobolevSections A q k) :
    (borderedZeroOneOfExponentLEL A k hpq w : BorderedSobolevSection A.halfTangentHom p k) =
      A.halfTangentHom.halfSectionChartData.ofExponentLEL volume k hpq w :=
  SectionChartData.coe_fixedOfExponentLEL _ hpq w

/-- Lowering the integrability exponent on `borderedZeroOneSobolevSections` is injective. -/
theorem borderedZeroOneOfExponentLEL_injective (hpq : p ≤ q) :
    Function.Injective (borderedZeroOneOfExponentLEL A k hpq) :=
  SectionChartData.fixedOfExponentLEL_injective _ hpq

@[simp]
theorem borderedZeroOneOfExponentLEL_self (w : borderedZeroOneSobolevSections A p k) :
    borderedZeroOneOfExponentLEL A k le_rfl w = w :=
  SectionChartData.fixedOfExponentLEL_self _ w

@[simp]
theorem borderedZeroOneOfExponentLEL_borderedZeroOneOfExponentLEL (hpq : p ≤ q) (hqr : q ≤ r)
    (w : borderedZeroOneSobolevSections A r k) :
    borderedZeroOneOfExponentLEL A k hpq (borderedZeroOneOfExponentLEL A k hqr w) =
      borderedZeroOneOfExponentLEL A k (hpq.trans hqr) w :=
  SectionChartData.fixedOfExponentLEL_fixedOfExponentLEL _ hpq hqr w

/-- Lowering the integrability exponent commutes with lowering the Sobolev order on bordered
`(0,1)`-forms. -/
theorem borderedZeroOneLowerOrderL_borderedZeroOneOfExponentLEL (hpq : p ≤ q)
    (w : borderedZeroOneSobolevSections A q (k + 1)) :
    borderedZeroOneLowerOrderL A p k (borderedZeroOneOfExponentLEL A (k + 1) hpq w) =
      borderedZeroOneOfExponentLEL A k hpq (borderedZeroOneLowerOrderL A q k w) :=
  SectionChartData.fixedLowerOrderL_fixedOfExponentLEL _ hpq w

/-- The `(0,1)`-projection commutes with lowering the integrability exponent. -/
theorem borderedZeroOneOfExponentLEL_borderedZeroOnePartSobolevL (hpq : p ≤ q)
    (w : BorderedSobolevSection A.halfTangentHom q k) :
    borderedZeroOneOfExponentLEL A k hpq (borderedZeroOnePartSobolevL A q k w) =
      borderedZeroOnePartSobolevL A p k
        (A.halfTangentHom.halfSectionChartData.ofExponentLEL volume k hpq w) :=
  A.halfTangentHom.halfSectionChartData.fixedOfExponentLEL_projFixedL
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ z _ ↦ halfSectionChartData_coord_zeroOnePart A i θ z) hpq w

end Exponent

/-! ### Smooth scalar multiplication -/

section SMul

variable {φ ψ : M → ℝ}

/-- Multiplying a bordered Sobolev `(0,1)`-form by a smooth function `φ : M → ℝ` gives a
`(0,1)`-form. -/
theorem contMDiffSMulL_mem_borderedZeroOneSobolevSections
    (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    {w : BorderedSobolevSection A.halfTangentHom p k}
    (hw : w ∈ borderedZeroOneSobolevSections A p k) :
    BorderedSobolevSection.contMDiffSMulL A.halfTangentHom p k hφ w ∈
      borderedZeroOneSobolevSections A p k :=
  SectionChartData.smulEnd_mem_fixedSubmodule
    (BorderedSobolevSection.chartValueL_contMDiffSMulL_ae hφ) hw

variable (A p k) in
/-- Multiplication by a smooth function `φ : M → ℝ` up to the boundary as a continuous linear
endomorphism of `borderedZeroOneSobolevSections A p k`. -/
def borderedZeroOneContMDiffSMulL (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ) :
    borderedZeroOneSobolevSections A p k →L[ℝ] borderedZeroOneSobolevSections A p k :=
  A.halfTangentHom.halfSectionChartData.fixedSMulEndL volume p k complexAntilinearPartL
    (BorderedSobolevSection.contMDiffSMulL A.halfTangentHom p k hφ)
    (BorderedSobolevSection.chartValueL_contMDiffSMulL_ae hφ)

@[simp]
theorem coe_borderedZeroOneContMDiffSMulL (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : borderedZeroOneSobolevSections A p k) :
    (borderedZeroOneContMDiffSMulL A p k hφ w : BorderedSobolevSection A.halfTangentHom p k) =
      BorderedSobolevSection.contMDiffSMulL A.halfTangentHom p k hφ w :=
  SectionChartData.coe_fixedSMulEndL _ _ _ w

@[simp]
theorem borderedZeroOneContMDiffSMulL_const (c : ℝ) :
    borderedZeroOneContMDiffSMulL A p k (contMDiff_const (c := c)) =
      c • ContinuousLinearMap.id ℝ _ :=
  SectionChartData.fixedSMulEndL_eq_smul_id _ _ _
    (BorderedSobolevSection.contMDiffSMulL_const (A := A.halfTangentHom) (p := p) (k := k) c)

/-- Smooth multiplication on `borderedZeroOneSobolevSections` is additive in the multiplier. -/
theorem borderedZeroOneContMDiffSMulL_add (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ ψ) :
    borderedZeroOneContMDiffSMulL A p k (hφ.add hψ) =
      borderedZeroOneContMDiffSMulL A p k hφ + borderedZeroOneContMDiffSMulL A p k hψ :=
  SectionChartData.fixedSMulEndL_eq_add _ _ _ _
    (BorderedSobolevSection.contMDiffSMulL_add (A := A.halfTangentHom) (p := p) (k := k) hφ hψ)

/-- Smooth multiplication on `borderedZeroOneSobolevSections` sends products to compositions. -/
theorem borderedZeroOneContMDiffSMulL_mul (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ ψ) :
    borderedZeroOneContMDiffSMulL A p k (hφ.mul hψ) =
      (borderedZeroOneContMDiffSMulL A p k hφ).comp
        (borderedZeroOneContMDiffSMulL A p k hψ) :=
  SectionChartData.fixedSMulEndL_eq_comp _ _ _ _
    (BorderedSobolevSection.contMDiffSMulL_mul (A := A.halfTangentHom) (p := p) (k := k) hφ hψ)

/-- Lowering the Sobolev order commutes with smooth multiplication on bordered `(0,1)`-forms. -/
theorem borderedZeroOneLowerOrderL_borderedZeroOneContMDiffSMulL
    (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : borderedZeroOneSobolevSections A p (k + 1)) :
    borderedZeroOneLowerOrderL A p k (borderedZeroOneContMDiffSMulL A p (k + 1) hφ w) =
      borderedZeroOneContMDiffSMulL A p k hφ (borderedZeroOneLowerOrderL A p k w) :=
  SectionChartData.fixedLowerOrderL_fixedSMulEndL _ _ _ w

/-- Lowering the integrability exponent commutes with smooth multiplication on bordered
`(0,1)`-forms. -/
theorem borderedZeroOneOfExponentLEL_borderedZeroOneContMDiffSMulL {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : borderedZeroOneSobolevSections A q k) :
    borderedZeroOneOfExponentLEL A k hpq (borderedZeroOneContMDiffSMulL A q k hφ w) =
      borderedZeroOneContMDiffSMulL A p k hφ (borderedZeroOneOfExponentLEL A k hpq w) :=
  SectionChartData.fixedOfExponentLEL_fixedSMulEndL _ hpq _ _ w

/-- The `(0,1)`-projection commutes with multiplication by a smooth real-valued function up to the
boundary. -/
theorem borderedZeroOneContMDiffSMulL_borderedZeroOnePartSobolevL
    (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : BorderedSobolevSection A.halfTangentHom p k) :
    borderedZeroOneContMDiffSMulL A p k hφ (borderedZeroOnePartSobolevL A p k w) =
      borderedZeroOnePartSobolevL A p k
        (BorderedSobolevSection.contMDiffSMulL A.halfTangentHom p k hφ w) :=
  A.halfTangentHom.halfSectionChartData.fixedSMulEndL_projFixedL
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ z _ ↦ halfSectionChartData_coord_zeroOnePart A i θ z) _ _ w

end SMul

end BorderedZeroOne

end TauCeti
