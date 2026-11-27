/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Geometry.Manifold.Complex.BorderedHolomorphic.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Antilinear
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.SMul
public import TauCeti.Topology.VectorBundle.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Bordered

/-!
# Sobolev `(0,1)`-forms over a Riemann surface with boundary

Let `M` be a Riemann surface with boundary modelled on `ClosedUpperHalfPlane` with transitions in
`TauCeti.borderedHolomorphicGroupoid`, and let `V → M` be a complex vector bundle with
finite-dimensional fibre `F`, regarded as a real bundle. For the canonical almost complex structure
`TauCeti.SmoothAlmostComplexStructure.ofBorderedHolomorphic M`, we construct
`W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)` as a closed complemented Banach subspace
`TauCeti.borderedZeroOneSobolevSections A p k` of
`TauCeti.BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k`.

By `TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Bordered`, in every chart `i`, the
`(0,1)`-part is read in `ℂ` as `ContinuousLinearMap.complexAntilinearPartL`
(`TauCeti.FiniteBundleAtlas.halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart`), and a
one-form is a `(0,1)`-form on `A.dom i` (boundary included) iff its reading is complex antilinear
(`TauCeti.FiniteBundleAtlas.isZeroOneForm_ofBorderedHolomorphic_chart_iff_halfCoord`). Instantiating
the `SectionChartData` theory of `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Antilinear` on
`(A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData` yields
`TauCeti.borderedZeroOnePartSobolevL`, `TauCeti.borderedZeroOneLowerOrdersL`,
`TauCeti.borderedZeroOneOfExponentLEL`, and `TauCeti.borderedZeroOneContMDiffSMulL`. We also prove:
* **Smooth `(0,1)`-forms up to the boundary**
  (`TauCeti.ofContMDiffSection_mem_borderedZeroOneSobolevSections_iff`,
  `TauCeti.borderedZeroOneOfContMDiffSection`): a `Cᵏ` one-form defines a Sobolev `(0,1)`-form iff
  it is `(0,1)` at every point of `M` (boundary included), and similarly for vanishing of the
  `(0,1)`-projection (`TauCeti.borderedZeroOnePartSobolevL_ofContMDiffSection_eq_zero_iff`).
* **Localization up to the boundary** (`TauCeti.exists_isZeroOneForm_memWkpLoc_halfCoord`): every
  element is represented by a global `(0,1)`-form whose readings lie in `MemWkpLoc`.

## Main definitions

* `TauCeti.borderedZeroOneSobolevSections`, `TauCeti.borderedZeroOnePartSobolevL`,
  `TauCeti.borderedZeroOneLowerOrdersL`, `TauCeti.borderedZeroOneOfExponentLEL`,
  `TauCeti.borderedZeroOneContMDiffSMulL`, `TauCeti.borderedZeroOneOfContMDiffSection`.

## Main results

* `TauCeti.mem_borderedZeroOneSobolevSections_iff`,
  `TauCeti.mem_borderedZeroOneSobolevSections_iff_isZeroOneForm`,
  `TauCeti.isClosed_borderedZeroOneSobolevSections`,
  `TauCeti.borderedZeroOneSobolevSections.instCompleteSpace`,
  `TauCeti.closedComplemented_borderedZeroOneSobolevSections`.
* `TauCeti.borderedZeroOneLowerOrdersL_injective`,
  `TauCeti.borderedZeroOneOfExponentLEL_injective`.
* `TauCeti.ofContMDiffSection_mem_borderedZeroOneSobolevSections_iff`,
  `TauCeti.borderedZeroOnePartSobolevL_ofContMDiffSection_eq_zero_iff`,
  `TauCeti.borderedZeroOneOfContMDiffSection_injective`.
* `TauCeti.exists_isZeroOneForm_memWkpLoc_halfCoord`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., §2.4, C.1–C.2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL complexAntilinearPartL_eq_self_iff
  complexAntilinearPartL_eq_zero_iff)
open scoped Manifold ENNReal ContDiff

namespace TauCeti

open SmoothAlmostComplexStructure

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

variable [∀ x, ContinuousSMul ℂ (V x)] in
omit [FiniteDimensional ℝ F] in
private theorem halfSectionChartData_coord_zeroOnePart
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
  rw [borderedZeroOneSobolevSections]
  conv_rhs =>
    ext i
    rw [← A.halfImage_tangentHom i,
      ← (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData_image i]
  exact SectionChartData.mem_antilinearSobolevSections_iff

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
  (mem_borderedZeroOneSobolevSections_iff_isZeroOneForm hw).2 fun _ ↦ .of_forall fun _ ↦ hθ _

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
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
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
  rw [← A.halfImage_tangentHom i,
    ← (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData_image i]
  exact SectionChartData.chartValueL_antilinearPartSobolevL_ae _ _ w i

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
              volume p k i w z v := by
  conv_rhs =>
    ext i
    rw [← A.halfImage_tangentHom i,
      ← (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData_image i]
  exact SectionChartData.antilinearPartSobolevL_eq_zero_iff _ _

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
@[simp]
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

/-- Forgetting derivatives preserves the bordered `(0,1)` condition. -/
theorem lowerOrdersL_mem_borderedZeroOneSobolevSections (d : ℕ)
    {w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p (k + d)}
    (hw : w ∈ borderedZeroOneSobolevSections A p (k + d)) :
    (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.lowerOrdersL volume p k d w ∈
      borderedZeroOneSobolevSections A p k :=
  SectionChartData.lowerOrdersL_mem_antilinearSobolevSections d hw

variable (A p k) in
/-- The continuous inclusion of the bordered Sobolev `(0,1)`-forms of order `k + d` into those of
order `k`. -/
def borderedZeroOneLowerOrdersL (d : ℕ) :
    borderedZeroOneSobolevSections A p (k + d) →L[ℝ] borderedZeroOneSobolevSections A p k :=
  (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.antilinearLowerOrdersL
    volume p k d

/-- As a function, the bordered order inclusion is the restriction of the canonical order map. -/
theorem coeFn_borderedZeroOneLowerOrdersL_eq_codRestrict (d : ℕ) :
    ⇑(borderedZeroOneLowerOrdersL A p k d) =
      Set.codRestrict
        (⇑((A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.lowerOrdersL
            volume p k d) ∘
          ⇑(borderedZeroOneSobolevSections A p (k + d)).subtypeL)
        (borderedZeroOneSobolevSections A p k)
        (fun w ↦ lowerOrdersL_mem_borderedZeroOneSobolevSections d w.property) :=
  funext fun w ↦ Subtype.ext (SectionChartData.coe_antilinearLowerOrdersL d w)

/-- The inclusion acts by the canonical order inclusion on the underlying one-form. -/
@[simp]
theorem coe_borderedZeroOneLowerOrdersL (d : ℕ)
    (w : borderedZeroOneSobolevSections A p (k + d)) :
    (borderedZeroOneLowerOrdersL A p k d w :
        BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) =
      (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.lowerOrdersL
        volume p k d w :=
  SectionChartData.coe_antilinearLowerOrdersL d w

/-- Forgetting zero derivatives is the identity. -/
@[simp]
theorem borderedZeroOneLowerOrdersL_zero (w : borderedZeroOneSobolevSections A p k) :
    borderedZeroOneLowerOrdersL A p k 0 w = w :=
  SectionChartData.antilinearLowerOrdersL_zero w

omit k in
/-- Coercion to one-forms commutes with equality transport of the Sobolev order. -/
@[simp]
theorem coe_borderedZeroOneSobolevSections_eqRec {a b : ℕ} (h : a = b)
    (w : borderedZeroOneSobolevSections A p a) :
    ((h ▸ w : borderedZeroOneSobolevSections A p b) :
        BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p b) =
      h ▸ (w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p a) :=
  SectionChartData.coe_antilinearSobolevSections_eqRec h w

/-- Bordered order inclusions compose, with the source order reassociated by `Nat.add_assoc`. -/
@[simp]
theorem borderedZeroOneLowerOrdersL_borderedZeroOneLowerOrdersL (d e : ℕ)
    (w : borderedZeroOneSobolevSections A p ((k + d) + e)) :
    borderedZeroOneLowerOrdersL A p k d (borderedZeroOneLowerOrdersL A p (k + d) e w) =
      borderedZeroOneLowerOrdersL A p k (d + e) ((Nat.add_assoc k d e) ▸ w) :=
  SectionChartData.antilinearLowerOrdersL_antilinearLowerOrdersL d e w

/-- Forgetting `d + 1` derivatives first forgets the highest derivative. -/
theorem borderedZeroOneLowerOrdersL_succ (d : ℕ) :
    borderedZeroOneLowerOrdersL A p k (d + 1) =
      (borderedZeroOneLowerOrdersL A p k d).comp (borderedZeroOneLowerOrdersL A p (k + d) 1) :=
  SectionChartData.antilinearLowerOrdersL_succ d

/-- The bordered order inclusion is injective. -/
theorem borderedZeroOneLowerOrdersL_injective (d : ℕ) :
    Function.Injective (borderedZeroOneLowerOrdersL A p k d) :=
  SectionChartData.antilinearLowerOrdersL_injective d

/-- The `(0,1)`-projection commutes with forgetting derivatives. -/
theorem borderedZeroOneLowerOrdersL_borderedZeroOnePartSobolevL (d : ℕ)
    (w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p (k + d)) :
    borderedZeroOneLowerOrdersL A p k d (borderedZeroOnePartSobolevL A p (k + d) w) =
      borderedZeroOnePartSobolevL A p k
        ((A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.lowerOrdersL
          volume p k d w) :=
  SectionChartData.antilinearLowerOrdersL_antilinearPartSobolevL d _ _ w

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

/-- Lowering the exponent commutes with forgetting derivatives on bordered Sobolev
`(0,1)`-forms. -/
theorem borderedZeroOneLowerOrdersL_borderedZeroOneOfExponentLEL (d : ℕ) (hpq : p ≤ q)
    (w : borderedZeroOneSobolevSections A q (k + d)) :
    borderedZeroOneLowerOrdersL A p k d (borderedZeroOneOfExponentLEL A (k + d) hpq w) =
      borderedZeroOneOfExponentLEL A k hpq (borderedZeroOneLowerOrdersL A q k d w) :=
  SectionChartData.antilinearLowerOrdersL_antilinearOfExponentLEL d hpq w

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
  (BorderedSobolevSection.contMDiffSMulL _ p k hφ).restrict fun _ ↦
    SectionChartData.mem_antilinearSobolevSections_of_chartValueL_ae_smul
      (BorderedSobolevSection.chartValueL_contMDiffSMulL_ae hφ)

@[simp]
theorem coe_borderedZeroOneContMDiffSMulL (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : borderedZeroOneSobolevSections A p k) :
    (borderedZeroOneContMDiffSMulL A p k hφ w :
        BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) =
      BorderedSobolevSection.contMDiffSMulL (A.tangentHom closedUpperHalfPlaneModel) p k hφ w :=
  ContinuousLinearMap.coe_restrict_apply _ w

@[simp]
theorem borderedZeroOneContMDiffSMulL_const (c : ℝ) :
    borderedZeroOneContMDiffSMulL A p k (contMDiff_const (c := c)) =
      c • ContinuousLinearMap.id ℝ _ := by
  ext1 w
  apply Subtype.ext
  simp

theorem borderedZeroOneContMDiffSMulL_add (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ ψ) :
    borderedZeroOneContMDiffSMulL A p k (hφ.add hψ) =
      borderedZeroOneContMDiffSMulL A p k hφ + borderedZeroOneContMDiffSMulL A p k hψ := by
  ext1 w
  apply Subtype.ext
  simp [BorderedSobolevSection.contMDiffSMulL_add hφ hψ]

theorem borderedZeroOneContMDiffSMulL_mul (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ ψ) :
    borderedZeroOneContMDiffSMulL A p k (hφ.mul hψ) =
      (borderedZeroOneContMDiffSMulL A p k hφ).comp (borderedZeroOneContMDiffSMulL A p k hψ) := by
  ext1 w
  apply Subtype.ext
  simp [BorderedSobolevSection.contMDiffSMulL_mul hφ hψ]

/-- Smooth real multiplication up to the boundary commutes with forgetting derivatives on
`(0,1)`-forms. -/
theorem borderedZeroOneLowerOrdersL_borderedZeroOneContMDiffSMulL (d : ℕ)
    (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : borderedZeroOneSobolevSections A p (k + d)) :
    borderedZeroOneLowerOrdersL A p k d (borderedZeroOneContMDiffSMulL A p (k + d) hφ w) =
      borderedZeroOneContMDiffSMulL A p k hφ (borderedZeroOneLowerOrdersL A p k d w) :=
  SectionChartData.antilinearLowerOrdersL_restrict d
    (fun m ↦ BorderedSobolevSection.contMDiffSMulL _ p m hφ)
    (fun _ _ ↦
      SectionChartData.mem_antilinearSobolevSections_of_chartValueL_ae_smul
        (BorderedSobolevSection.chartValueL_contMDiffSMulL_ae hφ))
    (fun _ ↦ BorderedSobolevSection.lowerOrderL_contMDiffSMulL hφ) w

/-- Smooth real multiplication up to the boundary commutes with the `(0,1)`-projection. -/
theorem borderedZeroOneContMDiffSMulL_borderedZeroOnePartSobolevL
    (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) ∞ φ)
    (w : BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) :
    borderedZeroOneContMDiffSMulL A p k hφ (borderedZeroOnePartSobolevL A p k w) =
      borderedZeroOnePartSobolevL A p k (BorderedSobolevSection.contMDiffSMulL _ p k hφ w) :=
  SectionChartData.restrict_antilinearPartSobolevL_of_chartValueL_ae_smul
    (BorderedSobolevSection.chartValueL_contMDiffSMulL_ae hφ) _ _ w

end SMul

/-! ### Localization up to the real boundary -/

/-- **Localization up to the boundary.** Every element `w` of
`borderedZeroOneSobolevSections A p k` is represented by a global `(0,1)`-form `θ` on `M` (at
boundary points as well as interior points) whose chart expression
`(A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ` in every chart `i` lies in the local
Sobolev class `MemWkpLoc p (A.halfClosedImage i) k` on the full chart image in the closed upper
half-plane. -/
theorem exists_isZeroOneForm_memWkpLoc_halfCoord (w : borderedZeroOneSobolevSections A p k) :
    ∃ θ : ∀ x, TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x,
      (∀ x, (ofBorderedHolomorphic M).IsZeroOneForm (θ x)) ∧
      (∀ i : Fin A.n, (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL
          volume p k i w =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
          (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ) ∧
      ∀ i : Fin A.n, MemWkpLoc p (A.halfClosedImage i) k
        ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ) := by
  obtain ⟨θ₀, hθ₀, hloc₀⟩ := BorderedSobolevSection.exists_section_memWkpLoc w.val
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  refine ⟨fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ₀ x),
    fun x ↦ isZeroOneForm_zeroOnePart (θ₀ x), fun i ↦ ?_, fun i ↦ ?_⟩
  · have hproj := chartValueL_borderedZeroOnePartSobolevL_ae_halfCoord (w := w.val)
      (by simpa only [halfImage_tangentHom] using hθ₀ i)
    rwa [borderedZeroOnePartSobolevL_coe] at hproj
  · have hloc : MemWkpLoc p (A.halfClosedImage i) k
        ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ₀) := by
      simpa only [halfClosedImage_tangentHom] using hloc₀ i
    rw [funext (A.halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart i θ₀)]
    exact hloc.clm_comp complexAntilinearPartL

end BorderedZeroOne

/-! ### `Cᵏ` `(0,1)`-forms up to the boundary and non-degeneracy -/

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

variable {A} in
private theorem chartValueL_ofContMDiffSection_halfCoord
    (θ : Cₛ^k⟮closedUpperHalfPlaneModel; ℂ →L[ℝ] F,
      fun x ↦ TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x⟯) (i : Fin A.n) :
    (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL volume p k i
        (BorderedSobolevSection.ofContMDiffSection
          (A.tangentHom closedUpperHalfPlaneModel) p k θ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        (A.tangentHom closedUpperHalfPlaneModel).halfCoord i θ := by
  simpa only [halfImage_tangentHom] using
    BorderedSobolevSection.chartValueL_ofContMDiffSection_ae
      (A.tangentHom closedUpperHalfPlaneModel) p k θ i

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
  let B := A.tangentHom closedUpperHalfPlaneModel
  refine ⟨fun hw x ↦ ?_, mem_borderedZeroOneSobolevSections_of_isZeroOneForm
    (chartValueL_ofContMDiffSection_halfCoord p k θ)⟩
  obtain ⟨i, hx⟩ := A.exists_mem_dom x
  let L : (ℂ →L[ℝ] F) →L[ℝ] (ℂ →L[ℝ] F) :=
    complexAntilinearPartL - ContinuousLinearMap.id ℝ (ℂ →L[ℝ] F)
  have hae : (fun z ↦ L (B.halfCoord i θ z)) =ᵐ[volume.restrict (B.halfImage i : Set ℂ)] 0 := by
    rw [A.halfImage_tangentHom i]
    filter_upwards [chartValueL_ofContMDiffSection_halfCoord p k θ i,
      mem_borderedZeroOneSobolevSections_iff.1 hw i] with z hz h01
    simpa only [L, B, _root_.sub_apply, ContinuousLinearMap.id_apply, Pi.zero_apply, sub_eq_zero,
      complexAntilinearPartL_eq_self_iff, ← hz] using h01
  have hval : L (B.halfCoord i θ (A.chart i x : ℂ)) = 0 :=
    B.continuous_comp_halfCoord_coe_chart_eq_zero_of_ae_eq_zero L.continuous
      θ.contMDiff.continuous hx hae
  rw [A.isZeroOneForm_ofBorderedHolomorphic_chart_iff_halfCoord θ hx]
  exact complexAntilinearPartL_eq_self_iff.1 (sub_eq_zero.1 hval)

variable {A p k} in
/-- The `(0,1)`-projection of the Sobolev section of a `Cᵏ` one-form `θ` vanishes iff `θ` is complex
linear (`θ x (j x v) = i • θ x v`) at *every* point of `M`, boundary points included. -/
theorem borderedZeroOnePartSobolevL_ofContMDiffSection_eq_zero_iff
    (θ : Cₛ^k⟮closedUpperHalfPlaneModel; ℂ →L[ℝ] F,
      fun x ↦ TangentSpace closedUpperHalfPlaneModel x →L[ℝ] V x⟯) :
    borderedZeroOnePartSobolevL A p k (BorderedSobolevSection.ofContMDiffSection _ p k θ) = 0 ↔
      ∀ x (v : TangentSpace closedUpperHalfPlaneModel x),
        θ x (ofBorderedHolomorphic M x v) = Complex.I • θ x v := by
  have : ∀ x, ContinuousSMul ℂ (V x) := VectorBundle.continuousSMul ℂ F V
  let B := A.tangentHom closedUpperHalfPlaneModel
  refine ⟨fun hw x ↦ ?_, fun hθ ↦ Subtype.ext ?_⟩
  · obtain ⟨i, hx⟩ := A.exists_mem_dom x
    have hae : (fun z ↦ complexAntilinearPartL (B.halfCoord i θ z))
        =ᵐ[volume.restrict (B.halfImage i : Set ℂ)] 0 := by
      rw [A.halfImage_tangentHom i]
      filter_upwards [chartValueL_ofContMDiffSection_halfCoord p k θ i,
        borderedZeroOnePartSobolevL_eq_zero_iff.1 hw i] with z hz hlin
      simpa only [B, Pi.zero_apply, complexAntilinearPartL_eq_zero_iff, ← hz] using hlin
    have hval : complexAntilinearPartL (B.halfCoord i θ (A.chart i x : ℂ)) = 0 :=
      B.continuous_comp_halfCoord_coe_chart_eq_zero_of_ae_eq_zero
        complexAntilinearPartL.continuous θ.contMDiff.continuous hx hae
    have hchart_val : B.halfCoord i (fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x))
        (A.chart i x : ℂ) = (B.triv i ⟨x, (ofBorderedHolomorphic M).zeroOnePart (θ x)⟩).snd :=
      B.halfCoord_coe_chart _ hx
    rw [← A.halfCoord_tangentHom_ofBorderedHolomorphic_zeroOnePart i θ, hchart_val] at hval
    exact zeroOnePart_eq_zero_iff.1 <|
      (((B.triv i).continuousLinearEquivAt ℝ x (B.dom_subset_baseSet i hx)).map_eq_zero_iff).1 hval
  · have hzero : (fun x ↦ (ofBorderedHolomorphic M).zeroOnePart (θ x)) = 0 :=
      funext fun x ↦ zeroOnePart_eq_zero_iff.2 (hθ x)
    refine BorderedSobolevSection.eq_of_ae_eq_halfCoord (s := 0) (fun i ↦ ?_) fun i ↦ ?_
    · rw [A.halfImage_tangentHom i]
      exact (chartValueL_borderedZeroOnePartSobolevL_ae_halfCoord
        (chartValueL_ofContMDiffSection_halfCoord p k θ i)).trans
          (.of_eq (congrArg (B.halfCoord i) hzero))
    · simpa only [ZeroMemClass.coe_zero, map_zero, ContMDiffSection.coe_zero] using
        BorderedSobolevSection.chartValueL_ofContMDiffSection_ae B p k 0 i

/-- **`Cᵏ` `(0,1)`-forms are Sobolev `(0,1)`-forms.** The linear map sending a `Cᵏ` `(0,1)`-form up
to the boundary to its class in `borderedZeroOneSobolevSections A p k`. -/
def borderedZeroOneOfContMDiffSection :
    (ofBorderedHolomorphic M).zeroOneContMDiffSections F V k →ₗ[ℝ]
      borderedZeroOneSobolevSections A p k :=
  (BorderedSobolevSection.ofContMDiffSection (A.tangentHom closedUpperHalfPlaneModel) p k).restrict
    fun θ hθ ↦ (ofContMDiffSection_mem_borderedZeroOneSobolevSections_iff θ).2
      (mem_zeroOneContMDiffSections_iff.1 hθ)

@[simp]
theorem coe_borderedZeroOneOfContMDiffSection
    (θ : (ofBorderedHolomorphic M).zeroOneContMDiffSections F V k) :
    (borderedZeroOneOfContMDiffSection A p k θ :
        BorderedSobolevSection (A.tangentHom closedUpperHalfPlaneModel) p k) =
      BorderedSobolevSection.ofContMDiffSection
        (A.tangentHom closedUpperHalfPlaneModel) p k θ.val :=
  LinearMap.coe_restrict_apply _ θ

/-- The chart data of `borderedZeroOneOfContMDiffSection A p k θ` on `A.halfImage i` equal the
coordinates `halfCoord` of `θ`. -/
theorem chartValueL_borderedZeroOneOfContMDiffSection_ae
    (θ : (ofBorderedHolomorphic M).zeroOneContMDiffSections F V k) (i : Fin A.n) :
    (A.tangentHom closedUpperHalfPlaneModel).halfSectionChartData.chartValueL volume p k i
        (borderedZeroOneOfContMDiffSection A p k θ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        (A.tangentHom closedUpperHalfPlaneModel).halfCoord i ⇑θ.val := by
  simpa only [coe_borderedZeroOneOfContMDiffSection, ← A.halfImage_tangentHom] using
    BorderedSobolevSection.chartValueL_ofContMDiffSection_ae
      (A.tangentHom closedUpperHalfPlaneModel) p k θ.val i

/-- **Norm bound.** The norm of `borderedZeroOneOfContMDiffSection A p k θ` is bounded by the sum
of the `Lᵖ` norms on `A.halfImage i` of the classical derivatives of orders `0` through `k` of the
chart components of `θ`. -/
theorem norm_borderedZeroOneOfContMDiffSection_le
    (θ : (ofBorderedHolomorphic M).zeroOneContMDiffSections F V k) :
    ‖borderedZeroOneOfContMDiffSection A p k θ‖ ≤
      ∑ i : Fin A.n, ∑ j, ∑ l ∈ Finset.range (k + 1),
        lpNorm (iteratedFDeriv ℝ l fun z ↦ (finBasis ℝ (ℂ →L[ℝ] F)).coord j
          ((A.tangentHom closedUpperHalfPlaneModel).halfCoord i ⇑θ.val z)) p
            (volume.restrict (A.halfImage i : Set ℂ)) := by
  refine (Submodule.norm_coe _).symm.le.trans ?_
  rw [coe_borderedZeroOneOfContMDiffSection]
  simp_rw [← A.halfImage_tangentHom]
  exact BorderedSobolevSection.norm_ofContMDiffSection_le _ p k θ.val

/-- **Injectivity.** Two `Cᵏ` `(0,1)`-forms up to the boundary defining the same Sobolev
`(0,1)`-form are equal everywhere on `M`, boundary points included. -/
theorem borderedZeroOneOfContMDiffSection_injective :
    Function.Injective (borderedZeroOneOfContMDiffSection A p k) := fun _ _ h ↦
  Subtype.ext <| BorderedSobolevSection.ofContMDiffSection_injective _ p k <| by
    simpa only [coe_borderedZeroOneOfContMDiffSection] using congrArg Subtype.val h

end Smooth

end TauCeti
