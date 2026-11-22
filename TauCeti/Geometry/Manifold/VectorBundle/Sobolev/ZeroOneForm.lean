/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Antilinear
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.SMul
public import TauCeti.Topology.VectorBundle.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart

/-!
# Sobolev `(0,1)`-forms over a complex curve

Let `M` be a boundaryless complex curve (modelled on `ℂ`) and `V → M` a complex vector bundle
with finite-dimensional fibre `F`, regarded as a real bundle. A `V`-valued one-form
`η : T_x M → V x` is a `(0,1)`-form when `η (i v) = -(i • η v)`
(`TauCeti.SmoothAlmostComplexStructure.IsZeroOneForm` for `ofComplexManifold ℂ M`). We construct
`W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)` as a closed complemented Banach subspace of
`TauCeti.SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k` for a finite bundle atlas `A` of `V`.

Instantiating the chart-data theory of `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Antilinear`
on `(A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData` and using
`TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Chart` yields
`TauCeti.zeroOneSobolevSections A μ p k`, `TauCeti.zeroOnePartSobolevL`,
`TauCeti.zeroOneLowerOrdersL`, `TauCeti.zeroOneOfExponentLEL`, and `TauCeti.zeroOneContMDiffSMulL`.

## Main definitions

* `TauCeti.zeroOneSobolevSections`, `TauCeti.zeroOnePartSobolevL`, `TauCeti.zeroOneLowerOrdersL`,
  `TauCeti.zeroOneOfExponentLEL`, `TauCeti.zeroOneContMDiffSMulL`: native `(0,1)`-forms,
  `(0,1)`-projection, order/exponent inclusions, and multiplication by smooth real functions.

## Main results

* `TauCeti.FiniteBundleAtlas.sectionChartData_image_tangentHom`,
  `TauCeti.FiniteBundleAtlas.sectionChartData_overlap_tangentHom`,
  `TauCeti.FiniteBundleAtlas.sectionChartData_transition_tangentHom`,
  `TauCeti.FiniteBundleAtlas.ae_image_tangentHom_iff`,
  `TauCeti.FiniteBundleAtlas.ae_overlap_tangentHom_iff`,
  `TauCeti.FiniteBundleAtlas.sectionChartData_coordChange_tangentHom_apply`,
  `TauCeti.FiniteBundleAtlas.complexAntilinearPartL_coordChangeL_comp`: chart data of one-forms
  share the images, overlaps, and transitions of `A`, and their overlap coordinate changes commute
  with taking the complex antilinear part.
* `TauCeti.mem_zeroOneSobolevSections_iff`, `TauCeti.mem_zeroOneSobolevSections_iff_isZeroOneForm`,
  `TauCeti.isClosed_zeroOneSobolevSections`, `TauCeti.zeroOneSobolevSections.instCompleteSpace`,
  `TauCeti.closedComplemented_zeroOneSobolevSections`: membership, closedness, completeness, and
  complementedness.
* `TauCeti.zeroOnePartSobolevL_coe`, `TauCeti.zeroOnePartSobolevL_eq_zero_iff`,
  `TauCeti.chartValueL_zeroOnePartSobolevL_ae_coord`: properties of the `(0,1)`-projection.
* `TauCeti.zeroOneLowerOrdersL_zeroOnePartSobolevL`,
  `TauCeti.zeroOneOfExponentLEL_zeroOnePartSobolevL`,
  `TauCeti.zeroOneContMDiffSMulL_zeroOnePartSobolevL`: commutation with scale inclusions and smooth
  real multiplication.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Appendix C.1–C.2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL)
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

namespace TauCeti

/-! ### Chart data of one-forms -/

namespace FiniteBundleAtlas

open SmoothAlmostComplexStructure

section TangentHom

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas ℂ M F V)

/-- The chart images of the section chart data of `V`-valued one-forms are those of `A`. -/
theorem sectionChartData_image_tangentHom (i : Fin A.n) :
    ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i : Set ℂ) = A.image i :=
  congrArg SetLike.coe
    (((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData_image i).trans (image_tangentHom A 𝓘(ℝ, ℂ) i))

/-- The chart overlaps of the section chart data of `V`-valued one-forms are those of `A`. -/
theorem sectionChartData_overlap_tangentHom (i i' : Fin A.n) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.overlap i i' = A.overlap i i' :=
  ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData_overlap i i').trans (overlap_tangentHom A 𝓘(ℝ, ℂ) i i')

/-- On an overlap, the chart transitions of the section chart data of `V`-valued one-forms are
those of `A`. -/
theorem sectionChartData_transition_tangentHom {i i' : Fin A.n} {y : ℂ}
    (hy : y ∈ A.overlap i i') :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.transition i i' y = A.transition i i' y :=
  ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData_transition_of_mem
    (by rwa [overlap_tangentHom])).trans (congrFun (transition_tangentHom A 𝓘(ℝ, ℂ) i i') y)

/-- Almost everywhere on a chart image of the section chart data of one-forms is almost everywhere
on the corresponding chart image of `A`. -/
theorem ae_image_tangentHom_iff (μ : Measure ℂ) (i : Fin A.n) {P : ℂ → Prop} :
    (∀ᵐ y ∂μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i : Set ℂ), P y) ↔
      ∀ᵐ y ∂μ.restrict (A.image i), P y := by
  rw [ae_restrict_iff' (A.image i).isOpen.measurableSet,
    ae_restrict_iff' ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i).isOpen.measurableSet,
    sectionChartData_image_tangentHom]

/-- Almost everywhere on an overlap of the section chart data of one-forms is almost everywhere
on the corresponding overlap of `A`. -/
theorem ae_overlap_tangentHom_iff (μ : Measure ℂ) (i i' : Fin A.n) {P : ℂ → Prop} :
    (∀ᵐ y ∂μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.overlap i i'), P y) ↔
      ∀ᵐ y ∂μ.restrict (A.overlap i i'), P y := by
  rw [sectionChartData_overlap_tangentHom]

/-- On the overlap of charts `i` and `i'`, the coordinate change of the chart data of `V`-valued
one-forms is `η ↦ g ∘ η ∘ dτ`, for the coordinate change `g` of `V` and the chart transition `τ`. -/
theorem sectionChartData_coordChange_tangentHom_apply {i i' : Fin A.n} {y : ℂ}
    (hy : y ∈ A.overlap i i') (η : ℂ →L[ℝ] F) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.coordChange i i' y η =
      ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F).comp
        (η.comp (fderiv ℝ (A.transition i i') y)) := by
  have hy' : y ∈ (A.tangentHom 𝓘(ℝ, ℂ)).overlap i i' := by rwa [overlap_tangentHom]
  have hτ : (A.tangentHom 𝓘(ℝ, ℂ)).transition i i' y ∈ (A.tangentHom 𝓘(ℝ, ℂ)).image i := by
    rw [transition_tangentHom, image_tangentHom]
    exact A.overlap_subset_image i' i (A.transition_mem_overlap hy)
  have h := (A.tangentHom 𝓘(ℝ, ℂ)).coord_eq_coordChange
    (fun x ↦ ((A.tangentHom 𝓘(ℝ, ℂ)).triv i).symm x η) hy'
  rw [(A.tangentHom 𝓘(ℝ, ℂ)).coord_triv_symm η hτ, A.coord_tangentHom_eq_coordChange _ hy,
    ← transition_tangentHom A 𝓘(ℝ, ℂ), (A.tangentHom 𝓘(ℝ, ℂ)).coord_triv_symm η hτ,
    transition_tangentHom] at h
  rw [(A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData_coordChange_of_mem hy']
  exact h.symm

variable [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] [∀ x, Module ℂ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [VectorBundle ℂ F V]

/-- On the overlap of charts `i` and `i'`, the complex antilinear part commutes with the
coordinate change of one-forms: `∂bar (g ∘ L ∘ dτ) = g ∘ ∂bar L ∘ dτ`, since both the coordinate
change `g` of the complex vector bundle `V` and the derivative of the holomorphic chart transition
`τ` are complex linear. -/
theorem complexAntilinearPartL_coordChangeL_comp {i i' : Fin A.n} {y : ℂ}
    (hy : y ∈ A.overlap i i') (L : ℂ →L[ℝ] F) :
    complexAntilinearPartL (((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) :
        F →L[ℝ] F).comp (L.comp (fderiv ℝ (A.transition i i') y))) =
      ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F).comp
        ((complexAntilinearPartL L).comp (fderiv ℝ (A.transition i i') y)) := by
  have := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  have hτ : A.transition i i' y ∈ (A.tangentHom 𝓘(ℝ, ℂ)).image i := by
    rw [image_tangentHom]
    exact A.overlap_subset_image i' i (A.transition_mem_overlap hy)
  set θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x :=
    fun x ↦ ((A.tangentHom 𝓘(ℝ, ℂ)).triv i).symm x L
  have h₁ := A.coord_tangentHom_eq_coordChange θ hy
  have h₂ := A.coord_tangentHom_eq_coordChange
    (fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x)) hy
  rw [A.coord_tangentHom_zeroOnePart, A.coord_tangentHom_zeroOnePart, h₁,
    (A.tangentHom 𝓘(ℝ, ℂ)).coord_triv_symm L hτ] at h₂
  exact h₂

end TangentHom

end FiniteBundleAtlas

/-! ### The Sobolev space of `(0,1)`-forms over a boundaryless complex curve -/

section ZeroOne

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealZeroOneForm : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

variable (A : FiniteBundleAtlas ℂ M F V)

omit [FiniteDimensional ℝ F] in
variable {A} in
private theorem mem_image_of_mem_image_tangentHom {i : Fin A.n} {y : ℂ}
    (hy : y ∈ (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i) : y ∈ A.image i :=
  A.mem_image.2 ((A.tangentHom 𝓘(ℝ, ℂ)).mem_image.1 hy)

omit [FiniteDimensional ℝ F] in
private theorem sectionChartData_coord_zeroOnePart
    (i : Fin (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.n)
    (θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) {y : ℂ}
    (hy : y ∈ (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i) :
    letI := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.coord i
        (fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x)) y =
      complexAntilinearPartL ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.coord i θ y) := by
  have := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  rw [(A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData_coord_of_mem _ hy,
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData_coord_of_mem _ hy]
  exact A.coord_tangentHom_zeroOnePart i θ y

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The `(0,1)`-forms in the Sobolev space `W^{k,p}` of `V`-valued one-forms on a complex curve,
the space `W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)`: the elements whose chart data are complex antilinear almost
everywhere on the image of every chart (`TauCeti.mem_zeroOneSobolevSections_iff`). -/
def zeroOneSobolevSections : Submodule ℝ (SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) :=
  (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.antilinearSobolevSections μ p k

instance zeroOneSobolevSections.instNormedAddCommGroup :
    NormedAddCommGroup (zeroOneSobolevSections A μ p k) :=
  (zeroOneSobolevSections A μ p k).normedAddCommGroup

instance zeroOneSobolevSections.instNormedSpace :
    NormedSpace ℝ (zeroOneSobolevSections A μ p k) :=
  (zeroOneSobolevSections A μ p k).normedSpace

instance zeroOneSobolevSections.instIsTopologicalAddGroup :
    IsTopologicalAddGroup (zeroOneSobolevSections A μ p k) :=
  Submodule.isTopologicalAddGroup (zeroOneSobolevSections A μ p k)

variable {A μ p k}

/-- An element of `W^{k,p}` of `V`-valued one-forms is a `(0,1)`-form exactly when its chart data
are complex antilinear almost everywhere on the image of every chart. -/
theorem mem_zeroOneSobolevSections_iff {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k} :
    w ∈ zeroOneSobolevSections A μ p k ↔
      ∀ i, ∀ᵐ y ∂μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i), ∀ v : ℂ,
        (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w y (Complex.I • v) =
          -(Complex.I • (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w y v) :=
  SectionChartData.mem_antilinearSobolevSections_iff

/-- An element of `W^{k,p}` of `V`-valued one-forms whose chart data are the readings of a
one-form `θ` is a `(0,1)`-form exactly when `θ` is a `(0,1)`-form almost everywhere in every
chart. -/
theorem mem_zeroOneSobolevSections_iff_isZeroOneForm
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hw : ∀ i, (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)]
        (A.tangentHom 𝓘(ℝ, ℂ)).coord i θ) :
    w ∈ zeroOneSobolevSections A μ p k ↔
      ∀ i, ∀ᵐ y ∂μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i),
        (ofComplexManifold ℂ M).IsZeroOneForm (θ ((A.chart i).symm y)) := by
  rw [mem_zeroOneSobolevSections_iff]
  refine forall_congr' fun i ↦ Filter.eventually_congr ?_
  filter_upwards [hw i,
    ae_restrict_mem ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i).isOpen.measurableSet]
    with y h hy
  rw [h, A.isZeroOneForm_iff_coord_tangentHom i θ (mem_image_of_mem_image_tangentHom hy)]

/-- An element of `W^{k,p}` of `V`-valued one-forms whose chart data are the readings of a
`(0,1)`-form is a `(0,1)`-form. -/
theorem mem_zeroOneSobolevSections_of_isZeroOneForm
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hw : ∀ i, (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)]
        (A.tangentHom 𝓘(ℝ, ℂ)).coord i θ)
    (hθ : ∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (θ x)) :
    w ∈ zeroOneSobolevSections A μ p k :=
  (mem_zeroOneSobolevSections_iff_isZeroOneForm hw).2 fun _ ↦ .of_forall fun _ ↦ hθ _

/-- The `(0,1)`-forms form a closed subspace of `SobolevSection`. -/
theorem isClosed_zeroOneSobolevSections :
    IsClosed
      (zeroOneSobolevSections A μ p k : Set (SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k)) :=
  SectionChartData.isClosed_antilinearSobolevSections

/-- **Completeness.** The Sobolev `(0,1)`-forms form a Banach space. -/
instance zeroOneSobolevSections.instCompleteSpace :
    CompleteSpace (zeroOneSobolevSections A μ p k) :=
  SectionChartData.antilinearSobolevSections.instCompleteSpace

/-! ### The `(0,1)`-projection -/

variable (A μ p k) in
/-- **The `(0,1)`-projection.** The continuous projection of `W^{k,p}` of `V`-valued one-forms onto
the `(0,1)`-forms, applying `η ↦ ½ (η + i • η ∘ i)` to the chart data. It lifts the pointwise
`(0,1)`-projection `TauCeti.SmoothAlmostComplexStructure.zeroOnePart`
(`TauCeti.chartValueL_zeroOnePartSobolevL_ae_coord`) and fixes the `(0,1)`-forms
(`TauCeti.zeroOnePartSobolevL_coe`). -/
def zeroOnePartSobolevL :
    SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k →L[ℝ] zeroOneSobolevSections A μ p k :=
  have (x : M) : ContinuousSMul ℂ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.antilinearPartSobolevL μ p k
    (fun θ x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x))
    (fun i θ _ hy ↦ sectionChartData_coord_zeroOnePart A i θ hy)

/-- The components of the `(0,1)`-projection of `w` are those of `w` transformed by the matrix of
the complex antilinear part `ContinuousLinearMap.complexAntilinearPartL` of the model fibre. -/
@[simp]
theorem coe_coe_zeroOnePartSobolevL (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) :
    ((zeroOnePartSobolevL A μ p k w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) :
        (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.SobolevData μ p k) =
      (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.constMapData μ p k complexAntilinearPartL w :=
  SectionChartData.coe_coe_antilinearPartSobolevL _ _ w

/-- The chart data of the `(0,1)`-projection of `w` are the `(0,1)`-projections
`η ↦ ½ (η + i • η ∘ i)` of the chart data of `w`. -/
theorem chartValueL_zeroOnePartSobolevL_ae (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k)
    (i : Fin A.n) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i (zeroOnePartSobolevL A μ p k w)
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)] fun y ↦
        complexAntilinearPartL ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w y) :=
  SectionChartData.chartValueL_antilinearPartSobolevL_ae _ _ w i

/-- The `(0,1)`-projection of `w` vanishes exactly when the chart data of `w` are complex linear
almost everywhere on the image of every chart. -/
theorem zeroOnePartSobolevL_eq_zero_iff {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k} :
    zeroOnePartSobolevL A μ p k w = 0 ↔
      ∀ i, ∀ᵐ y ∂μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i), ∀ v : ℂ,
        (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w y (Complex.I • v) =
          Complex.I • (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w y v :=
  SectionChartData.antilinearPartSobolevL_eq_zero_iff _ _

/-- **Lifting the pointwise projection.** If the chart data of `w` in chart `i` are the readings of
a one-form `θ`, the chart data of its `(0,1)`-projection in chart `i` are the readings of the
`(0,1)`-part of `θ`. -/
theorem chartValueL_zeroOnePartSobolevL_ae_coord
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x} {i : Fin A.n}
    (hw : (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)]
        (A.tangentHom 𝓘(ℝ, ℂ)).coord i θ) :
    letI := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.chartValueL μ p k i (zeroOnePartSobolevL A μ p k w)
      =ᵐ[μ.restrict ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.image i)]
        (A.tangentHom 𝓘(ℝ, ℂ)).coord i fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x) := by
  have := fun x ↦ (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  have hcoord := (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData_coord_ae_eq μ i
  exact (SectionChartData.chartValueL_antilinearPartSobolevL_ae_coord _ _
    (hw.trans (hcoord θ).symm)).trans (hcoord _)

/-- The `(0,1)`-projection fixes the `(0,1)`-forms. -/
@[simp]
theorem zeroOnePartSobolevL_coe (w : zeroOneSobolevSections A μ p k) :
    zeroOnePartSobolevL A μ p k w = w :=
  SectionChartData.antilinearPartSobolevL_coe _ _ w

/-- An element of `W^{k,p}` of `V`-valued one-forms is fixed by the `(0,1)`-projection exactly when
it is a `(0,1)`-form. -/
@[simp]
theorem coe_zeroOnePartSobolevL_eq_self_iff {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k} :
    (zeroOnePartSobolevL A μ p k w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) = w ↔
      w ∈ zeroOneSobolevSections A μ p k :=
  SectionChartData.coe_antilinearPartSobolevL_eq_self_iff _ _

/-- The `(0,1)`-projection is onto the `(0,1)`-forms. -/
theorem zeroOnePartSobolevL_surjective : Function.Surjective (zeroOnePartSobolevL A μ p k) :=
  SectionChartData.antilinearPartSobolevL_surjective _ _

/-- **Complemented.** The `(0,1)`-forms are a complemented subspace of `W^{k,p}` of `V`-valued
one-forms, with the `(0,1)`-projection as a continuous projection onto it. -/
theorem closedComplemented_zeroOneSobolevSections :
    (zeroOneSobolevSections A μ p k).ClosedComplemented :=
  ⟨zeroOnePartSobolevL A μ p k, zeroOnePartSobolevL_coe⟩

/-! ### Lowering the order -/

/-- Forgetting derivatives preserves the native `(0,1)` condition. -/
theorem lowerOrdersL_mem_zeroOneSobolevSections (d : ℕ)
    {w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p (k + d)}
    (hw : w ∈ zeroOneSobolevSections A μ p (k + d)) :
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL μ p k d w ∈
      zeroOneSobolevSections A μ p k :=
  SectionChartData.lowerOrdersL_mem_antilinearSobolevSections d hw

variable (A μ p k) in
/-- The continuous inclusion of native `(0,1)`-forms from order `k + d` to order `k`. -/
def zeroOneLowerOrdersL (d : ℕ) :
    zeroOneSobolevSections A μ p (k + d) →L[ℝ] zeroOneSobolevSections A μ p k :=
  (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.antilinearLowerOrdersL μ p k d

/-- As a function, the native order inclusion is the restriction of the canonical order map. -/
theorem coeFn_zeroOneLowerOrdersL_eq_codRestrict (d : ℕ) :
    ⇑(zeroOneLowerOrdersL A μ p k d) =
      Set.codRestrict
        (⇑((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL μ p k d) ∘
          ⇑(zeroOneSobolevSections A μ p (k + d)).subtypeL)
        (zeroOneSobolevSections A μ p k)
        (fun w ↦ lowerOrdersL_mem_zeroOneSobolevSections d w.property) :=
  funext fun w ↦ Subtype.ext (SectionChartData.coe_antilinearLowerOrdersL d w)

/-- The inclusion acts by the canonical order inclusion on the underlying one-form. -/
@[simp]
theorem coe_zeroOneLowerOrdersL (d : ℕ) (w : zeroOneSobolevSections A μ p (k + d)) :
    (zeroOneLowerOrdersL A μ p k d w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) =
      (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL μ p k d w :=
  SectionChartData.coe_antilinearLowerOrdersL d w

/-- Forgetting zero derivatives is the identity. -/
@[simp]
theorem zeroOneLowerOrdersL_zero (w : zeroOneSobolevSections A μ p k) :
    zeroOneLowerOrdersL A μ p k 0 w = w :=
  SectionChartData.antilinearLowerOrdersL_zero w

omit k in
/-- Coercion to one-forms commutes with equality transport of the Sobolev order. -/
@[simp]
theorem coe_zeroOneSobolevSections_eqRec {a b : ℕ} (h : a = b)
    (w : zeroOneSobolevSections A μ p a) :
    ((h ▸ w : zeroOneSobolevSections A μ p b) : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p b) =
      h ▸ (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p a) :=
  SectionChartData.coe_antilinearSobolevSections_eqRec h w

/-- Native order inclusions compose, with the source order reassociated by `Nat.add_assoc`. -/
@[simp]
theorem zeroOneLowerOrdersL_zeroOneLowerOrdersL (d e : ℕ)
    (w : zeroOneSobolevSections A μ p ((k + d) + e)) :
    zeroOneLowerOrdersL A μ p k d (zeroOneLowerOrdersL A μ p (k + d) e w) =
      zeroOneLowerOrdersL A μ p k (d + e) ((Nat.add_assoc k d e) ▸ w) :=
  SectionChartData.antilinearLowerOrdersL_antilinearLowerOrdersL d e w

/-- Forgetting `d + 1` derivatives first forgets the highest derivative. -/
theorem zeroOneLowerOrdersL_succ (d : ℕ) :
    zeroOneLowerOrdersL A μ p k (d + 1) =
      (zeroOneLowerOrdersL A μ p k d).comp (zeroOneLowerOrdersL A μ p (k + d) 1) :=
  SectionChartData.antilinearLowerOrdersL_succ d

/-- The native order inclusion is injective. -/
theorem zeroOneLowerOrdersL_injective (d : ℕ) :
    Function.Injective (zeroOneLowerOrdersL A μ p k d) :=
  SectionChartData.antilinearLowerOrdersL_injective d

/-- The native `(0,1)` projection commutes with forgetting derivatives. -/
theorem zeroOneLowerOrdersL_zeroOnePartSobolevL (d : ℕ)
    (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p (k + d)) :
    zeroOneLowerOrdersL A μ p k d (zeroOnePartSobolevL A μ p (k + d) w) =
      zeroOnePartSobolevL A μ p k
        ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.lowerOrdersL μ p k d w) :=
  SectionChartData.antilinearLowerOrdersL_antilinearPartSobolevL d _ _ w

/-! ### Lowering the integrability exponent -/

section Exponent

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

variable (A μ k) in
/-- For `p ≤ q`, the continuous inclusion of the `(0,1)`-forms of exponent `q` into those of
exponent `p`. -/
def zeroOneOfExponentLEL (hpq : p ≤ q) :
    zeroOneSobolevSections A μ q k →L[ℝ] zeroOneSobolevSections A μ p k :=
  (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.antilinearOfExponentLEL μ k hpq

@[simp]
theorem coe_zeroOneOfExponentLEL (hpq : p ≤ q) (w : zeroOneSobolevSections A μ q k) :
    (zeroOneOfExponentLEL A μ k hpq w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) =
      (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.ofExponentLEL μ k hpq w :=
  SectionChartData.coe_antilinearOfExponentLEL hpq w

/-- Lowering the integrability exponent on `(0,1)`-forms is injective. -/
theorem zeroOneOfExponentLEL_injective (hpq : p ≤ q) :
    Function.Injective (zeroOneOfExponentLEL A μ k hpq) :=
  SectionChartData.antilinearOfExponentLEL_injective hpq

omit [Fact (1 ≤ q)] in
@[simp]
theorem zeroOneOfExponentLEL_self (w : zeroOneSobolevSections A μ p k) :
    zeroOneOfExponentLEL A μ k le_rfl w = w :=
  SectionChartData.antilinearOfExponentLEL_self w

@[simp]
theorem zeroOneOfExponentLEL_zeroOneOfExponentLEL {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (hpq : p ≤ q) (hqr : q ≤ r) (w : zeroOneSobolevSections A μ r k) :
    zeroOneOfExponentLEL A μ k hpq (zeroOneOfExponentLEL A μ k hqr w) =
      zeroOneOfExponentLEL A μ k (hpq.trans hqr) w :=
  SectionChartData.antilinearOfExponentLEL_antilinearOfExponentLEL hpq hqr w

/-- Lowering the exponent commutes with forgetting derivatives on `(0,1)`-forms. -/
theorem zeroOneLowerOrdersL_zeroOneOfExponentLEL (d : ℕ) (hpq : p ≤ q)
    (w : zeroOneSobolevSections A μ q (k + d)) :
    zeroOneLowerOrdersL A μ p k d (zeroOneOfExponentLEL A μ (k + d) hpq w) =
      zeroOneOfExponentLEL A μ k hpq (zeroOneLowerOrdersL A μ q k d w) :=
  SectionChartData.antilinearLowerOrdersL_antilinearOfExponentLEL d hpq w

/-- Lowering the exponent commutes with the `(0,1)`-projection. -/
theorem zeroOneOfExponentLEL_zeroOnePartSobolevL (hpq : p ≤ q)
    (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ q k) :
    zeroOneOfExponentLEL A μ k hpq (zeroOnePartSobolevL A μ q k w) =
      zeroOnePartSobolevL A μ p k
        ((A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.ofExponentLEL μ k hpq w) :=
  SectionChartData.antilinearOfExponentLEL_antilinearPartSobolevL _ _ hpq w

end Exponent

/-! ### Multiplication by smooth real functions -/

section SMul

variable {φ ψ : M → ℝ}

variable (A μ p k) in
/-- Multiplication by a smooth real function `φ : M → ℝ` on the Sobolev `(0,1)`-forms
`zeroOneSobolevSections A μ p k`. -/
def zeroOneContMDiffSMulL (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ) :
    zeroOneSobolevSections A μ p k →L[ℝ] zeroOneSobolevSections A μ p k :=
  (SobolevSection.contMDiffSMulL (A.tangentHom 𝓘(ℝ, ℂ)) μ p k hφ).restrict fun _ ↦
    (A.tangentHom 𝓘(ℝ, ℂ)).sectionChartData.mem_antilinearSobolevSections_of_chartValueL_ae_smul
      (SobolevSection.chartValueL_contMDiffSMulL_ae hφ)

@[simp]
theorem coe_zeroOneContMDiffSMulL (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (w : zeroOneSobolevSections A μ p k) :
    (zeroOneContMDiffSMulL A μ p k hφ w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) =
      SobolevSection.contMDiffSMulL (A.tangentHom 𝓘(ℝ, ℂ)) μ p k hφ w :=
  ContinuousLinearMap.coe_restrict_apply _ w

@[simp]
theorem zeroOneContMDiffSMulL_const (c : ℝ) :
    zeroOneContMDiffSMulL A μ p k (contMDiff_const (c := c)) = c • ContinuousLinearMap.id ℝ _ := by
  ext1 w
  apply Subtype.ext
  simp only [smul_apply, ContinuousLinearMap.id_apply, Submodule.coe_smul,
    coe_zeroOneContMDiffSMulL]
  exact DFunLike.congr_fun (SobolevSection.contMDiffSMulL_const c) w.val

theorem zeroOneContMDiffSMulL_add (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ ψ) :
    zeroOneContMDiffSMulL A μ p k (hφ.add hψ) =
      zeroOneContMDiffSMulL A μ p k hφ + zeroOneContMDiffSMulL A μ p k hψ := by
  ext1 w
  apply Subtype.ext
  simp only [add_apply, Submodule.coe_add, coe_zeroOneContMDiffSMulL]
  exact DFunLike.congr_fun (SobolevSection.contMDiffSMulL_add hφ hψ) w.val

theorem zeroOneContMDiffSMulL_mul (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ ψ) :
    zeroOneContMDiffSMulL A μ p k (hφ.mul hψ) =
      (zeroOneContMDiffSMulL A μ p k hφ).comp (zeroOneContMDiffSMulL A μ p k hψ) := by
  ext1 w
  apply Subtype.ext
  simp only [ContinuousLinearMap.comp_apply, coe_zeroOneContMDiffSMulL]
  exact DFunLike.congr_fun (SobolevSection.contMDiffSMulL_mul hφ hψ) w.val

/-- Smooth real multiplication commutes with forgetting derivatives on `(0,1)`-forms. -/
theorem zeroOneLowerOrdersL_zeroOneContMDiffSMulL (d : ℕ) (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (w : zeroOneSobolevSections A μ p (k + d)) :
    zeroOneLowerOrdersL A μ p k d (zeroOneContMDiffSMulL A μ p (k + d) hφ w) =
      zeroOneContMDiffSMulL A μ p k hφ (zeroOneLowerOrdersL A μ p k d w) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [zeroOneLowerOrdersL_succ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    refine (congrArg (zeroOneLowerOrdersL A μ p k d) (Subtype.ext ?_)).trans (ih _)
    simp only [coe_zeroOneLowerOrdersL, coe_zeroOneContMDiffSMulL,
      SectionChartData.lowerOrdersL_one]
    exact SobolevSection.lowerOrderL_contMDiffSMulL hφ w.val

/-- Smooth real multiplication commutes with the `(0,1)`-projection. -/
theorem zeroOneContMDiffSMulL_zeroOnePartSobolevL (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (w : SobolevSection (A.tangentHom 𝓘(ℝ, ℂ)) μ p k) :
    zeroOneContMDiffSMulL A μ p k hφ (zeroOnePartSobolevL A μ p k w) =
      zeroOnePartSobolevL A μ p k
        (SobolevSection.contMDiffSMulL (A.tangentHom 𝓘(ℝ, ℂ)) μ p k hφ w) :=
  SectionChartData.restrict_antilinearPartSobolevL_of_chartValueL_ae_smul
    (SobolevSection.chartValueL_contMDiffSMulL_ae hφ) _ _ w

end SMul

end ZeroOne

end TauCeti
