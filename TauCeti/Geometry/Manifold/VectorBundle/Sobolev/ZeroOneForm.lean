/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Exponent
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.SMul
public import TauCeti.Topology.VectorBundle.RestrictScalars
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Tangent
import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.FixedSubmodule

/-!
# Sobolev `(0,1)`-forms over a complex curve

Let `M` be a complex curve without boundary, a complex manifold modelled on `ℂ`, and let `V → M`
be a complex vector bundle with finite-dimensional model fibre `F`, regarded as a real vector
bundle. A `V`-valued one-form `η : T_x M → V x` is a `(0,1)`-form when it is complex antilinear,
`η (i v) = -(i • η v)` (`TauCeti.SmoothAlmostComplexStructure.IsZeroOneForm` for the almost
complex structure `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold ℂ M`). This file
constructs the target space `W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)` of real Cauchy–Riemann operators on a
compact boundaryless curve as a closed subspace of the Sobolev space
`TauCeti.SobolevSection A.tangentHom μ p k` of `V`-valued one-forms, built on the charts of a
finite bundle atlas `A` of `V`.

In chart `i` a one-form is read through the preferred trivializations of the tangent bundle and of
`V`, which are both complex linear: the first is the derivative of a holomorphic chart transition
and the second comes from the complex vector bundle structure. So a one-form is a `(0,1)`-form at
a point exactly when its chart reading `η : ℂ →L[ℝ] F` is complex antilinear, and the
`(0,1)`-projection `η ↦ ½ (η + i • η ∘ i)` acts on chart readings by a constant idempotent linear
map of the model fibre `ℂ →L[ℝ] F`, the complex antilinear part
`ContinuousLinearMap.complexAntilinearPartL`
(`TauCeti.FiniteBundleAtlas.isZeroOneForm_iff_coord_tangentHom`,
`TauCeti.FiniteBundleAtlas.coord_tangentHom_zeroOnePart`, which hold for complex manifolds of any
dimension). Specializing `TauCeti.SectionChartData.fixedSubmodule` and
`TauCeti.SectionChartData.projFixedL` to `ContinuousLinearMap.complexAntilinearPartL` yields the
closed, complete, complemented subspace `TauCeti.zeroOneSobolevSections A μ p k`, the continuous
`(0,1)`-projection `TauCeti.zeroOnePartSobolevL`, the order inclusion `TauCeti.zeroOneLowerOrderL`,
the exponent inclusion `TauCeti.zeroOneOfExponentLEL`, and multiplication by smooth real-valued
functions `TauCeti.zeroOneContMDiffSMulL`.

## Main definitions

* `TauCeti.zeroOneSobolevSections A μ p k`: the `(0,1)`-forms in `W^{k,p}` of `V`-valued
  one-forms.
* `TauCeti.zeroOnePartSobolevL`: the continuous `(0,1)`-projection onto it.
* `TauCeti.zeroOneLowerOrderL`: the inclusion of order `k + 1` into order `k`.
* `TauCeti.zeroOneOfExponentLEL`: the inclusion of exponent `q` into exponent `p` for `p ≤ q`.
* `TauCeti.zeroOneContMDiffSMulL`: multiplication by a smooth function `φ : M → ℝ`.

## Main results

* `TauCeti.FiniteBundleAtlas.isZeroOneForm_iff_coord_tangentHom`,
  `TauCeti.FiniteBundleAtlas.coord_tangentHom_zeroOnePart`: on the image of a chart, a one-form is a
  `(0,1)`-form exactly when its reading is complex antilinear, and its `(0,1)`-part is read as the
  complex antilinear part of its reading.
* `TauCeti.mem_zeroOneSobolevSections_iff`: membership is complex antilinearity of the chart data
  almost everywhere.
* `TauCeti.mem_zeroOneSobolevSections_iff_isZeroOneForm`,
  `TauCeti.mem_zeroOneSobolevSections_of_isZeroOneForm`,
  `TauCeti.ofContMDiffSection_mem_zeroOneSobolevSections`: characterizations and `Cᵏ` section
  membership.
* `TauCeti.isClosed_zeroOneSobolevSections`, `TauCeti.zeroOneSobolevSections.instCompleteSpace`:
  the subspace is closed and complete.
* `TauCeti.zeroOnePartSobolevL_coe`, `TauCeti.closedComplemented_zeroOneSobolevSections`: the
  projection fixes `(0,1)`-forms, and the subspace is complemented.
* `TauCeti.chartValueL_zeroOnePartSobolevL_ae`, `TauCeti.zeroOnePartSobolevL_eq_zero_iff`,
  `TauCeti.chartValueL_zeroOnePartSobolevL_ae_coord`: chart action, kernel, and lifting of the
  pointwise `(0,1)`-projection.
* `TauCeti.zeroOneLowerOrderL_zeroOnePartSobolevL`,
  `TauCeti.zeroOneOfExponentLEL_zeroOnePartSobolevL`,
  `TauCeti.zeroOneContMDiffSMulL_zeroOnePartSobolevL`: the `(0,1)`-projection commutes with order
  lowering, exponent lowering, and smooth multiplication.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1 and C.2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open ContinuousLinearMap (complexAntilinearPartL complexAntilinearPartL_apply_apply
  complexAntilinearPartL_apply_I_smul complexAntilinearPartL_complexAntilinearPartL
  complexAntilinearPartL_eq_self_iff complexAntilinearPartL_eq_zero_iff)
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

universe u

namespace TauCeti

/-! ### Chart readings of `(0,1)`-forms -/

namespace FiniteBundleAtlas

open SmoothAlmostComplexStructure

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [VectorBundle ℂ F V]
  (A : FiniteBundleAtlas E M F V)

variable [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)] in
/-- The `(0,1)`-part of a one-form is read in a chart as the complex antilinear part
`ContinuousLinearMap.complexAntilinearPartL` of its reading. -/
theorem coord_tangentHom_zeroOnePart (i : Fin A.n)
    (θ : ∀ x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x) (y : E) :
    A.tangentHom.coord i (fun x ↦ (ofComplexManifold E M).zeroOnePart (θ x)) y =
      complexAntilinearPartL (A.tangentHom.coord i θ y) :=
  A.coord_modelTangentHom_zeroOnePart i (fun _ hx ↦ inTangentCoordinates_ofComplexManifold hx) θ y

/-- On the image of a chart, a one-form is read as a complex antilinear map exactly when it is a
`(0,1)`-form at the corresponding point. -/
theorem isZeroOneForm_iff_coord_tangentHom (i : Fin A.n)
    (θ : ∀ x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x) {y : E} (hy : y ∈ A.image i) :
    (ofComplexManifold E M).IsZeroOneForm (θ ((A.chart i).symm y)) ↔
      ∀ v, A.tangentHom.coord i θ y (Complex.I • v) =
        -(Complex.I • A.tangentHom.coord i θ y v) :=
  A.isZeroOneForm_iff_coord_modelTangentHom i
    (fun _ hx ↦ inTangentCoordinates_ofComplexManifold hx) θ hy

end FiniteBundleAtlas

section ZeroOne

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [FiniteDimensional ℝ F]
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
    (hy : y ∈ A.tangentHom.sectionChartData.image i) : y ∈ A.image i :=
  A.mem_image.2 (A.tangentHom.mem_image.1 hy)

/-! ### The Sobolev space of `(0,1)`-forms -/

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The `(0,1)`-forms in the Sobolev space `W^{k,p}` of `V`-valued one-forms on a complex curve,
the space `W^{k,p}(Σ, Λ^{0,1} ⊗_ℂ V)`: the elements whose chart data are complex antilinear almost
everywhere on the image of every chart (`TauCeti.mem_zeroOneSobolevSections_iff`). -/
def zeroOneSobolevSections : Submodule ℝ (SobolevSection A.tangentHom μ p k) :=
  A.tangentHom.sectionChartData.fixedSubmodule μ p k complexAntilinearPartL

variable {A μ p k}

/-- An element of `W^{k,p}` of `V`-valued one-forms is a `(0,1)`-form exactly when its chart data
are complex antilinear almost everywhere on the image of every chart. -/
theorem mem_zeroOneSobolevSections_iff {w : SobolevSection A.tangentHom μ p k} :
    w ∈ zeroOneSobolevSections A μ p k ↔
      ∀ i, ∀ᵐ y ∂μ.restrict (A.tangentHom.sectionChartData.image i), ∀ v : ℂ,
        A.tangentHom.sectionChartData.chartValueL μ p k i w y (Complex.I • v) =
          -(Complex.I • A.tangentHom.sectionChartData.chartValueL μ p k i w y v) :=
  SectionChartData.mem_fixedSubmodule_iff.trans <| forall_congr' fun _ ↦
    Filter.eventually_congr (Filter.Eventually.of_forall fun _ ↦ complexAntilinearPartL_eq_self_iff)

/-- An element of `W^{k,p}` of `V`-valued one-forms whose chart data are the readings of a
one-form `θ` is a `(0,1)`-form exactly when `θ` is a `(0,1)`-form almost everywhere in every
chart. -/
theorem mem_zeroOneSobolevSections_iff_isZeroOneForm {w : SobolevSection A.tangentHom μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hw : ∀ i, A.tangentHom.sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict (A.tangentHom.sectionChartData.image i)] A.tangentHom.coord i θ) :
    w ∈ zeroOneSobolevSections A μ p k ↔
      ∀ i, ∀ᵐ y ∂μ.restrict (A.tangentHom.sectionChartData.image i),
        (ofComplexManifold ℂ M).IsZeroOneForm (θ ((A.chart i).symm y)) := by
  rw [mem_zeroOneSobolevSections_iff]
  refine forall_congr' fun i ↦ Filter.eventually_congr ?_
  filter_upwards [hw i,
    ae_restrict_mem (A.tangentHom.sectionChartData.image i).isOpen.measurableSet] with y h hy
  rw [h, A.isZeroOneForm_iff_coord_tangentHom i θ (mem_image_of_mem_image_tangentHom hy)]

/-- An element of `W^{k,p}` of `V`-valued one-forms whose chart data are the readings of a
`(0,1)`-form is a `(0,1)`-form. -/
theorem mem_zeroOneSobolevSections_of_isZeroOneForm {w : SobolevSection A.tangentHom μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hw : ∀ i, A.tangentHom.sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict (A.tangentHom.sectionChartData.image i)] A.tangentHom.coord i θ)
    (hθ : ∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (θ x)) :
    w ∈ zeroOneSobolevSections A μ p k :=
  (mem_zeroOneSobolevSections_iff_isZeroOneForm hw).2 fun _ ↦ Filter.Eventually.of_forall
    fun _ ↦ hθ _

/-- A `Cᵏ` section of `x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x` that is a `(0,1)`-form at every point
defines an element of `zeroOneSobolevSections A μ p k`. -/
theorem ofContMDiffSection_mem_zeroOneSobolevSections
    [ContMDiffVectorBundle k F V 𝓘(ℝ, ℂ)]
    {θ : Cₛ^k⟮𝓘(ℝ, ℂ); ℂ →L[ℝ] F, fun x ↦ TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x⟯}
    (hθ : ∀ x, (ofComplexManifold ℂ M).IsZeroOneForm (θ x)) :
    SobolevSection.ofContMDiffSection A.tangentHom μ p k θ ∈ zeroOneSobolevSections A μ p k :=
  mem_zeroOneSobolevSections_of_isZeroOneForm
    (SobolevSection.chartValueL_ofContMDiffSection_ae A.tangentHom μ p k θ) hθ

/-- The `(0,1)`-forms form a closed subspace: it is the intersection of the kernels of continuous
linear maps. -/
theorem isClosed_zeroOneSobolevSections :
    IsClosed (zeroOneSobolevSections A μ p k : Set (SobolevSection A.tangentHom μ p k)) :=
  A.tangentHom.sectionChartData.isClosed_fixedSubmodule μ p k complexAntilinearPartL

variable (A μ p k) in
/-- Normed additive group structure on `zeroOneSobolevSections A μ p k`, registered directly on the
head symbol so continuous linear operator spaces on `zeroOneSobolevSections A μ p k` do not time out
searching across nested `Submodule` coercions. -/
noncomputable instance zeroOneSobolevSections.instNormedAddCommGroup :
    NormedAddCommGroup (zeroOneSobolevSections A μ p k) :=
  Submodule.normedAddCommGroup _

variable (A μ p k) in
/-- Real normed space structure on `zeroOneSobolevSections A μ p k`. -/
noncomputable instance zeroOneSobolevSections.instNormedSpace :
    NormedSpace ℝ (zeroOneSobolevSections A μ p k) :=
  Submodule.normedSpace _

/-- **Completeness.** The Sobolev `(0,1)`-forms form a Banach space. -/
instance zeroOneSobolevSections.instCompleteSpace :
    CompleteSpace (zeroOneSobolevSections A μ p k) :=
  isClosed_zeroOneSobolevSections.completeSpace_coe

/-! ### The `(0,1)`-projection -/

variable (F) in
omit [IsManifold 𝓘(ℂ) ∞ M] [FiniteDimensional ℝ F] in
private def zeroOnePartSection (θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) :
    ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x :=
  letI (x' : M) : ContinuousSMul ℂ (V x') :=
    (VectorBundle.continuousLinearEquivAt ℂ F V x').continuousSMul
  fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x)

omit [FiniteDimensional ℝ F] in
private theorem sectionChartData_coord_zeroOnePart (A : FiniteBundleAtlas ℂ M F V) (i : Fin A.n)
    (θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) (y : ℂ) :
    A.tangentHom.sectionChartData.coord i (zeroOnePartSection F θ) y =
      complexAntilinearPartL (A.tangentHom.sectionChartData.coord i θ y) :=
  letI (x : M) : ContinuousSMul ℂ (V x) :=
    (VectorBundle.continuousLinearEquivAt ℂ F V x).continuousSMul
  have h : A.tangentHom.coord i (zeroOnePartSection F θ) =
      complexAntilinearPartL ∘ A.tangentHom.coord i θ :=
    funext (A.coord_tangentHom_zeroOnePart i θ)
  (congrFun (congrArg (indicator _) h) y).trans
    (congrFun (indicator_comp_of_zero complexAntilinearPartL.map_zero) y)

variable (A μ p k) in
/-- **The `(0,1)`-projection.** The continuous projection of `W^{k,p}` of `V`-valued one-forms onto
the `(0,1)`-forms, applying `η ↦ ½ (η + i • η ∘ i)` to the chart data. It lifts the pointwise
`(0,1)`-projection `TauCeti.SmoothAlmostComplexStructure.zeroOnePart`
(`TauCeti.chartValueL_zeroOnePartSobolevL_ae_coord`) and fixes the `(0,1)`-forms
(`TauCeti.zeroOnePartSobolevL_coe`). -/
def zeroOnePartSobolevL : SobolevSection A.tangentHom μ p k →L[ℝ] zeroOneSobolevSections A μ p k :=
  A.tangentHom.sectionChartData.projFixedL μ p k
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ y _ ↦ sectionChartData_coord_zeroOnePart A i θ y)

/-- The components of the `(0,1)`-projection of `w` are those of `w` transformed by the matrix of
the complex antilinear part `ContinuousLinearMap.complexAntilinearPartL` of the model fibre. -/
@[simp]
theorem coe_coe_zeroOnePartSobolevL (w : SobolevSection A.tangentHom μ p k) :
    ((zeroOnePartSobolevL A μ p k w : SobolevSection A.tangentHom μ p k) :
        A.tangentHom.sectionChartData.SobolevData μ p k) =
      A.tangentHom.sectionChartData.constMapData μ p k complexAntilinearPartL w :=
  A.tangentHom.sectionChartData.coe_coe_projFixedL
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ y _ ↦ sectionChartData_coord_zeroOnePart A i θ y) w

/-- The chart data of the `(0,1)`-projection of `w` are the `(0,1)`-projections
`η ↦ ½ (η + i • η ∘ i)` of the chart data of `w`. -/
theorem chartValueL_zeroOnePartSobolevL_ae (w : SobolevSection A.tangentHom μ p k)
    (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i (zeroOnePartSobolevL A μ p k w)
      =ᵐ[μ.restrict (A.tangentHom.sectionChartData.image i)]
        fun y ↦ complexAntilinearPartL (A.tangentHom.sectionChartData.chartValueL μ p k i w y) :=
  A.tangentHom.sectionChartData.chartValueL_projFixedL_ae
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ y _ ↦ sectionChartData_coord_zeroOnePart A i θ y) w i

/-- The `(0,1)`-projection of `w` vanishes exactly when the chart data of `w` are complex linear
almost everywhere on the image of every chart. -/
theorem zeroOnePartSobolevL_eq_zero_iff {w : SobolevSection A.tangentHom μ p k} :
    zeroOnePartSobolevL A μ p k w = 0 ↔
      ∀ i, ∀ᵐ y ∂μ.restrict (A.tangentHom.sectionChartData.image i), ∀ v : ℂ,
        A.tangentHom.sectionChartData.chartValueL μ p k i w y (Complex.I • v) =
          Complex.I • A.tangentHom.sectionChartData.chartValueL μ p k i w y v :=
  (A.tangentHom.sectionChartData.projFixedL_eq_zero_iff μ p k
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ y _ ↦ sectionChartData_coord_zeroOnePart A i θ y)).trans <| forall_congr' fun _ ↦
      Filter.eventually_congr
        (Filter.Eventually.of_forall fun _ ↦ complexAntilinearPartL_eq_zero_iff)

variable [∀ x, ContinuousSMul ℂ (V x)] in
/-- **Lifting the pointwise projection.** If the chart data of `w` in chart `i` are the readings of
a one-form `θ`, the chart data of its `(0,1)`-projection in chart `i` are the readings of the
`(0,1)`-part of `θ`. -/
theorem chartValueL_zeroOnePartSobolevL_ae_coord {w : SobolevSection A.tangentHom μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x} {i : Fin A.n}
    (hw : A.tangentHom.sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict (A.tangentHom.sectionChartData.image i)] A.tangentHom.coord i θ) :
    A.tangentHom.sectionChartData.chartValueL μ p k i (zeroOnePartSobolevL A μ p k w)
      =ᵐ[μ.restrict (A.tangentHom.sectionChartData.image i)]
        A.tangentHom.coord i fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x) := by
  have hcoord (θ' : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) :=
    A.tangentHom.sectionChartData_coord_ae_eq μ i θ'
  exact (A.tangentHom.sectionChartData.chartValueL_projFixedL_ae_coord
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ y _ ↦ sectionChartData_coord_zeroOnePart A i θ y)
      (hw.trans (hcoord θ).symm)).trans (hcoord _)

/-- The `(0,1)`-projection fixes the `(0,1)`-forms. -/
@[simp]
theorem zeroOnePartSobolevL_coe (w : zeroOneSobolevSections A μ p k) :
    zeroOnePartSobolevL A μ p k w = w :=
  A.tangentHom.sectionChartData.projFixedL_coe
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ y _ ↦ sectionChartData_coord_zeroOnePart A i θ y) w

/-- An element of `W^{k,p}` of `V`-valued one-forms is fixed by the `(0,1)`-projection exactly when
it is a `(0,1)`-form. -/
theorem coe_zeroOnePartSobolevL_eq_self_iff {w : SobolevSection A.tangentHom μ p k} :
    (zeroOnePartSobolevL A μ p k w : SobolevSection A.tangentHom μ p k) = w ↔
      w ∈ zeroOneSobolevSections A μ p k :=
  A.tangentHom.sectionChartData.coe_projFixedL_eq_self_iff μ p k
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ y _ ↦ sectionChartData_coord_zeroOnePart A i θ y)

/-- The `(0,1)`-projection is onto the `(0,1)`-forms. -/
theorem zeroOnePartSobolevL_surjective : Function.Surjective (zeroOnePartSobolevL A μ p k) :=
  A.tangentHom.sectionChartData.projFixedL_surjective μ p k
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ y _ ↦ sectionChartData_coord_zeroOnePart A i θ y)

/-- **Complemented.** The `(0,1)`-forms are a complemented subspace of `W^{k,p}` of `V`-valued
one-forms, with the `(0,1)`-projection as a continuous projection onto it. -/
theorem closedComplemented_zeroOneSobolevSections :
    (zeroOneSobolevSections A μ p k).ClosedComplemented :=
  ⟨zeroOnePartSobolevL A μ p k, zeroOnePartSobolevL_coe⟩

/-! ### Lowering the order -/

/-- Forgetting the highest derivative of a `(0,1)`-form gives a `(0,1)`-form. -/
theorem lowerOrderL_mem_zeroOneSobolevSections {w : SobolevSection A.tangentHom μ p (k + 1)}
    (hw : w ∈ zeroOneSobolevSections A μ p (k + 1)) :
    A.tangentHom.sectionChartData.lowerOrderL μ p k w ∈ zeroOneSobolevSections A μ p k :=
  SectionChartData.lowerOrderL_mem_fixedSubmodule hw

variable (A μ p k) in
/-- The continuous inclusion of the `(0,1)`-forms of order `k + 1` into those of order `k`. -/
def zeroOneLowerOrderL :
    zeroOneSobolevSections A μ p (k + 1) →L[ℝ] zeroOneSobolevSections A μ p k :=
  A.tangentHom.sectionChartData.fixedLowerOrderL μ p k complexAntilinearPartL

/-- The inclusion of `(0,1)`-forms forgets the highest derivative. -/
@[simp]
theorem coe_zeroOneLowerOrderL (w : zeroOneSobolevSections A μ p (k + 1)) :
    (zeroOneLowerOrderL A μ p k w : SobolevSection A.tangentHom μ p k) =
      A.tangentHom.sectionChartData.lowerOrderL μ p k w :=
  SectionChartData.coe_fixedLowerOrderL _ w

/-- The `(0,1)`-projection commutes with forgetting the highest derivative. -/
theorem zeroOneLowerOrderL_zeroOnePartSobolevL (w : SobolevSection A.tangentHom μ p (k + 1)) :
    zeroOneLowerOrderL A μ p k (zeroOnePartSobolevL A μ p (k + 1) w) =
      zeroOnePartSobolevL A μ p k (A.tangentHom.sectionChartData.lowerOrderL μ p k w) :=
  A.tangentHom.sectionChartData.fixedLowerOrderL_projFixedL
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ y _ ↦ sectionChartData_coord_zeroOnePart A i θ y) w

/-! ### Lowering the integrability exponent -/

section Exponent

variable {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)]

/-- Lowering the integrability exponent of a `(0,1)`-form gives a `(0,1)`-form. -/
theorem ofExponentLEL_mem_zeroOneSobolevSections (hpq : p ≤ q)
    {w : SobolevSection A.tangentHom μ q k} (hw : w ∈ zeroOneSobolevSections A μ q k) :
    A.tangentHom.sectionChartData.ofExponentLEL μ k hpq w ∈ zeroOneSobolevSections A μ p k :=
  SectionChartData.ofExponentLEL_mem_fixedSubmodule hpq hw

variable (A μ k) in
/-- For `p ≤ q`, the continuous inclusion of `zeroOneSobolevSections A μ q k` into
`zeroOneSobolevSections A μ p k`. -/
def zeroOneOfExponentLEL (hpq : p ≤ q) :
    zeroOneSobolevSections A μ q k →L[ℝ] zeroOneSobolevSections A μ p k :=
  A.tangentHom.sectionChartData.fixedOfExponentLEL μ k complexAntilinearPartL hpq

@[simp]
theorem coe_zeroOneOfExponentLEL (hpq : p ≤ q) (w : zeroOneSobolevSections A μ q k) :
    (zeroOneOfExponentLEL A μ k hpq w : SobolevSection A.tangentHom μ p k) =
      A.tangentHom.sectionChartData.ofExponentLEL μ k hpq w :=
  SectionChartData.coe_fixedOfExponentLEL _ hpq w

/-- Lowering the integrability exponent on `zeroOneSobolevSections` is injective. -/
theorem zeroOneOfExponentLEL_injective (hpq : p ≤ q) :
    Function.Injective (zeroOneOfExponentLEL A μ k hpq) :=
  SectionChartData.fixedOfExponentLEL_injective _ hpq

@[simp]
theorem zeroOneOfExponentLEL_self (w : zeroOneSobolevSections A μ p k) :
    zeroOneOfExponentLEL A μ k le_rfl w = w :=
  SectionChartData.fixedOfExponentLEL_self _ w

@[simp]
theorem zeroOneOfExponentLEL_zeroOneOfExponentLEL (hpq : p ≤ q) (hqr : q ≤ r)
    (w : zeroOneSobolevSections A μ r k) :
    zeroOneOfExponentLEL A μ k hpq (zeroOneOfExponentLEL A μ k hqr w) =
      zeroOneOfExponentLEL A μ k (hpq.trans hqr) w :=
  SectionChartData.fixedOfExponentLEL_fixedOfExponentLEL _ hpq hqr w

/-- Lowering the integrability exponent commutes with lowering the Sobolev order on
`(0,1)`-forms. -/
theorem zeroOneLowerOrderL_zeroOneOfExponentLEL (hpq : p ≤ q)
    (w : zeroOneSobolevSections A μ q (k + 1)) :
    zeroOneLowerOrderL A μ p k (zeroOneOfExponentLEL A μ (k + 1) hpq w) =
      zeroOneOfExponentLEL A μ k hpq (zeroOneLowerOrderL A μ q k w) :=
  SectionChartData.fixedLowerOrderL_fixedOfExponentLEL _ hpq w

/-- The `(0,1)`-projection commutes with lowering the integrability exponent. -/
theorem zeroOneOfExponentLEL_zeroOnePartSobolevL (hpq : p ≤ q)
    (w : SobolevSection A.tangentHom μ q k) :
    zeroOneOfExponentLEL A μ k hpq (zeroOnePartSobolevL A μ q k w) =
      zeroOnePartSobolevL A μ p k (A.tangentHom.sectionChartData.ofExponentLEL μ k hpq w) :=
  A.tangentHom.sectionChartData.fixedOfExponentLEL_projFixedL
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ y _ ↦ sectionChartData_coord_zeroOnePart A i θ y) hpq w

end Exponent

/-! ### Smooth scalar multiplication -/

section SMul

variable {φ ψ : M → ℝ}

/-- Multiplying a Sobolev `(0,1)`-form by a smooth function `φ : M → ℝ` gives a `(0,1)`-form. -/
theorem contMDiffSMulL_mem_zeroOneSobolevSections (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    {w : SobolevSection A.tangentHom μ p k} (hw : w ∈ zeroOneSobolevSections A μ p k) :
    SobolevSection.contMDiffSMulL A.tangentHom μ p k hφ w ∈ zeroOneSobolevSections A μ p k :=
  SectionChartData.smulEnd_mem_fixedSubmodule
    (SobolevSection.chartValueL_contMDiffSMulL_ae hφ) hw

variable (A μ p k) in
/-- Multiplication by a smooth function `φ : M → ℝ` as a continuous linear endomorphism of
`zeroOneSobolevSections A μ p k`. -/
def zeroOneContMDiffSMulL (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ) :
    zeroOneSobolevSections A μ p k →L[ℝ] zeroOneSobolevSections A μ p k :=
  A.tangentHom.sectionChartData.fixedSMulEndL μ p k complexAntilinearPartL
    (SobolevSection.contMDiffSMulL A.tangentHom μ p k hφ)
    (SobolevSection.chartValueL_contMDiffSMulL_ae hφ)

@[simp]
theorem coe_zeroOneContMDiffSMulL (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (w : zeroOneSobolevSections A μ p k) :
    (zeroOneContMDiffSMulL A μ p k hφ w : SobolevSection A.tangentHom μ p k) =
      SobolevSection.contMDiffSMulL A.tangentHom μ p k hφ w :=
  SectionChartData.coe_fixedSMulEndL _ _ _ w

@[simp]
theorem zeroOneContMDiffSMulL_const (c : ℝ) :
    zeroOneContMDiffSMulL A μ p k (contMDiff_const (c := c)) = c • ContinuousLinearMap.id ℝ _ :=
  SectionChartData.fixedSMulEndL_eq_smul_id _ _ _
    (SobolevSection.contMDiffSMulL_const (A := A.tangentHom) (μ := μ) (p := p) (k := k) c)

/-- Smooth multiplication on `zeroOneSobolevSections` is additive in the multiplier. -/
theorem zeroOneContMDiffSMulL_add (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ ψ) :
    zeroOneContMDiffSMulL A μ p k (hφ.add hψ) =
      zeroOneContMDiffSMulL A μ p k hφ + zeroOneContMDiffSMulL A μ p k hψ :=
  SectionChartData.fixedSMulEndL_eq_add _ _ _ _
    (SobolevSection.contMDiffSMulL_add (A := A.tangentHom) (μ := μ) (p := p) (k := k) hφ hψ)

/-- Smooth multiplication on `zeroOneSobolevSections` sends products to compositions. -/
theorem zeroOneContMDiffSMulL_mul (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (hψ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ ψ) :
    zeroOneContMDiffSMulL A μ p k (hφ.mul hψ) =
      (zeroOneContMDiffSMulL A μ p k hφ).comp (zeroOneContMDiffSMulL A μ p k hψ) :=
  SectionChartData.fixedSMulEndL_eq_comp _ _ _ _
    (SobolevSection.contMDiffSMulL_mul (A := A.tangentHom) (μ := μ) (p := p) (k := k) hφ hψ)

/-- Lowering the Sobolev order commutes with smooth multiplication on `(0,1)`-forms. -/
theorem zeroOneLowerOrderL_zeroOneContMDiffSMulL (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (w : zeroOneSobolevSections A μ p (k + 1)) :
    zeroOneLowerOrderL A μ p k (zeroOneContMDiffSMulL A μ p (k + 1) hφ w) =
      zeroOneContMDiffSMulL A μ p k hφ (zeroOneLowerOrderL A μ p k w) :=
  SectionChartData.fixedLowerOrderL_fixedSMulEndL _ _ _ w

/-- Lowering the integrability exponent commutes with smooth multiplication on `(0,1)`-forms. -/
theorem zeroOneOfExponentLEL_zeroOneContMDiffSMulL {q : ℝ≥0∞} [Fact (1 ≤ q)] (hpq : p ≤ q)
    (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ) (w : zeroOneSobolevSections A μ q k) :
    zeroOneOfExponentLEL A μ k hpq (zeroOneContMDiffSMulL A μ q k hφ w) =
      zeroOneContMDiffSMulL A μ p k hφ (zeroOneOfExponentLEL A μ k hpq w) :=
  SectionChartData.fixedOfExponentLEL_fixedSMulEndL _ hpq _ _ w

/-- The `(0,1)`-projection commutes with multiplication by a smooth real-valued function. -/
theorem zeroOneContMDiffSMulL_zeroOnePartSobolevL (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ φ)
    (w : SobolevSection A.tangentHom μ p k) :
    zeroOneContMDiffSMulL A μ p k hφ (zeroOnePartSobolevL A μ p k w) =
      zeroOnePartSobolevL A μ p k (SobolevSection.contMDiffSMulL A.tangentHom μ p k hφ w) :=
  A.tangentHom.sectionChartData.fixedSMulEndL_projFixedL
    (ContinuousLinearMap.ext complexAntilinearPartL_complexAntilinearPartL)
    (fun i θ y _ ↦ sectionChartData_coord_zeroOnePart A i θ y) _ _ w

end SMul

end ZeroOne

end TauCeti
