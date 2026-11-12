/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
public import TauCeti.Topology.VectorBundle.RestrictScalars
import TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars

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
`(0,1)`-projection `η ↦ ½ (η + i • η ∘ i)` acts on chart readings by a constant linear map of the
model fibre `ℂ →L[ℝ] F`. The space `TauCeti.zeroOneSobolevSections A μ p k` consists of the
elements whose chart data are complex antilinear almost everywhere in every chart. It is the
kernel of continuous linear maps, hence closed and complete. Applying the constant linear map to
the components in every chart gives a continuous projection onto it
(`TauCeti.zeroOnePartSobolevL`), which lifts the pointwise `(0,1)`-projection
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart`; so the subspace is complemented.

## Main definitions

* `TauCeti.zeroOneSobolevSections A μ p k`: the `(0,1)`-forms in `W^{k,p}` of `V`-valued
  one-forms.
* `TauCeti.zeroOnePartSobolevL`: the continuous `(0,1)`-projection onto it.
* `TauCeti.zeroOneLowerOrderL`: the inclusion of order `k + 1` into order `k`.

## Main results

* `TauCeti.mem_zeroOneSobolevSections_iff`: membership is complex antilinearity of the chart data
  almost everywhere.
* `TauCeti.mem_zeroOneSobolevSections_iff_isZeroOneForm`: an element whose chart data are the
  readings of a one-form `θ` is a `(0,1)`-form exactly when `θ` is a `(0,1)`-form almost
  everywhere in every chart.
* `TauCeti.isClosed_zeroOneSobolevSections`, `TauCeti.zeroOneSobolevSections.instCompleteSpace`:
  the subspace is closed and complete.
* `TauCeti.zeroOnePartSobolevL_coe`, `TauCeti.closedComplemented_zeroOneSobolevSections`: the
  projection fixes `(0,1)`-forms, and the subspace is complemented.
* `TauCeti.chartValueL_zeroOnePartSobolevL_ae_coord`: the projection lifts the pointwise
  `(0,1)`-projection of one-forms.
* `TauCeti.mem_zeroOneSobolevSections_of_isZeroOneForm`: an element whose chart data are the
  readings of a `(0,1)`-form, for instance of a smooth one, is a Sobolev `(0,1)`-form.
* `TauCeti.zeroOneLowerOrderL_zeroOnePartSobolevL`: the projection commutes with lowering the
  order.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1 and C.2.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ENNReal ContDiff TauCeti.ComplexManifold

universe u

namespace TauCeti

section ZeroOne

open SmoothAlmostComplexStructure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, IsScalarTower ℝ ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, ContinuousSMul ℂ (V x)] [FiberBundle F V] [VectorBundle ℂ F V]

local instance instVectorBundleRealZeroOneForm : VectorBundle ℝ F V :=
  VectorBundle.restrictScalars ℝ ℂ F V

/-! ### The `(0,1)`-projection on the model fibre -/

variable (F) in
/-- The `(0,1)`-projection `η ↦ ½ (η + i • η ∘ i)` of real linear maps `ℂ →L[ℝ] F`: the complex
antilinear part `TauCeti.complexAntilinearPartLinearMap` for multiplication by `i` on `ℂ` and on
`F`, on continuous linear maps. -/
private def modelZeroOnePart : (ℂ →L[ℝ] F) →L[ℝ] (ℂ →L[ℝ] F) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (ℂ →ₗ[ℝ] F) ≃ₗ[ℝ] ℂ →L[ℝ] F).toLinearMap ∘ₗ
      complexAntilinearPartLinearMap (DistribSMul.toLinearMap ℝ ℂ Complex.I)
        (DistribSMul.toLinearMap ℝ F Complex.I) ∘ₗ ContinuousLinearMap.coeLM ℝ)

private theorem toLinearMap_modelZeroOnePart (η : ℂ →L[ℝ] F) :
    (modelZeroOnePart F η : ℂ →ₗ[ℝ] F) = complexAntilinearPart
      (DistribSMul.toLinearMap ℝ ℂ Complex.I) (DistribSMul.toLinearMap ℝ F Complex.I) η :=
  rfl

private theorem modelZeroOnePart_apply (η : ℂ →L[ℝ] F) (v : ℂ) :
    modelZeroOnePart F η v = (2⁻¹ : ℝ) • (η v + Complex.I • η (Complex.I • v)) :=
  (LinearMap.congr_fun (toLinearMap_modelZeroOnePart η) v).trans
    (complexAntilinearPart_apply _ _ _ v)

/-- A real linear map `ℂ →L[ℝ] F` is fixed by the `(0,1)`-projection exactly when it is complex
antilinear. -/
private theorem modelZeroOnePart_eq_self_iff {η : ℂ →L[ℝ] F} :
    modelZeroOnePart F η = η ↔ ∀ v, η (Complex.I • v) = -(Complex.I • η v) := by
  rw [← ContinuousLinearMap.coe_inj, toLinearMap_modelZeroOnePart]
  refine ⟨fun h ↦ (h ▸ complexAntilinearPart_isComplexAntilinear
    Complex.toLinearMap_I_comp_toLinearMap_I Complex.toLinearMap_I_comp_toLinearMap_I _).apply,
    fun h ↦ (isComplexAntilinear_of_apply h).complexAntilinearPart_eq
      Complex.toLinearMap_I_comp_toLinearMap_I⟩

/-- The `(0,1)`-projection of a real linear map `ℂ →L[ℝ] F` is complex antilinear. -/
private theorem modelZeroOnePart_antilinear (η : ℂ →L[ℝ] F) (v : ℂ) :
    modelZeroOnePart F η (Complex.I • v) = -(Complex.I • modelZeroOnePart F η v) :=
  (toLinearMap_modelZeroOnePart η ▸ complexAntilinearPart_isComplexAntilinear
    Complex.toLinearMap_I_comp_toLinearMap_I Complex.toLinearMap_I_comp_toLinearMap_I _).apply v

/-! ### Chart readings of `(0,1)`-forms -/

variable (A : FiniteBundleAtlas ℂ M F V)

/-- On the image of a chart, the `(0,1)`-part of a one-form is read as the `(0,1)`-projection of
its reading. -/
private theorem coord_tangentHom_zeroOnePart (i : Fin A.n)
    (θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) {y : ℂ} (hy : y ∈ A.image i) :
    A.tangentHom.coord i (fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x)) y =
      modelZeroOnePart F (A.tangentHom.coord i θ y) := by
  have hx : (A.chart i).symm y ∈ (chartAt ℂ (A.center i)).source :=
    A.dom_subset_chart_source i (A.symm_mem_dom hy)
  have hS (a v : ℂ) : (tangentBundleCore 𝓘(ℝ, ℂ) M).coordChange (achart ℂ (A.center i))
      (achart ℂ ((A.chart i).symm y)) ((A.chart i).symm y) (a • v) =
      a • (tangentBundleCore 𝓘(ℝ, ℂ) M).coordChange (achart ℂ (A.center i))
        (achart ℂ ((A.chart i).symm y)) ((A.chart i).symm y) v :=
    tangentCoordChange_smul ℝ (𝕜' := ℂ) ⟨hx, mem_chart_source ℂ _⟩ a v
  rw [FiniteBundleAtlas.coord_tangentHom, FiniteBundleAtlas.coord_tangentHom]
  ext v
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    modelZeroOnePart_apply, zeroOnePart_apply]
  -- `TangentSpace 𝓘(ℝ, ℂ) x` is `ℂ` by definition but carries no `ℂ`-action, so the readings of
  -- tangent vectors, the complex linearity `hS` of the real tangent coordinate change and the
  -- almost complex structure `v ↦ i • v` can only be matched up to this definitional equality:
  -- `erw` rewrites the coordinate change, whose coercion is to `TangentSpace`, by its `ℂ`-valued
  -- form, and the final `rfl` identifies `(i • id) w` on `TangentSpace` with `i • w` on `ℂ`.
  erw [TangentBundle.symmL_trivializationAt_eq_core hx, hS]
  rw [map_smul, map_add, Trivialization.coe_continuousLinearMapAt_restrictScalars ℝ ℂ, map_smul,
    toEndomorphism_ofComplexManifold]
  rfl

/-- On the image of a chart, a one-form is read as a complex antilinear map exactly when it is a
`(0,1)`-form at the corresponding point. -/
private theorem isZeroOneForm_iff_coord_tangentHom (i : Fin A.n)
    (θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x) {y : ℂ} (hy : y ∈ A.image i) :
    (ofComplexManifold ℂ M).IsZeroOneForm (θ ((A.chart i).symm y)) ↔
      ∀ v, A.tangentHom.coord i θ y (Complex.I • v) =
        -(Complex.I • A.tangentHom.coord i θ y v) := by
  rw [← modelZeroOnePart_eq_self_iff, ← coord_tangentHom_zeroOnePart A i θ hy,
    ← zeroOnePart_eq_self_iff, FiniteBundleAtlas.coord_tangentHom,
    FiniteBundleAtlas.coord_tangentHom]
  refine ⟨fun h ↦ by rw [h], fun h ↦ ?_⟩
  -- The reading at `y` is injective: both trivializations are isomorphisms at the point.
  have hdom := A.symm_mem_dom hy
  have h₁ : (A.chart i).symm y ∈
      (trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) (A.center i)).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact A.dom_subset_chart_source i hdom
  have h₂ : (A.chart i).symm y ∈ (trivializationAt F V (A.center i)).baseSet :=
    A.dom_subset_baseSet i hdom
  rw [ContinuousLinearMap.inCoordinates_eq h₁ h₂, ContinuousLinearMap.inCoordinates_eq h₁ h₂] at h
  exact (ContinuousLinearEquiv.arrowCongrEquiv _ _).injective h

omit [FiniteDimensional ℝ F] [∀ x, ContinuousSMul ℂ (V x)] in
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
  ⨅ i : Fin A.n, LinearMap.ker
    (((modelZeroOnePart F - ContinuousLinearMap.id ℝ _).compLpL p _).comp
      ((A.tangentHom.sectionChartData.chartValueL μ p k i).comp
        (A.tangentHom.sectionChartData.sobolevSections μ p k).subtypeL)).toLinearMap

variable {A μ p k}

omit [∀ x, ContinuousSMul ℂ (V x)] in
/-- An element of `W^{k,p}` of `V`-valued one-forms is a `(0,1)`-form exactly when its chart data
are complex antilinear almost everywhere on the image of every chart. -/
theorem mem_zeroOneSobolevSections_iff {w : SobolevSection A.tangentHom μ p k} :
    w ∈ zeroOneSobolevSections A μ p k ↔
      ∀ i, ∀ᵐ y ∂μ.restrict (A.tangentHom.sectionChartData.image i), ∀ v : ℂ,
        A.tangentHom.sectionChartData.chartValueL μ p k i w y (Complex.I • v) =
          -(Complex.I • A.tangentHom.sectionChartData.chartValueL μ p k i w y v) := by
  simp only [zeroOneSobolevSections, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun i ↦ ?_
  have hc := ContinuousLinearMap.coeFn_compLpL (p := p)
    (μ := μ.restrict (A.tangentHom.sectionChartData.image i))
    (modelZeroOnePart F - ContinuousLinearMap.id ℝ _)
    (A.tangentHom.sectionChartData.chartValueL μ p k i w)
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, Lp.eq_zero_iff_ae_eq_zero]
  have key : (fun y ↦ (modelZeroOnePart F - ContinuousLinearMap.id ℝ (ℂ →L[ℝ] F))
      (A.tangentHom.sectionChartData.chartValueL μ p k i w y))
        =ᵐ[μ.restrict (A.tangentHom.sectionChartData.image i)] 0 ↔
      ∀ᵐ y ∂μ.restrict (A.tangentHom.sectionChartData.image i), ∀ v : ℂ,
        A.tangentHom.sectionChartData.chartValueL μ p k i w y (Complex.I • v) =
          -(Complex.I • A.tangentHom.sectionChartData.chartValueL μ p k i w y v) := by
    refine Filter.eventually_congr (Filter.Eventually.of_forall fun y ↦ ?_)
    exact sub_eq_zero.trans modelZeroOnePart_eq_self_iff
  exact ⟨fun h ↦ key.1 (hc.symm.trans h), fun h ↦ hc.trans (key.2 h)⟩

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
  rw [h, isZeroOneForm_iff_coord_tangentHom A i θ (mem_image_of_mem_image_tangentHom hy)]

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

omit [∀ x, ContinuousSMul ℂ (V x)] in
/-- The `(0,1)`-forms form a closed subspace: it is the intersection of the kernels of continuous
linear maps. -/
theorem isClosed_zeroOneSobolevSections :
    IsClosed (zeroOneSobolevSections A μ p k : Set (SobolevSection A.tangentHom μ p k)) := by
  rw [zeroOneSobolevSections, Submodule.coe_iInf]
  exact isClosed_iInter fun i ↦ ContinuousLinearMap.isClosed_ker _

/-- **Completeness.** The Sobolev `(0,1)`-forms form a Banach space. -/
instance zeroOneSobolevSections.instCompleteSpace :
    CompleteSpace (zeroOneSobolevSections A μ p k) :=
  isClosed_zeroOneSobolevSections.completeSpace_coe

/-! ### The `(0,1)`-projection -/

variable (A μ p k) in
/-- The `(0,1)`-projection on `W^{k,p}` of `V`-valued one-forms, as an endomorphism. -/
private def zeroOnePartEnd :
    SobolevSection A.tangentHom μ p k →L[ℝ] SobolevSection A.tangentHom μ p k :=
  SectionChartData.constMapL μ p k (modelZeroOnePart F)
    (fun θ x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x)) fun i θ y hy ↦ by
      rw [A.tangentHom.sectionChartData_coord_of_mem _ hy,
        A.tangentHom.sectionChartData_coord_of_mem _ hy]
      exact coord_tangentHom_zeroOnePart A i θ (mem_image_of_mem_image_tangentHom hy)

private theorem chartValueL_zeroOnePartEnd_ae (w : SobolevSection A.tangentHom μ p k)
    (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i (zeroOnePartEnd A μ p k w)
      =ᵐ[μ.restrict (A.tangentHom.sectionChartData.image i)]
        fun y ↦ modelZeroOnePart F (A.tangentHom.sectionChartData.chartValueL μ p k i w y) :=
  SectionChartData.chartValueL_constMapL_ae μ p k _ w i

private theorem zeroOnePartEnd_mem (w : SobolevSection A.tangentHom μ p k) :
    zeroOnePartEnd A μ p k w ∈ zeroOneSobolevSections A μ p k :=
  mem_zeroOneSobolevSections_iff.2 fun i ↦ (chartValueL_zeroOnePartEnd_ae w i).mono
    fun y hy v ↦ by
      rw [hy]
      exact modelZeroOnePart_antilinear _ v

private theorem zeroOnePartEnd_of_mem {w : SobolevSection A.tangentHom μ p k}
    (hw : w ∈ zeroOneSobolevSections A μ p k) : zeroOnePartEnd A μ p k w = w := by
  obtain ⟨s, hs⟩ := A.tangentHom.sectionChartData.exists_section μ p k w
  refine SectionChartData.eq_of_ae_eq_coord (s := s) (fun i ↦ ?_) hs
  filter_upwards [chartValueL_zeroOnePartEnd_ae w i, mem_zeroOneSobolevSections_iff.1 hw i,
    hs i] with y h₁ h₂ h₃
  rw [h₁, modelZeroOnePart_eq_self_iff.2 h₂, h₃]

variable (A μ p k) in
/-- **The `(0,1)`-projection.** The continuous projection of `W^{k,p}` of `V`-valued one-forms onto
the `(0,1)`-forms, applying `η ↦ ½ (η + i • η ∘ i)` to the chart data. It lifts the pointwise
`(0,1)`-projection `TauCeti.SmoothAlmostComplexStructure.zeroOnePart`
(`TauCeti.chartValueL_zeroOnePartSobolevL_ae_coord`) and fixes the `(0,1)`-forms
(`TauCeti.zeroOnePartSobolevL_coe`). -/
def zeroOnePartSobolevL : SobolevSection A.tangentHom μ p k →L[ℝ] zeroOneSobolevSections A μ p k :=
  (zeroOnePartEnd A μ p k).codRestrict _ zeroOnePartEnd_mem

private theorem coe_zeroOnePartSobolevL (w : SobolevSection A.tangentHom μ p k) :
    (zeroOnePartSobolevL A μ p k w : SobolevSection A.tangentHom μ p k) =
      zeroOnePartEnd A μ p k w :=
  rfl

/-- The chart data of the `(0,1)`-projection of `w` are the `(0,1)`-projections
`η ↦ ½ (η + i • η ∘ i)` of the chart data of `w`. -/
theorem chartValueL_zeroOnePartSobolevL_ae (w : SobolevSection A.tangentHom μ p k)
    (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i (zeroOnePartSobolevL A μ p k w)
      =ᵐ[μ.restrict (A.tangentHom.sectionChartData.image i)] fun y ↦
        (2⁻¹ : ℝ) • (A.tangentHom.sectionChartData.chartValueL μ p k i w y + Complex.I •
          (A.tangentHom.sectionChartData.chartValueL μ p k i w y).comp
            (Complex.I • ContinuousLinearMap.id ℝ ℂ)) :=
  (chartValueL_zeroOnePartEnd_ae w i).mono fun y hy ↦ by
    rw [coe_zeroOnePartSobolevL, hy]
    ext v
    simp only [modelZeroOnePart_apply, add_apply, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]

/-- **Lifting the pointwise projection.** If the chart data of `w` are the readings of a one-form
`θ`, the chart data of its `(0,1)`-projection are the readings of the `(0,1)`-part of `θ`. -/
theorem chartValueL_zeroOnePartSobolevL_ae_coord {w : SobolevSection A.tangentHom μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] V x}
    (hw : ∀ i, A.tangentHom.sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict (A.tangentHom.sectionChartData.image i)] A.tangentHom.coord i θ) (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i (zeroOnePartSobolevL A μ p k w)
      =ᵐ[μ.restrict (A.tangentHom.sectionChartData.image i)]
        A.tangentHom.coord i fun x ↦ (ofComplexManifold ℂ M).zeroOnePart (θ x) := by
  filter_upwards [chartValueL_zeroOnePartEnd_ae w i, hw i,
    ae_restrict_mem (A.tangentHom.sectionChartData.image i).isOpen.measurableSet] with y h₁ h₂ hy
  rw [coe_zeroOnePartSobolevL, h₁, h₂,
    coord_tangentHom_zeroOnePart A i θ (mem_image_of_mem_image_tangentHom hy)]

/-- The `(0,1)`-projection fixes the `(0,1)`-forms. -/
@[simp]
theorem zeroOnePartSobolevL_coe (w : zeroOneSobolevSections A μ p k) :
    zeroOnePartSobolevL A μ p k w = w :=
  Subtype.ext (zeroOnePartEnd_of_mem w.2)

/-- An element of `W^{k,p}` of `V`-valued one-forms is fixed by the `(0,1)`-projection exactly when
it is a `(0,1)`-form. -/
theorem coe_zeroOnePartSobolevL_eq_self_iff {w : SobolevSection A.tangentHom μ p k} :
    (zeroOnePartSobolevL A μ p k w : SobolevSection A.tangentHom μ p k) = w ↔
      w ∈ zeroOneSobolevSections A μ p k :=
  ⟨fun h ↦ h ▸ (zeroOnePartSobolevL A μ p k w).2, zeroOnePartEnd_of_mem⟩

/-- The `(0,1)`-projection is onto the `(0,1)`-forms. -/
theorem zeroOnePartSobolevL_surjective : Function.Surjective (zeroOnePartSobolevL A μ p k) :=
  fun w ↦ ⟨w, zeroOnePartSobolevL_coe w⟩

/-- **Complemented.** The `(0,1)`-forms are a complemented subspace of `W^{k,p}` of `V`-valued
one-forms, with the `(0,1)`-projection as a continuous projection onto it. -/
theorem closedComplemented_zeroOneSobolevSections :
    (zeroOneSobolevSections A μ p k).ClosedComplemented :=
  ⟨zeroOnePartSobolevL A μ p k, zeroOnePartSobolevL_coe⟩

/-! ### Lowering the order -/

omit [∀ x, ContinuousSMul ℂ (V x)] in
/-- Forgetting the highest derivative of a `(0,1)`-form gives a `(0,1)`-form. -/
theorem lowerOrderL_mem_zeroOneSobolevSections {w : SobolevSection A.tangentHom μ p (k + 1)}
    (hw : w ∈ zeroOneSobolevSections A μ p (k + 1)) :
    A.tangentHom.sectionChartData.lowerOrderL μ p k w ∈ zeroOneSobolevSections A μ p k := by
  rw [mem_zeroOneSobolevSections_iff] at hw ⊢
  intro i
  rw [SectionChartData.chartValueL_lowerOrderL_coe]
  exact hw i

variable (A μ p k) in
/-- The continuous inclusion of the `(0,1)`-forms of order `k + 1` into those of order `k`. -/
def zeroOneLowerOrderL :
    zeroOneSobolevSections A μ p (k + 1) →L[ℝ] zeroOneSobolevSections A μ p k :=
  ((A.tangentHom.sectionChartData.lowerOrderL μ p k).comp
    (zeroOneSobolevSections A μ p (k + 1)).subtypeL).codRestrict _
      fun w ↦ lowerOrderL_mem_zeroOneSobolevSections w.2

omit [∀ x, ContinuousSMul ℂ (V x)] in
/-- The inclusion of `(0,1)`-forms forgets the highest derivative. -/
@[simp]
theorem coe_zeroOneLowerOrderL (w : zeroOneSobolevSections A μ p (k + 1)) :
    (zeroOneLowerOrderL A μ p k w : SobolevSection A.tangentHom μ p k) =
      A.tangentHom.sectionChartData.lowerOrderL μ p k w :=
  ContinuousLinearMap.coe_codRestrict_apply _ _ _ _

/-- The `(0,1)`-projection commutes with forgetting the highest derivative. -/
theorem zeroOneLowerOrderL_zeroOnePartSobolevL (w : SobolevSection A.tangentHom μ p (k + 1)) :
    zeroOneLowerOrderL A μ p k (zeroOnePartSobolevL A μ p (k + 1) w) =
      zeroOnePartSobolevL A μ p k (A.tangentHom.sectionChartData.lowerOrderL μ p k w) :=
  Subtype.ext (SectionChartData.lowerOrderL_constMapL μ p k _ w)

end ZeroOne

end TauCeti
