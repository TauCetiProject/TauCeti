/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Smooth bundle maps acting on Sobolev sections

Let `M` be a smooth manifold without boundary modelled on a finite-dimensional real inner product
space `E`, and let `Φ x : V x →L[ℝ] W x` be a smooth morphism between smooth real vector bundles
with finite-dimensional model fibres `F` and `G`, a smooth section of the hom bundle. This file
shows that `s ↦ Φ s` is a continuous linear map `W^{k,p}(V) → W^{k,p}(W)` for every order `k` and
every `1 ≤ p ≤ ∞`, and that `θ ↦ Φ ∘ θ` is a continuous linear map between the Sobolev spaces of
`V`-valued and of `W`-valued one-forms. When every `Φ x` is invertible these maps are isomorphisms
of Banach spaces.

The Sobolev spaces are built on finite bundle atlases. The space of `W` uses the charts of the
atlas `A` of `V`, as the atlas `A.ofBaseSet h` of `W`, whose chart domains have closures in the
base sets of the preferred trivializations of `W` (such joint atlases exist on every compact
Hausdorff manifold, `TauCeti.FiniteBundleAtlas.exists_closure_dom_subset_baseSet`). In chart `i`
the reading of `Φ s` is the reading of `Φ` in the hom-bundle atlas `A.hom h`, a smooth
operator-valued function, applied to the reading of `s`
(`TauCeti.FiniteBundleAtlas.coord_hom_apply`), so the map multiplies the chart data by a smooth
operator coefficient (`TauCeti.Wkp.contDiffOnCLMApplyL`).

This is first done for abstract chart data (`TauCeti.SectionChartData.CoeffMap`): a map of
sections whose readings in each chart of the target are a smooth operator coefficient applied to
the readings in a chart of the source with larger image acts continuously on the Sobolev sections
(`TauCeti.SectionChartData.CoeffMap.mapL`).

## Main definitions

* `TauCeti.SectionChartData.CoeffMap`: a map of sections read in charts as a smooth operator
  coefficient.
* `TauCeti.SectionChartData.CoeffMap.mapL`: its action on Sobolev sections.
* `TauCeti.SobolevSection.bundleMapL`: the action `s ↦ Φ s` of a smooth bundle morphism on
  `W^{k,p}` sections, and `TauCeti.SobolevSection.tangentHomMapL` its action `θ ↦ Φ ∘ θ` on
  `W^{k,p}` one-forms.
* `TauCeti.SobolevSection.bundleEquivL`, `TauCeti.SobolevSection.tangentHomEquivL`: the
  isomorphisms induced by a smooth bundle isomorphism.

## Main results

* `TauCeti.SectionChartData.CoeffMap.chartValueL_mapL_ae_coord`: the image of an element with
  section `s` has section `Ψ.toFun s`.
* `TauCeti.SobolevSection.chartValueL_bundleMapL_ae_coord`,
  `TauCeti.SobolevSection.chartValueL_tangentHomMapL_ae_coord`: the images of an element with
  section `s` and of a one-form with section `θ` have sections `Φ s` and `Φ ∘ θ`.
* `TauCeti.SobolevSection.bundleMapL_ofContMDiffSection`: on smooth sections the map is `Φ`.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

/-! ### Inverses of smooth bundle isomorphisms -/

section Inverse

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {W : B → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, AddCommGroup (W x)]
  [∀ x, Module 𝕜 (W x)] [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul 𝕜 (W x)] [FiberBundle G W] [VectorBundle 𝕜 G W]
  {n : WithTop ℕ∞} {Φ : ∀ x, V x ≃L[𝕜] W x}

/-- **The inverse of a `Cⁿ` bundle isomorphism is `Cⁿ`.** If a family of fibrewise continuous
linear equivalences is a `Cⁿ` section of the hom bundle, so is the family of their inverses. -/
theorem _root_.ContMDiff.clm_bundle_equiv_symm
    (hΦ : ContMDiff IB (IB.prod 𝓘(𝕜, F →L[𝕜] G)) n fun x ↦
      TotalSpace.mk' (F →L[𝕜] G) (E := fun x ↦ V x →L[𝕜] W x) x (Φ x : V x →L[𝕜] W x)) :
    ContMDiff IB (IB.prod 𝓘(𝕜, G →L[𝕜] F)) n fun x ↦
      TotalSpace.mk' (G →L[𝕜] F) (E := fun x ↦ W x →L[𝕜] V x) x ((Φ x).symm : W x →L[𝕜] V x) := by
  simpa only [ContinuousLinearMap.inverse_equiv] using
    hΦ.clm_bundle_inverse fun _ ↦ ContinuousLinearMap.isInvertible_equiv

end Inverse

namespace SectionChartData

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {S : Type*} [AddCommGroup S] [Module ℝ S] {S' : Type*} [AddCommGroup S'] [Module ℝ S']

/-- **Maps of sections read as smooth operator coefficients.** A map `toFun` from the sections of
chart data `C` to those of chart data `C'` such that, on the image of each chart `i` of `C'`, the
reading of `toFun s` is a smooth operator-valued function `coeff i` applied to the reading of `s`
in a chart `chart i` of `C` whose image contains that of `i`. The coefficient is smooth on an open
set `domain i` containing the compact closure of the image of chart `i`. -/
structure CoeffMap (C : SectionChartData E F S) (C' : SectionChartData E G S') where
  /-- The map of sections. -/
  toFun : S → S'
  /-- The chart of `C` in which the readings in chart `i` of `C'` are computed. -/
  chart : Fin C'.n → Fin C.n
  image_le : ∀ i, C'.image i ≤ C.image (chart i)
  isCompact_closure_image : ∀ i, IsCompact (closure (C'.image i : Set E))
  /-- An open set on which the coefficient of chart `i` is smooth. -/
  domain : Fin C'.n → Set E
  isOpen_domain : ∀ i, IsOpen (domain i)
  closure_image_subset_domain : ∀ i, closure (C'.image i : Set E) ⊆ domain i
  /-- The operator coefficient of chart `i`. -/
  coeff : Fin C'.n → E → F →L[ℝ] G
  contDiffOn_coeff : ∀ i, ContDiffOn ℝ ∞ (coeff i) (domain i)
  coord_toFun : ∀ i s, ∀ y ∈ C'.image i, C'.coord i (toFun s) y = coeff i y (C.coord (chart i) s y)

namespace CoeffMap

variable {C : SectionChartData E F S} {C' : SectionChartData E G S'} (Ψ : C.CoeffMap C')
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- The action of `Ψ` on tuples of components: in chart `i` of `C'`, the components of chart
`Ψ.chart i` of `C` are restricted to the image of chart `i` and multiplied by the matrix of the
coefficient `Ψ.coeff i`. -/
def dataL : C.SobolevData μ p k →L[ℝ] C'.SobolevData μ p k :=
  ContinuousLinearMap.pi fun i ↦
    (Wkp.contDiffOnCLMApplyL (Ψ.isOpen_domain i).uniqueDiffOn (Ψ.isCompact_closure_image i)
      (Ψ.closure_image_subset_domain i) k (finBasis ℝ F) (finBasis ℝ G)
      (Ψ.contDiffOn_coeff i)).comp
    ((ContinuousLinearMap.piMap fun _ : Fin (finrank ℝ F) ↦ Wkp.restrictL (Ψ.image_le i) k).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun i : Fin C.n ↦
        ∀ _ : Fin (finrank ℝ F), Wkp μ (C.image i) p k) (Ψ.chart i)))

theorem dataL_apply (w : C.SobolevData μ p k) (i : Fin C'.n) :
    Ψ.dataL μ p k w i =
      Wkp.contDiffOnCLMApplyL (Ψ.isOpen_domain i).uniqueDiffOn (Ψ.isCompact_closure_image i)
        (Ψ.closure_image_subset_domain i) k (finBasis ℝ F) (finBasis ℝ G) (Ψ.contDiffOn_coeff i)
        fun l ↦ Wkp.restrictL (Ψ.image_le i) k (w (Ψ.chart i) l) :=
  (rfl)

/-- **The chart formula.** In chart `i` of `C'`, the chart data of the image of a tuple are the
coefficient `Ψ.coeff i` applied to its chart data in chart `Ψ.chart i` of `C`. -/
theorem chartValueL_dataL_ae (w : C.SobolevData μ p k) (i : Fin C'.n) :
    C'.chartValueL μ p k i (Ψ.dataL μ p k w) =ᵐ[μ.restrict (C'.image i)]
      fun y ↦ Ψ.coeff i y (C.chartValueL μ p k (Ψ.chart i) w y) := by
  have h₂ := ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (Ψ.image_le i))
    (C.chartValueL_apply_ae μ p k (Ψ.chart i) w)
  have h₃ : ∀ᵐ y ∂μ.restrict (C'.image i), ∀ m,
      Wkp.value k (Ψ.dataL μ p k w i m) y = (finBasis ℝ G).repr (Ψ.coeff i y
        (∑ l, Wkp.value k (Wkp.restrictL (Ψ.image_le i) k (w (Ψ.chart i) l)) y •
          finBasis ℝ F l)) m :=
    ae_all_iff.2 fun m ↦ by
      rw [dataL_apply]
      exact Wkp.value_contDiffOnCLMApplyL_ae _ _ _ k _ _ _ _ m
  have h₄ : ∀ᵐ y ∂μ.restrict (C'.image i), ∀ l,
      Wkp.value k (Wkp.restrictL (Ψ.image_le i) k (w (Ψ.chart i) l)) y =
        Wkp.value k (w (Ψ.chart i) l) y :=
    ae_all_iff.2 fun l ↦ Wkp.value_restrictL_ae (Ψ.image_le i) k _
  filter_upwards [C'.chartValueL_apply_ae μ p k i (Ψ.dataL μ p k w), h₂, h₃, h₄]
    with y h₁ h₂ h₃ h₄
  simp only [h₁, h₂, h₃, h₄, Basis.sum_repr]

/-- The image of the components of a section `s` consists of the components of `Ψ.toFun s`. -/
theorem chartValueL_dataL_ae_coord {w : C.SobolevData μ p k} {s : S}
    (hs : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) (i : Fin C'.n) :
    C'.chartValueL μ p k i (Ψ.dataL μ p k w) =ᵐ[μ.restrict (C'.image i)]
      C'.coord i (Ψ.toFun s) := by
  filter_upwards [Ψ.chartValueL_dataL_ae μ p k w i,
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 (Ψ.image_le i))
      (hs (Ψ.chart i)), ae_restrict_mem (C'.image i).isOpen.measurableSet] with y h₁ h₂ hy
  rw [h₁, h₂, Ψ.coord_toFun i s y hy]

/-- **The action on Sobolev sections.** The continuous linear map sending an element of
`W^{k,p}` for `C` with section `s` to the element of `W^{k,p}` for `C'` with section `Ψ.toFun s`
(`TauCeti.SectionChartData.CoeffMap.chartValueL_mapL_ae_coord`). -/
def mapL : C.sobolevSections μ p k →L[ℝ] C'.sobolevSections μ p k :=
  ((Ψ.dataL μ p k).comp (C.sobolevSections μ p k).subtypeL).codRestrict _ fun w ↦ by
    obtain ⟨s, hs⟩ := C.exists_section μ p k w
    exact (C'.mem_sobolevSections_iff μ p k).2 ⟨Ψ.toFun s, Ψ.chartValueL_dataL_ae_coord μ p k hs⟩

variable {Ψ μ p k} in
/-- The image under `Ψ.mapL` of an element with section `s` has section `Ψ.toFun s`. -/
theorem chartValueL_mapL_ae_coord {w : C.sobolevSections μ p k} {s : S}
    (hs : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) (i : Fin C'.n) :
    C'.chartValueL μ p k i (Ψ.mapL μ p k w) =ᵐ[μ.restrict (C'.image i)]
      C'.coord i (Ψ.toFun s) :=
  Ψ.chartValueL_dataL_ae_coord μ p k hs i

/-- If the map of sections of `Ψ'` undoes that of `Ψ`, then `Ψ'.mapL` undoes `Ψ.mapL`. -/
theorem mapL_mapL {Ψ' : C'.CoeffMap C} (h : ∀ s, Ψ'.toFun (Ψ.toFun s) = s)
    (w : C.sobolevSections μ p k) : Ψ'.mapL μ p k (Ψ.mapL μ p k w) = w := by
  obtain ⟨s, hs⟩ := C.exists_section μ p k w
  refine eq_of_ae_eq_coord (s := s) (fun i ↦ ?_) hs
  rw [← h s]
  exact chartValueL_mapL_ae_coord (chartValueL_mapL_ae_coord hs) i

/-- **Isomorphisms of Sobolev sections.** Maps of sections read as smooth operator coefficients
which are mutually inverse induce an isomorphism of the Sobolev sections. -/
def mapEquivL (Ψ' : C'.CoeffMap C) (h : ∀ s, Ψ'.toFun (Ψ.toFun s) = s)
    (h' : ∀ s, Ψ.toFun (Ψ'.toFun s) = s) :
    C.sobolevSections μ p k ≃L[ℝ] C'.sobolevSections μ p k :=
  .ofContinuousLinearMap (Ψ.mapL μ p k) (Ψ'.mapL μ p k)
    (ContinuousLinearMap.ext (Ψ'.mapL_mapL μ p k h'))
    (ContinuousLinearMap.ext (Ψ.mapL_mapL μ p k h))

@[simp]
theorem coe_mapEquivL (Ψ' : C'.CoeffMap C) (h : ∀ s, Ψ'.toFun (Ψ.toFun s) = s)
    (h' : ∀ s, Ψ.toFun (Ψ'.toFun s) = s) :
    (Ψ.mapEquivL μ p k Ψ' h h' : C.sobolevSections μ p k →L[ℝ] C'.sobolevSections μ p k) =
      Ψ.mapL μ p k :=
  (rfl)

@[simp]
theorem coe_mapEquivL_symm (Ψ' : C'.CoeffMap C) (h : ∀ s, Ψ'.toFun (Ψ.toFun s) = s)
    (h' : ∀ s, Ψ.toFun (Ψ'.toFun s) = s) :
    ((Ψ.mapEquivL μ p k Ψ' h h').symm :
      C'.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k) = Ψ'.mapL μ p k :=
  (rfl)

end CoeffMap

end SectionChartData

/-! ### Smooth bundle morphisms -/

namespace FiniteBundleAtlas

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, AddCommGroup (W x)]
  [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle ∞ G W 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt G W (A.center i)).baseSet)
  {Φ : ∀ x, V x →L[ℝ] W x}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ G] in
/-- The reading of a smooth bundle morphism `Φ` in a chart of the hom-bundle atlas is smooth on
the open set of points of the chart target lying over the base sets of both trivializations. -/
theorem contDiffOn_coord_hom
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x (Φ x))
    (i : Fin A.n) :
    ContDiffOn ℝ ∞ ((A.hom (𝕜 := ℝ) h).coord i Φ)
      (((A.hom (𝕜 := ℝ) h).chart i).target ∩
        ((A.hom (𝕜 := ℝ) h).chart i).symm ⁻¹' ((A.hom (𝕜 := ℝ) h).triv i).baseSet) :=
  (contDiffOn_trivialization_comp_chart_symm_of_contMDiff hΦ
    (IsManifold.chart_mem_maximalAtlas _) ((A.hom (𝕜 := ℝ) h).triv i)).congr fun y _ ↦
      (A.hom (𝕜 := ℝ) h).coord_def i Φ y

/-- **A smooth bundle morphism acts on sections by its chart readings.** The map `s ↦ Φ s` from
the sections of `V`, read in the charts of `A`, to those of `W`, read in the same charts as the
atlas `A.ofBaseSet h`, with the reading of `Φ` in the hom-bundle atlas `A.hom h` as coefficient. -/
def coeffMap
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x (Φ x)) :
    A.sectionChartData.CoeffMap (A.ofBaseSet h).sectionChartData where
  toFun s x := Φ x (s x)
  chart i := i
  image_le i := (image_ofBaseSet (h := h) i).le
  isCompact_closure_image i := (A.ofBaseSet h).isCompact_closure_image i
  domain i :=
    ((A.hom (𝕜 := ℝ) h).chart i).target ∩
      ((A.hom (𝕜 := ℝ) h).chart i).symm ⁻¹' ((A.hom (𝕜 := ℝ) h).triv i).baseSet
  isOpen_domain i :=
    ((A.hom (𝕜 := ℝ) h).chart i).isOpen_inter_preimage_symm ((A.hom (𝕜 := ℝ) h).triv i).open_baseSet
  closure_image_subset_domain i := by
    have heq : ((A.ofBaseSet h).sectionChartData.image i : Set E) = (A.hom (𝕜 := ℝ) h).image i :=
      congrArg SetLike.coe ((image_ofBaseSet (A := A) (h := h) i).trans
        (image_hom (𝕜 := ℝ) (A := A) (h := h) i).symm)
    rw [heq]
    exact (A.hom (𝕜 := ℝ) h).closure_image_subset_target_inter_preimage_baseSet i
  coeff i := (A.hom (𝕜 := ℝ) h).coord i Φ
  contDiffOn_coeff i := A.contDiffOn_coord_hom h hΦ i
  coord_toFun (i : Fin A.n) s y hy := by
    have hy' : y ∈ A.image i := by rwa [← image_ofBaseSet (h := h)]
    rw [sectionChartData_coord_of_mem _ _ hy, sectionChartData_coord_of_mem _ _ hy',
      A.coord_hom_apply h i Φ s hy']

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]

/-- **A smooth bundle morphism acts on one-forms by its chart readings.** The map `θ ↦ Φ ∘ θ` from
`V`-valued to `W`-valued one-forms, read in the charts of `A` and of `A.ofBaseSet h`, with the
composition with the reading of `Φ` as coefficient. -/
def tangentHomCoeffMap
    (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] G)) ∞
      fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x (Φ x)) :
    A.tangentHom.sectionChartData.CoeffMap (A.ofBaseSet h).tangentHom.sectionChartData where
  toFun θ x := (Φ x).comp (θ x)
  chart i := i
  image_le (i : Fin A.n) := SetLike.coe_subset_coe.1 <|
    ((A.ofBaseSet h).sectionChartData_image_tangentHom i).trans
      ((congrArg SetLike.coe (image_ofBaseSet (A := A) (h := h) i)).trans
        (A.sectionChartData_image_tangentHom i).symm) |>.subset
  isCompact_closure_image i := (A.ofBaseSet h).tangentHom.isCompact_closure_image i
  domain i :=
    ((A.hom (𝕜 := ℝ) h).chart i).target ∩
      ((A.hom (𝕜 := ℝ) h).chart i).symm ⁻¹' ((A.hom (𝕜 := ℝ) h).triv i).baseSet
  isOpen_domain i :=
    ((A.hom (𝕜 := ℝ) h).chart i).isOpen_inter_preimage_symm ((A.hom (𝕜 := ℝ) h).triv i).open_baseSet
  closure_image_subset_domain i := by
    have heq : ((A.ofBaseSet h).tangentHom.sectionChartData.image i : Set E) =
        (A.hom (𝕜 := ℝ) h).image i :=
      congrArg SetLike.coe (((A.ofBaseSet h).image_tangentHom i).trans
        ((image_ofBaseSet (A := A) (h := h) i).trans
          (image_hom (𝕜 := ℝ) (A := A) (h := h) i).symm))
    rw [heq]
    exact (A.hom (𝕜 := ℝ) h).closure_image_subset_target_inter_preimage_baseSet i
  coeff i := ContinuousLinearMap.compL ℝ E F G ∘ (A.hom (𝕜 := ℝ) h).coord i Φ
  contDiffOn_coeff i := by
    have hL : ContDiff ℝ ∞ (ContinuousLinearMap.compL ℝ E F G) :=
      ContinuousLinearMap.contDiff _
    exact hL.comp_contDiffOn (A.contDiffOn_coord_hom h hΦ i)
  coord_toFun (i : Fin A.n) θ y hy := by
    have hy' : y ∈ A.image i := (((A.ofBaseSet h).sectionChartData_image_tangentHom i).trans
      (congrArg SetLike.coe (image_ofBaseSet (A := A) (h := h) i))).subset hy
    have hyA : y ∈ A.tangentHom.image i := (A.sectionChartData_image_tangentHom i).symm.subset hy'
    have hx : (A.chart i).symm y ∈ (trivializationAt F V (A.center i)).baseSet :=
      A.dom_subset_baseSet i (A.symm_mem_dom hy')
    refine ((A.ofBaseSet h).tangentHom.sectionChartData_coord_of_mem _ hy).trans ?_
    refine ((A.ofBaseSet h).coord_tangentHom i _ y).trans ?_
    refine (ContinuousLinearMap.inCoordinates_comp _ _ hx).trans ?_
    rw [A.tangentHom.sectionChartData_coord_of_mem _ hyA, coord_tangentHom, Function.comp_apply,
      coord_hom, ContinuousLinearMap.compL_apply]
    -- `A.ofBaseSet h` has the centres and charts of `A` (`ofBaseSet_center`, `chart_ofBaseSet`).
    rfl

end FiniteBundleAtlas

namespace SobolevSection

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, AddCommGroup (W x)]
  [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)] [∀ x, IsTopologicalAddGroup (W x)]
  [∀ x, ContinuousSMul ℝ (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
  [ContMDiffVectorBundle ∞ G W 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt G W (A.center i)).baseSet)
  {Φ : ∀ x, V x →L[ℝ] W x}
  (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] G)) ∞
    fun x ↦ TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x (Φ x))
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- **Smooth bundle morphisms act on Sobolev sections.** The continuous linear map
`W^{k,p}(V) → W^{k,p}(W)` induced by a smooth bundle morphism `Φ`, sending an element with section
`s` to the element with section `Φ s` (`TauCeti.SobolevSection.chartValueL_bundleMapL_ae_coord`). -/
def bundleMapL : SobolevSection A μ p k →L[ℝ] SobolevSection (A.ofBaseSet h) μ p k :=
  (A.coeffMap h hΦ).mapL μ p k

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- **Smooth bundle morphisms act on Sobolev one-forms.** The continuous linear map from `W^{k,p}`
`V`-valued one-forms to `W^{k,p}` `W`-valued one-forms induced by a smooth bundle morphism `Φ`,
sending an element with one-form `θ` to the element with one-form `Φ ∘ θ`
(`TauCeti.SobolevSection.chartValueL_tangentHomMapL_ae_coord`). -/
def tangentHomMapL [IsManifold 𝓘(ℝ, E) 1 M] :
    SobolevSection A.tangentHom μ p k →L[ℝ] SobolevSection (A.ofBaseSet h).tangentHom μ p k :=
  (A.tangentHomCoeffMap h hΦ).mapL μ p k

variable {A h hΦ μ p k}

/-- The image under `bundleMapL` of an element with section `s` has section `Φ s`. -/
theorem chartValueL_bundleMapL_ae_coord {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (i : Fin A.n) :
    (A.ofBaseSet h).sectionChartData.chartValueL μ p k i (bundleMapL A h hΦ μ p k w)
      =ᵐ[μ.restrict ((A.ofBaseSet h).image i)] (A.ofBaseSet h).coord i fun x ↦ Φ x (s x) :=
  ((A.ofBaseSet h).ae_eq_sectionChartData_coord_iff μ).1 <|
    SectionChartData.CoeffMap.chartValueL_mapL_ae_coord (Ψ := A.coeffMap h hΦ)
      (fun i ↦ (A.ae_eq_sectionChartData_coord_iff μ).2 (hs i)) i

variable [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)] in
/-- The image under `tangentHomMapL` of an element with one-form `θ` has one-form `Φ ∘ θ`. -/
theorem chartValueL_tangentHomMapL_ae_coord [IsManifold 𝓘(ℝ, E) 1 M]
    {w : SobolevSection A.tangentHom μ p k} {θ : ∀ x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x}
    (hθ : ∀ i, A.tangentHom.sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict (A.tangentHom.image i)] A.tangentHom.coord i θ) (i : Fin A.n) :
    (A.ofBaseSet h).tangentHom.sectionChartData.chartValueL μ p k i (tangentHomMapL A h hΦ μ p k w)
      =ᵐ[μ.restrict ((A.ofBaseSet h).tangentHom.image i)]
        (A.ofBaseSet h).tangentHom.coord i fun x ↦ (Φ x).comp (θ x) :=
  ((A.ofBaseSet h).tangentHom.ae_eq_sectionChartData_coord_iff μ).1 <|
    SectionChartData.CoeffMap.chartValueL_mapL_ae_coord (Ψ := A.tangentHomCoeffMap h hΦ)
      (fun i ↦ (A.tangentHom.ae_eq_sectionChartData_coord_iff μ).2 (hθ i)) i

/-- On a smooth section `s`, the map induced by `Φ` is the Sobolev section of the smooth section
`Φ s`. -/
theorem bundleMapL_ofContMDiffSection (s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯) :
    bundleMapL A h hΦ μ p k (ofContMDiffSection A μ p k s) =
      ofContMDiffSection (A.ofBaseSet h) μ p k
        ⟨fun x ↦ Φ x (s x),
          ContMDiff.clm_bundle_apply (hΦ.of_le (m := k) (by exact_mod_cast le_top)) s.contMDiff⟩ :=
  eq_of_ae_eq_coord (s := fun x ↦ Φ x (s x))
    (fun i ↦ chartValueL_bundleMapL_ae_coord (chartValueL_ofContMDiffSection_ae A μ p k s) i)
    (chartValueL_ofContMDiffSection_ae (A.ofBaseSet h) μ p k _)

/-! ### Smooth bundle isomorphisms -/

section Equiv

variable (A h μ p k) [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  {Φ : ∀ x, V x ≃L[ℝ] W x}

variable (hΦ : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F →L[ℝ] G)) ∞ fun x ↦
  TotalSpace.mk' (F →L[ℝ] G) (E := fun x ↦ V x →L[ℝ] W x) x (Φ x : V x →L[ℝ] W x))

/-- **Smooth bundle isomorphisms act on Sobolev sections.** The isomorphism of Banach spaces
`W^{k,p}(V) ≃ W^{k,p}(W)` induced by a smooth bundle isomorphism `Φ`, sending an element with
section `s` to the element with section `Φ s`. Its inverse is induced by `Φ⁻¹`. -/
def bundleEquivL : SobolevSection A μ p k ≃L[ℝ] SobolevSection (A.ofBaseSet h) μ p k :=
  -- The atlas `(A.ofBaseSet h).ofBaseSet _` of `V` has the fields of `A`, so it is `A`.
  (A.coeffMap h hΦ).mapEquivL μ p k
    ((A.ofBaseSet h).coeffMap A.closure_dom_subset_baseSet (hΦ.clm_bundle_equiv_symm))
    (fun _ ↦ funext fun x ↦ (Φ x).symm_apply_apply _)
    (fun _ ↦ funext fun x ↦ (Φ x).apply_symm_apply _)

@[simp]
theorem coe_bundleEquivL :
    (bundleEquivL A h μ p k hΦ :
      SobolevSection A μ p k →L[ℝ] SobolevSection (A.ofBaseSet h) μ p k) =
      bundleMapL A h hΦ μ p k :=
  (rfl)

variable {A h μ p k hΦ} in
/-- The image under the inverse of `bundleEquivL` of an element with section `t` has section
`Φ⁻¹ t`. -/
theorem chartValueL_bundleEquivL_symm_ae_coord {w : SobolevSection (A.ofBaseSet h) μ p k}
    {t : ∀ x, W x} (ht : ∀ i, (A.ofBaseSet h).sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict ((A.ofBaseSet h).image i)] (A.ofBaseSet h).coord i t) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i ((bundleEquivL A h μ p k hΦ).symm w)
      =ᵐ[μ.restrict (A.image i)] A.coord i fun x ↦ (Φ x).symm (t x) :=
  -- The inverse is `bundleMapL` for `Φ⁻¹` on the atlas `A.ofBaseSet h`, whose own `ofBaseSet` atlas
  -- of `V` has the fields of `A`.
  chartValueL_bundleMapL_ae_coord (A := A.ofBaseSet h) (hΦ := hΦ.clm_bundle_equiv_symm) ht i

/-- **Smooth bundle isomorphisms act on Sobolev one-forms.** The isomorphism of Banach spaces
between `W^{k,p}` `V`-valued and `W`-valued one-forms induced by a smooth bundle isomorphism `Φ`,
sending an element with one-form `θ` to the element with one-form `Φ ∘ θ`. -/
def tangentHomEquivL [IsManifold 𝓘(ℝ, E) 1 M] :
    SobolevSection A.tangentHom μ p k ≃L[ℝ] SobolevSection (A.ofBaseSet h).tangentHom μ p k :=
  -- The atlas `(A.ofBaseSet h).ofBaseSet _` of `V` has the fields of `A`, so it is `A`.
  (A.tangentHomCoeffMap h hΦ).mapEquivL μ p k
    ((A.ofBaseSet h).tangentHomCoeffMap A.closure_dom_subset_baseSet
      (hΦ.clm_bundle_equiv_symm))
    (fun _ ↦ funext fun x ↦ ContinuousLinearMap.ext fun _ ↦ (Φ x).symm_apply_apply _)
    (fun _ ↦ funext fun x ↦ ContinuousLinearMap.ext fun _ ↦ (Φ x).apply_symm_apply _)

@[simp]
theorem coe_tangentHomEquivL [IsManifold 𝓘(ℝ, E) 1 M] :
    (tangentHomEquivL A h μ p k hΦ :
      SobolevSection A.tangentHom μ p k →L[ℝ] SobolevSection (A.ofBaseSet h).tangentHom μ p k) =
      tangentHomMapL A h hΦ μ p k :=
  (rfl)

variable {A h μ p k hΦ} in
/-- The image under the inverse of `tangentHomEquivL` of an element with one-form `θ` has one-form
`Φ⁻¹ ∘ θ`. -/
theorem chartValueL_tangentHomEquivL_symm_ae_coord [IsManifold 𝓘(ℝ, E) 1 M]
    {w : SobolevSection (A.ofBaseSet h).tangentHom μ p k}
    {θ : ∀ x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] W x}
    (hθ : ∀ i, (A.ofBaseSet h).tangentHom.sectionChartData.chartValueL μ p k i w
      =ᵐ[μ.restrict ((A.ofBaseSet h).tangentHom.image i)] (A.ofBaseSet h).tangentHom.coord i θ)
    (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i ((tangentHomEquivL A h μ p k hΦ).symm w)
      =ᵐ[μ.restrict (A.tangentHom.image i)]
        A.tangentHom.coord i fun x ↦ ((Φ x).symm : W x →L[ℝ] V x).comp (θ x) :=
  -- The inverse is `tangentHomMapL` for `Φ⁻¹` on the atlas `A.ofBaseSet h`, whose own `ofBaseSet`
  -- atlas of `V` has the fields of `A`.
  chartValueL_tangentHomMapL_ae_coord (A := A.ofBaseSet h) (hΦ := hΦ.clm_bundle_equiv_symm) hθ i

end Equiv

end SobolevSection

end TauCeti
