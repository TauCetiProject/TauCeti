/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.ContMDiffSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.SMul

/-!
# Sobolev sections of a fibrewise product bundle

Let `A` be a finite bundle atlas of a real vector bundle `V → M` whose chart domains have closures
inside the base sets of the preferred trivializations of a second real vector bundle `V'`, so that
the same charts form an atlas `A.ofBaseSet h` of `V'` and an atlas `A.prod h` of the fibrewise
product `V ×ᵇ V'`. This file shows that the Sobolev space `W^{k,p}(V ×ᵇ V')` of
`TauCeti.SobolevSection` is isomorphic, as a Banach space, to `W^{k,p}(V) × W^{k,p}(V')`
(`TauCeti.SobolevSection.prodEquiv`), for every order `k` and every `1 ≤ p ≤ ∞`.

A section of `V ×ᵇ V'` is read in each chart as the pair of the readings of its components
(`TauCeti.FiniteBundleAtlas.coord_prod`). The components of an element of `W^{k,p}(V ×ᵇ V')` are
taken in the basis `Module.finBasis ℝ (F × F')` of the model fibre, which is unrelated to the bases
`Module.finBasis ℝ F` and `Module.finBasis ℝ F'` of the factors; but the coordinates of the
projections and inclusions of `F × F'` in these bases are constant, so the isomorphism acts on
components by constant linear combinations of scalar Sobolev functions. Its chart data are the
pair of projections of the chart data (`TauCeti.SobolevSection.chartValueL_prodEquiv_fst_ae`,
`TauCeti.SobolevSection.chartValueL_prodEquiv_snd_ae`), so it sends the components of a section `s`
to the components of its two projections. It commutes with the inclusions of order `k + 1` into
order `k`, with multiplication by smooth functions, and with the inclusions of `Cᵏ` sections.

Both this isomorphism and its analogue for one-forms are instances of one construction
(`TauCeti.SobolevSection.prodEquivOfCoord`): for bundles `W`, `W₁`, `W₂` read on the charts of
`A`, an isomorphism `e : G ≃L[ℝ] G₁ × G₂` of model fibres which carries the readings of sections
of `W` to the readings of pairs of sections of `W₁` and `W₂`, and back, induces
`W^{k,p}(W) ≃ W^{k,p}(W₁) × W^{k,p}(W₂)`. For one-forms, a one-form with values in `V ×ᵇ V'` is read
in the charts of `(A.prod h).tangentHom` as the `prod` of the readings of its two components
(`TauCeti.FiniteBundleAtlas.coord_tangentHom_prod`), so `W^{k,p}` of `V ×ᵇ V'`-valued one-forms is
isomorphic to the product of `W^{k,p}` of `V`-valued and of `V'`-valued one-forms
(`TauCeti.SobolevSection.tangentHomProdEquiv`).

## Main definitions

* `TauCeti.SobolevSection.prodEquivOfCoord`: the isomorphism induced by a fibre isomorphism
  `G ≃L[ℝ] G₁ × G₂` compatible with chart readings.
* `TauCeti.SobolevSection.prodEquiv`: the isomorphism
  `W^{k,p}(V ×ᵇ V') ≃L[ℝ] W^{k,p}(V) × W^{k,p}(V')`.
* `TauCeti.SobolevSection.tangentHomProdEquiv`: the same isomorphism for one-forms.

## Main results

* `TauCeti.SobolevSection.chartValueL_prodEquivOfCoord_fst_ae`,
  `TauCeti.SobolevSection.chartValueL_prodEquivOfCoord_snd_ae`,
  `TauCeti.SobolevSection.chartValueL_prodEquivOfCoord_symm_ae`: its chart data.
* `TauCeti.SobolevSection.chartValueL_prodEquiv_fst_ae`,
  `TauCeti.SobolevSection.chartValueL_prodEquiv_snd_ae`,
  `TauCeti.SobolevSection.chartValueL_prodEquiv_symm_ae`: the chart data of the isomorphism and of
  its inverse.
* `TauCeti.SobolevSection.chartValueL_prodEquiv_fst_ae_coord`,
  `TauCeti.SobolevSection.chartValueL_prodEquiv_snd_ae_coord`,
  `TauCeti.SobolevSection.chartValueL_prodEquiv_symm_ae_coord`: the isomorphism and its inverse on
  the components of sections.
* `TauCeti.SobolevSection.prodEquiv_lowerOrderL`, `TauCeti.SobolevSection.prodEquiv_contMDiffSMulL`,
  `TauCeti.SobolevSection.prodEquiv_ofContMDiffSection`: compatibility with the inclusion of order
  `k + 1` into order `k`, with smooth multiplication and with `Cᵏ` sections; the `_symm_` forms
  state the same for the inverse.
* `TauCeti.SobolevSection.chartValueL_tangentHomProdEquiv_fst_ae`,
  `TauCeti.SobolevSection.chartValueL_tangentHomProdEquiv_snd_ae`,
  `TauCeti.SobolevSection.chartValueL_tangentHomProdEquiv_symm_ae`: the chart data of the
  isomorphism of one-forms and of its inverse.
-/

public section

noncomputable section

open Bundle MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

namespace SobolevSection

open FiniteBundleAtlas
open SectionChartData (fiberMapData fiberMapData_apply chartValueL_ae_of_eq_fiberMap)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')] [∀ x, AddCommGroup (V' x)]
  [∀ x, Module ℝ (V' x)] [∀ x, TopologicalSpace (V' x)] [FiberBundle F' V'] [VectorBundle ℝ F' V']
  (A : FiniteBundleAtlas E M F V)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet)
  (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

variable {A h μ p k}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ F'] [μ.IsAddHaarMeasure] in
/-- An almost everywhere statement on the image of a chart of `A.prod h` is one on the image of
the corresponding chart of `A`. -/
private theorem ae_restrict_image_prod_iff {i : Fin A.n} {P : E → Prop} :
    (∀ᵐ y ∂μ.restrict ((A.prod h).sectionChartData.image i), P y) ↔
      ∀ᵐ y ∂μ.restrict (A.image i), P y := by
  rw [(A.prod h).sectionChartData_image i, FiniteBundleAtlas.image_prod]

section ProdOfCoord

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)] [∀ x, AddCommGroup (W x)]
  [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)] [FiberBundle G W] [VectorBundle ℝ G W]
  {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁] [FiniteDimensional ℝ G₁]
  {W₁ : M → Type*} [TopologicalSpace (TotalSpace G₁ W₁)] [∀ x, AddCommGroup (W₁ x)]
  [∀ x, Module ℝ (W₁ x)] [∀ x, TopologicalSpace (W₁ x)] [FiberBundle G₁ W₁]
  [VectorBundle ℝ G₁ W₁]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] [FiniteDimensional ℝ G₂]
  {W₂ : M → Type*} [TopologicalSpace (TotalSpace G₂ W₂)] [∀ x, AddCommGroup (W₂ x)]
  [∀ x, Module ℝ (W₂ x)] [∀ x, TopologicalSpace (W₂ x)] [FiberBundle G₂ W₂]
  [VectorBundle ℝ G₂ W₂]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [FiniteDimensional ℝ G]
  [μ.IsAddHaarMeasure] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] [∀ x, AddCommGroup (V x)] in
/-- An almost everywhere statement on the image of a chart of `A.ofBaseSet hW` is one on the image
of the corresponding chart of `A`. -/
private theorem ae_restrict_image_ofBaseSet_iff
    {hW : ∀ i, closure (A.dom i) ⊆ (trivializationAt G W (A.center i)).baseSet} {i : Fin A.n}
    {P : E → Prop} :
    (∀ᵐ y ∂μ.restrict ((A.ofBaseSet hW).sectionChartData.image i), P y) ↔
      ∀ᵐ y ∂μ.restrict (A.image i), P y := by
  rw [(A.ofBaseSet hW).sectionChartData_image i, image_ofBaseSet]

variable {hW : ∀ i, closure (A.dom i) ⊆ (trivializationAt G W (A.center i)).baseSet}
  {hW₁ : ∀ i, closure (A.dom i) ⊆ (trivializationAt G₁ W₁ (A.center i)).baseSet}
  {hW₂ : ∀ i, closure (A.dom i) ⊆ (trivializationAt G₂ W₂ (A.center i)).baseSet}
  (e : G ≃L[ℝ] G₁ × G₂)

variable (hW hW₁ μ p k) in
/-- The components of the first factor of a tuple of components on the charts of `A.ofBaseSet hW`.
-/
private def ofCoordFstData :
    (A.ofBaseSet hW).sectionChartData.SobolevData μ p k →L[ℝ]
      (A.ofBaseSet hW₁).sectionChartData.SobolevData μ p k :=
  fiberMapData μ p k ((ContinuousLinearMap.fst ℝ G₁ G₂).comp (e : G →L[ℝ] G₁ × G₂))
    fun i ↦ ((image_ofBaseSet (h := hW₁) i).trans (image_ofBaseSet (h := hW) i).symm).le

variable (hW hW₂ μ p k) in
/-- The components of the second factor of a tuple of components on the charts of
`A.ofBaseSet hW`. -/
private def ofCoordSndData :
    (A.ofBaseSet hW).sectionChartData.SobolevData μ p k →L[ℝ]
      (A.ofBaseSet hW₂).sectionChartData.SobolevData μ p k :=
  fiberMapData μ p k ((ContinuousLinearMap.snd ℝ G₁ G₂).comp (e : G →L[ℝ] G₁ × G₂))
    fun i ↦ ((image_ofBaseSet (h := hW₂) i).trans (image_ofBaseSet (h := hW) i).symm).le

variable (hW hW₁ μ p k) in
/-- The components on the charts of `A.ofBaseSet hW` of a tuple of components on the charts of
`A.ofBaseSet hW₁`, placed in the first factor. -/
private def ofCoordInlData :
    (A.ofBaseSet hW₁).sectionChartData.SobolevData μ p k →L[ℝ]
      (A.ofBaseSet hW).sectionChartData.SobolevData μ p k :=
  fiberMapData μ p k ((e.symm : G₁ × G₂ →L[ℝ] G).comp (ContinuousLinearMap.inl ℝ G₁ G₂))
    fun i ↦ ((image_ofBaseSet (h := hW) i).trans (image_ofBaseSet (h := hW₁) i).symm).le

variable (hW hW₂ μ p k) in
/-- The components on the charts of `A.ofBaseSet hW` of a tuple of components on the charts of
`A.ofBaseSet hW₂`, placed in the second factor. -/
private def ofCoordInrData :
    (A.ofBaseSet hW₂).sectionChartData.SobolevData μ p k →L[ℝ]
      (A.ofBaseSet hW).sectionChartData.SobolevData μ p k :=
  fiberMapData μ p k ((e.symm : G₁ × G₂ →L[ℝ] G).comp (ContinuousLinearMap.inr ℝ G₁ G₂))
    fun i ↦ ((image_ofBaseSet (h := hW) i).trans (image_ofBaseSet (h := hW₂) i).symm).le

omit [FiniteDimensional ℝ G₂] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] [∀ x, AddCommGroup (V x)] in
private theorem chartValueL_ofCoordFstData_ae
    (w : (A.ofBaseSet hW).sectionChartData.SobolevData μ p k)
    (i : Fin A.n) :
    (A.ofBaseSet hW₁).sectionChartData.chartValueL μ p k i (ofCoordFstData μ p k hW hW₁ e w)
      =ᵐ[μ.restrict (A.image i)]
        fun y ↦ (e ((A.ofBaseSet hW).sectionChartData.chartValueL μ p k i w y)).1 := by
  refine (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW₁)).1 ?_
  filter_upwards [chartValueL_ae_of_eq_fiberMap μ p k (C₁ := (A.ofBaseSet hW).sectionChartData)
    (C₂ := (A.ofBaseSet hW₁).sectionChartData)
    ((ContinuousLinearMap.fst ℝ G₁ G₂).comp (e : G →L[ℝ] G₁ × G₂)) (i₁ := i) (i₂ := i)
    ((image_ofBaseSet (h := hW₁) i).trans (image_ofBaseSet (h := hW) i).symm).le (w₁ := w)
    (w₂ := ofCoordFstData μ p k hW hW₁ e w) (fiberMapData_apply μ p k _ _ w i)] with y hy
  rw [hy]
  simp

omit [FiniteDimensional ℝ G₁] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] [∀ x, AddCommGroup (V x)] in
private theorem chartValueL_ofCoordSndData_ae
    (w : (A.ofBaseSet hW).sectionChartData.SobolevData μ p k)
    (i : Fin A.n) :
    (A.ofBaseSet hW₂).sectionChartData.chartValueL μ p k i (ofCoordSndData μ p k hW hW₂ e w)
      =ᵐ[μ.restrict (A.image i)]
        fun y ↦ (e ((A.ofBaseSet hW).sectionChartData.chartValueL μ p k i w y)).2 := by
  refine (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW₂)).1 ?_
  filter_upwards [chartValueL_ae_of_eq_fiberMap μ p k (C₁ := (A.ofBaseSet hW).sectionChartData)
    (C₂ := (A.ofBaseSet hW₂).sectionChartData)
    ((ContinuousLinearMap.snd ℝ G₁ G₂).comp (e : G →L[ℝ] G₁ × G₂)) (i₁ := i) (i₂ := i)
    ((image_ofBaseSet (h := hW₂) i).trans (image_ofBaseSet (h := hW) i).symm).le (w₁ := w)
    (w₂ := ofCoordSndData μ p k hW hW₂ e w) (fiberMapData_apply μ p k _ _ w i)] with y hy
  rw [hy]
  simp

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (V x)] in
private theorem chartValueL_ofCoordPairData_ae
    (u : (A.ofBaseSet hW₁).sectionChartData.SobolevData μ p k)
    (v : (A.ofBaseSet hW₂).sectionChartData.SobolevData μ p k) (i : Fin A.n) :
    (A.ofBaseSet hW).sectionChartData.chartValueL μ p k i
        (ofCoordInlData μ p k hW hW₁ e u + ofCoordInrData μ p k hW hW₂ e v)
      =ᵐ[μ.restrict (A.image i)] fun y ↦
        e.symm ((A.ofBaseSet hW₁).sectionChartData.chartValueL μ p k i u y,
          (A.ofBaseSet hW₂).sectionChartData.chartValueL μ p k i v y) := by
  have hu := chartValueL_ae_of_eq_fiberMap μ p k (C₁ := (A.ofBaseSet hW₁).sectionChartData)
    (C₂ := (A.ofBaseSet hW).sectionChartData)
    ((e.symm : G₁ × G₂ →L[ℝ] G).comp (ContinuousLinearMap.inl ℝ G₁ G₂)) (i₁ := i) (i₂ := i)
    ((image_ofBaseSet (h := hW) i).trans (image_ofBaseSet (h := hW₁) i).symm).le (w₁ := u)
    (w₂ := ofCoordInlData μ p k hW hW₁ e u) (fiberMapData_apply μ p k _ _ u i)
  have hv := chartValueL_ae_of_eq_fiberMap μ p k (C₁ := (A.ofBaseSet hW₂).sectionChartData)
    (C₂ := (A.ofBaseSet hW).sectionChartData)
    ((e.symm : G₁ × G₂ →L[ℝ] G).comp (ContinuousLinearMap.inr ℝ G₁ G₂)) (i₁ := i) (i₂ := i)
    ((image_ofBaseSet (h := hW) i).trans (image_ofBaseSet (h := hW₂) i).symm).le (w₁ := v)
    (w₂ := ofCoordInrData μ p k hW hW₂ e v) (fiberMapData_apply μ p k _ _ v i)
  refine (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW)).1 ?_
  filter_upwards [hu, hv, Lp.coeFn_add
    ((A.ofBaseSet hW).sectionChartData.chartValueL μ p k i (ofCoordInlData μ p k hW hW₁ e u))
    ((A.ofBaseSet hW).sectionChartData.chartValueL μ p k i (ofCoordInrData μ p k hW hW₂ e v))]
    with y hu hv hadd
  rw [map_add, hadd, Pi.add_apply, hu, hv]
  simp [← map_add]

variable {f₁ : (∀ x, W x) → ∀ x, W₁ x} {f₂ : (∀ x, W x) → ∀ x, W₂ x}
  {g : (∀ x, W₁ x) → (∀ x, W₂ x) → ∀ x, W x}

include e in
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] [μ.IsAddHaarMeasure] [FiniteDimensional ℝ G]
  [FiniteDimensional ℝ G₁] [FiniteDimensional ℝ G₂] [∀ x, AddCommGroup (V x)] in
/-- Coordinates of a section of `W` on the image of chart `i` read through the section chart
data. -/
private theorem e_sectionChartData_coord_ae
    (hf : ∀ i s, ∀ y ∈ A.image i, e ((A.ofBaseSet hW).coord i s y) =
      ((A.ofBaseSet hW₁).coord i (f₁ s) y, (A.ofBaseSet hW₂).coord i (f₂ s) y))
    (i : Fin A.n) (s : ∀ x, W x) :
    ∀ᵐ y ∂μ.restrict (A.image i), e ((A.ofBaseSet hW).sectionChartData.coord i s y) =
      ((A.ofBaseSet hW₁).sectionChartData.coord i (f₁ s) y,
        (A.ofBaseSet hW₂).sectionChartData.coord i (f₂ s) y) := by
  filter_upwards [ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy
  rw [(A.ofBaseSet hW).sectionChartData_coord_of_mem s ((image_ofBaseSet i).ge hy),
    (A.ofBaseSet hW₁).sectionChartData_coord_of_mem _ ((image_ofBaseSet i).ge hy),
    (A.ofBaseSet hW₂).sectionChartData_coord_of_mem _ ((image_ofBaseSet i).ge hy), hf i s y hy]

variable (hW hW₁ hW₂ μ p k f₁ f₂ g)

/-- The first component of `TauCeti.SobolevSection.prodEquivOfCoord`. -/
private def ofCoordFstL
    (hf : ∀ i s, ∀ y ∈ A.image i, e ((A.ofBaseSet hW).coord i s y) =
      ((A.ofBaseSet hW₁).coord i (f₁ s) y, (A.ofBaseSet hW₂).coord i (f₂ s) y)) :
    SobolevSection (A.ofBaseSet hW) μ p k →L[ℝ] SobolevSection (A.ofBaseSet hW₁) μ p k :=
  ((ofCoordFstData μ p k hW hW₁ e).comp
      ((A.ofBaseSet hW).sectionChartData.sobolevSections μ p k).subtypeL).codRestrict
    ((A.ofBaseSet hW₁).sectionChartData.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := (A.ofBaseSet hW).sectionChartData.exists_section μ p k w
      refine (SectionChartData.mem_sobolevSections_iff _ μ p k).2
        ⟨f₁ s, fun i ↦ (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW₁)).2 ?_⟩
      filter_upwards [chartValueL_ofCoordFstData_ae (hW₁ := hW₁) e
          (w : (A.ofBaseSet hW).sectionChartData.SobolevData μ p k) i,
        (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW)).1 (hs i),
        e_sectionChartData_coord_ae e hf i s] with y h₁ h₂ h₃
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, h₁, h₂, h₃]

/-- The second component of `TauCeti.SobolevSection.prodEquivOfCoord`. -/
private def ofCoordSndL
    (hf : ∀ i s, ∀ y ∈ A.image i, e ((A.ofBaseSet hW).coord i s y) =
      ((A.ofBaseSet hW₁).coord i (f₁ s) y, (A.ofBaseSet hW₂).coord i (f₂ s) y)) :
    SobolevSection (A.ofBaseSet hW) μ p k →L[ℝ] SobolevSection (A.ofBaseSet hW₂) μ p k :=
  ((ofCoordSndData μ p k hW hW₂ e).comp
      ((A.ofBaseSet hW).sectionChartData.sobolevSections μ p k).subtypeL).codRestrict
    ((A.ofBaseSet hW₂).sectionChartData.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := (A.ofBaseSet hW).sectionChartData.exists_section μ p k w
      refine (SectionChartData.mem_sobolevSections_iff _ μ p k).2
        ⟨f₂ s, fun i ↦ (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW₂)).2 ?_⟩
      filter_upwards [chartValueL_ofCoordSndData_ae (hW₂ := hW₂) e
          (w : (A.ofBaseSet hW).sectionChartData.SobolevData μ p k) i,
        (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW)).1 (hs i),
        e_sectionChartData_coord_ae e hf i s] with y h₁ h₂ h₃
      rw [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, h₁, h₂, h₃]

/-- The inverse of `TauCeti.SobolevSection.prodEquivOfCoord`. -/
private def ofCoordPairL
    (hg : ∀ i s₁ s₂, ∀ y ∈ A.image i, e ((A.ofBaseSet hW).coord i (g s₁ s₂) y) =
      ((A.ofBaseSet hW₁).coord i s₁ y, (A.ofBaseSet hW₂).coord i s₂ y)) :
    SobolevSection (A.ofBaseSet hW₁) μ p k × SobolevSection (A.ofBaseSet hW₂) μ p k →L[ℝ]
      SobolevSection (A.ofBaseSet hW) μ p k :=
  ((ofCoordInlData μ p k hW hW₁ e).comp
      (((A.ofBaseSet hW₁).sectionChartData.sobolevSections μ p k).subtypeL.comp
        (ContinuousLinearMap.fst ℝ _ _)) +
    (ofCoordInrData μ p k hW hW₂ e).comp
      (((A.ofBaseSet hW₂).sectionChartData.sobolevSections μ p k).subtypeL.comp
        (ContinuousLinearMap.snd ℝ _ _))).codRestrict
    ((A.ofBaseSet hW).sectionChartData.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s₁, hs₁⟩ := (A.ofBaseSet hW₁).sectionChartData.exists_section μ p k w.1
      obtain ⟨s₂, hs₂⟩ := (A.ofBaseSet hW₂).sectionChartData.exists_section μ p k w.2
      refine (SectionChartData.mem_sobolevSections_iff _ μ p k).2
        ⟨g s₁ s₂, fun i ↦ (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW)).2 ?_⟩
      filter_upwards [chartValueL_ofCoordPairData_ae (hW := hW) e
          (w.1 : (A.ofBaseSet hW₁).sectionChartData.SobolevData μ p k)
          (w.2 : (A.ofBaseSet hW₂).sectionChartData.SobolevData μ p k) i,
        (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW₁)).1 (hs₁ i),
        (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW₂)).1 (hs₂ i),
        ae_restrict_mem (A.image i).isOpen.measurableSet] with y h₁ h₂ h₃ hy
      have hg' := hg i s₁ s₂ y hy
      rw [← (A.ofBaseSet hW).sectionChartData_coord_of_mem _ ((image_ofBaseSet (h := hW) i).ge hy),
        ← (A.ofBaseSet hW₁).sectionChartData_coord_of_mem _
          ((image_ofBaseSet (h := hW₁) i).ge hy),
        ← (A.ofBaseSet hW₂).sectionChartData_coord_of_mem _
          ((image_ofBaseSet (h := hW₂) i).ge hy), ← h₂, ← h₃, ← e.eq_symm_apply] at hg'
      simpa using h₁.trans hg'.symm

variable {hf : ∀ i s, ∀ y ∈ A.image i, e ((A.ofBaseSet hW).coord i s y) =
      ((A.ofBaseSet hW₁).coord i (f₁ s) y, (A.ofBaseSet hW₂).coord i (f₂ s) y)}
  {hg : ∀ i s₁ s₂, ∀ y ∈ A.image i, e ((A.ofBaseSet hW).coord i (g s₁ s₂) y) =
      ((A.ofBaseSet hW₁).coord i s₁ y, (A.ofBaseSet hW₂).coord i s₂ y)}

omit [FiniteDimensional ℝ G₂] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] [∀ x, AddCommGroup (V x)] in
private theorem coe_ofCoordFstL (w : SobolevSection (A.ofBaseSet hW) μ p k) :
    (ofCoordFstL μ p k hW hW₁ hW₂ e f₁ f₂ hf w :
        (A.ofBaseSet hW₁).sectionChartData.SobolevData μ p k) =
      ofCoordFstData μ p k hW hW₁ e w := by
  simp [ofCoordFstL]

omit [FiniteDimensional ℝ G₁] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] [∀ x, AddCommGroup (V x)] in
private theorem coe_ofCoordSndL (w : SobolevSection (A.ofBaseSet hW) μ p k) :
    (ofCoordSndL μ p k hW hW₁ hW₂ e f₁ f₂ hf w :
        (A.ofBaseSet hW₂).sectionChartData.SobolevData μ p k) =
      ofCoordSndData μ p k hW hW₂ e w := by
  simp [ofCoordSndL]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (V x)] in
private theorem coe_ofCoordPairL (u : SobolevSection (A.ofBaseSet hW₁) μ p k)
    (v : SobolevSection (A.ofBaseSet hW₂) μ p k) :
    (ofCoordPairL μ p k hW hW₁ hW₂ e g hg (u, v) :
        (A.ofBaseSet hW).sectionChartData.SobolevData μ p k) =
      ofCoordInlData μ p k hW hW₁ e u + ofCoordInrData μ p k hW hW₂ e v := by
  simp [ofCoordPairL]

variable (A) in
/-- **Sobolev sections on the same charts split along a fibre isomorphism.** Let `W`, `W₁`, `W₂`
be vector bundles read on the charts of `A`, and `e : G ≃L[ℝ] G₁ × G₂` an isomorphism of their
model fibres which, on the chart images, carries the readings of a section `s` of `W` to the
readings of two sections `f₁ s` of `W₁` and `f₂ s` of `W₂`, and the readings of a section
`g s₁ s₂` of `W` to those of `s₁` and `s₂`. Then `W^{k,p}(W) ≃ W^{k,p}(W₁) × W^{k,p}(W₂)`, acting on
the chart data by `e` (`TauCeti.SobolevSection.chartValueL_prodEquivOfCoord_fst_ae`,
`TauCeti.SobolevSection.chartValueL_prodEquivOfCoord_snd_ae`,
`TauCeti.SobolevSection.chartValueL_prodEquivOfCoord_symm_ae`). -/
def prodEquivOfCoord
    (hf : ∀ i s, ∀ y ∈ A.image i, e ((A.ofBaseSet hW).coord i s y) =
      ((A.ofBaseSet hW₁).coord i (f₁ s) y, (A.ofBaseSet hW₂).coord i (f₂ s) y))
    (hg : ∀ i s₁ s₂, ∀ y ∈ A.image i, e ((A.ofBaseSet hW).coord i (g s₁ s₂) y) =
      ((A.ofBaseSet hW₁).coord i s₁ y, (A.ofBaseSet hW₂).coord i s₂ y)) :
    SobolevSection (A.ofBaseSet hW) μ p k ≃L[ℝ]
      SobolevSection (A.ofBaseSet hW₁) μ p k × SobolevSection (A.ofBaseSet hW₂) μ p k :=
  ContinuousLinearEquiv.ofContinuousLinearMap
    ((ofCoordFstL μ p k hW hW₁ hW₂ e f₁ f₂ hf).prod (ofCoordSndL μ p k hW hW₁ hW₂ e f₁ f₂ hf))
    (ofCoordPairL μ p k hW hW₁ hW₂ e g hg)
    (h₂ := ContinuousLinearMap.ext fun w ↦ SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
      (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW)).2 <| by
      filter_upwards [chartValueL_ofCoordPairData_ae (hW := hW) e (ofCoordFstData μ p k hW hW₁ e w)
          (ofCoordSndData μ p k hW hW₂ e w) i,
        chartValueL_ofCoordFstData_ae (hW₁ := hW₁) e
          (w : (A.ofBaseSet hW).sectionChartData.SobolevData μ p k) i,
        chartValueL_ofCoordSndData_ae (hW₂ := hW₂) e
          (w : (A.ofBaseSet hW).sectionChartData.SobolevData μ p k) i]
        with y h₁ h₂ h₃
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, coe_ofCoordPairL,
        coe_ofCoordFstL, coe_ofCoordSndL, ContinuousLinearMap.id_apply, h₁, h₂, h₃, Prod.mk.eta,
        ContinuousLinearEquiv.symm_apply_apply])
    (h₁ := ContinuousLinearMap.ext fun w ↦ by
      obtain ⟨u, v⟩ := w
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.id_apply]
      refine Prod.ext (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
          (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW₁)).2 ?_)
        (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
          (ae_restrict_image_ofBaseSet_iff (A := A) (hW := hW₂)).2 ?_)
      · filter_upwards [chartValueL_ofCoordFstData_ae (hW₁ := hW₁) e
            (ofCoordPairL μ p k hW hW₁ hW₂ e g hg (u, v) :
            (A.ofBaseSet hW).sectionChartData.SobolevData μ p k) i,
          chartValueL_ofCoordPairData_ae (hW := hW) e
            (u : (A.ofBaseSet hW₁).sectionChartData.SobolevData μ p k)
            (v : (A.ofBaseSet hW₂).sectionChartData.SobolevData μ p k) i] with y h₁ h₂
        rw [coe_ofCoordFstL, h₁, coe_ofCoordPairL, h₂, ContinuousLinearEquiv.apply_symm_apply]
      · filter_upwards [chartValueL_ofCoordSndData_ae (hW₂ := hW₂) e
            (ofCoordPairL μ p k hW hW₁ hW₂ e g hg (u, v) :
            (A.ofBaseSet hW).sectionChartData.SobolevData μ p k) i,
          chartValueL_ofCoordPairData_ae (hW := hW) e
            (u : (A.ofBaseSet hW₁).sectionChartData.SobolevData μ p k)
            (v : (A.ofBaseSet hW₂).sectionChartData.SobolevData μ p k) i] with y h₁ h₂
        rw [coe_ofCoordSndL, h₁, coe_ofCoordPairL, h₂, ContinuousLinearEquiv.apply_symm_apply])

variable {hW hW₁ hW₂ μ p k f₁ f₂ g}

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (V x)] in
/-- The chart data of the first component of `prodEquivOfCoord` are the first components of `e`
applied to the chart data. -/
theorem chartValueL_prodEquivOfCoord_fst_ae (w : SobolevSection (A.ofBaseSet hW) μ p k)
    (i : Fin A.n) :
    (A.ofBaseSet hW₁).sectionChartData.chartValueL μ p k i
        (prodEquivOfCoord A μ p k hW hW₁ hW₂ e f₁ f₂ g hf hg w).1
      =ᵐ[μ.restrict (A.image i)]
        fun y ↦ (e ((A.ofBaseSet hW).sectionChartData.chartValueL μ p k i w y)).1 := by
  rw [prodEquivOfCoord, ContinuousLinearEquiv.coe_ofContinuousLinearMap,
    ContinuousLinearMap.prod_apply, coe_ofCoordFstL]
  exact chartValueL_ofCoordFstData_ae (hW₁ := hW₁) e
    (w : (A.ofBaseSet hW).sectionChartData.SobolevData μ p k) i

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (V x)] in
/-- The chart data of the second component of `prodEquivOfCoord` are the second components of `e`
applied to the chart data. -/
theorem chartValueL_prodEquivOfCoord_snd_ae (w : SobolevSection (A.ofBaseSet hW) μ p k)
    (i : Fin A.n) :
    (A.ofBaseSet hW₂).sectionChartData.chartValueL μ p k i
        (prodEquivOfCoord A μ p k hW hW₁ hW₂ e f₁ f₂ g hf hg w).2
      =ᵐ[μ.restrict (A.image i)]
        fun y ↦ (e ((A.ofBaseSet hW).sectionChartData.chartValueL μ p k i w y)).2 := by
  rw [prodEquivOfCoord, ContinuousLinearEquiv.coe_ofContinuousLinearMap,
    ContinuousLinearMap.prod_apply, coe_ofCoordSndL]
  exact chartValueL_ofCoordSndData_ae (hW₂ := hW₂) e
    (w : (A.ofBaseSet hW).sectionChartData.SobolevData μ p k) i

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (V x)] in
/-- The chart data of the inverse of `prodEquivOfCoord` are `e.symm` applied to the pairs of the
chart data. -/
theorem chartValueL_prodEquivOfCoord_symm_ae (u : SobolevSection (A.ofBaseSet hW₁) μ p k)
    (v : SobolevSection (A.ofBaseSet hW₂) μ p k) (i : Fin A.n) :
    (A.ofBaseSet hW).sectionChartData.chartValueL μ p k i
        ((prodEquivOfCoord A μ p k hW hW₁ hW₂ e f₁ f₂ g hf hg).symm (u, v))
      =ᵐ[μ.restrict (A.image i)] fun y ↦
        e.symm ((A.ofBaseSet hW₁).sectionChartData.chartValueL μ p k i u y,
          (A.ofBaseSet hW₂).sectionChartData.chartValueL μ p k i v y) := by
  rw [prodEquivOfCoord, ContinuousLinearEquiv.symm_ofContinuousLinearMap,
    ContinuousLinearEquiv.coe_ofContinuousLinearMap, coe_ofCoordPairL]
  exact chartValueL_ofCoordPairData_ae (hW := hW) e
    (u : (A.ofBaseSet hW₁).sectionChartData.SobolevData μ p k)
    (v : (A.ofBaseSet hW₂).sectionChartData.SobolevData μ p k) i

end ProdOfCoord

/-! ### Sections of a product bundle -/

variable (A h μ p k) in
/-- **Sobolev sections of a product bundle.** The Sobolev space `W^{k,p}(V ×ᵇ V')` on the charts
of `A.prod h` is isomorphic to the product of the Sobolev spaces `W^{k,p}(V)` on the charts of `A`
and `W^{k,p}(V')` on the charts of `A.ofBaseSet h`. Its chart data are the pair of projections of
the chart data (`TauCeti.SobolevSection.chartValueL_prodEquiv_fst_ae`,
`TauCeti.SobolevSection.chartValueL_prodEquiv_snd_ae`). -/
def prodEquiv :
    SobolevSection (A.prod h) μ p k ≃L[ℝ]
      SobolevSection A μ p k × SobolevSection (A.ofBaseSet h) μ p k :=
  prodEquivOfCoord A μ p k (fun i ↦ subset_inter (A.closure_dom_subset_baseSet i) (h i))
    A.closure_dom_subset_baseSet h (.refl ℝ (F × F'))
    (fun s x ↦ (s x).1) (fun s x ↦ (s x).2) (fun s t x ↦ ((s x, t x) : (V ×ᵇ V') x))
    (fun i s y _ ↦ coord_prod A h i s y) (fun i _ _ y _ ↦ coord_prod A h i _ y)

/-- The chart data of the first component of `prodEquiv A h μ p k w` are the first projections of
the chart data of `w`. -/
theorem chartValueL_prodEquiv_fst_ae (w : SobolevSection (A.prod h) μ p k) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i (prodEquiv A h μ p k w).1 =ᵐ[μ.restrict (A.image i)]
      fun y ↦ ((A.prod h).sectionChartData.chartValueL μ p k i w y).1 :=
  chartValueL_prodEquivOfCoord_fst_ae (.refl ℝ (F × F')) w i

/-- The chart data of the second component of `prodEquiv A h μ p k w` are the second projections
of the chart data of `w`. -/
theorem chartValueL_prodEquiv_snd_ae (w : SobolevSection (A.prod h) μ p k) (i : Fin A.n) :
    (A.ofBaseSet h).sectionChartData.chartValueL μ p k i (prodEquiv A h μ p k w).2
      =ᵐ[μ.restrict (A.image i)]
      fun y ↦ ((A.prod h).sectionChartData.chartValueL μ p k i w y).2 :=
  chartValueL_prodEquivOfCoord_snd_ae (.refl ℝ (F × F')) w i

/-- The chart data of `(prodEquiv A h μ p k).symm (u, v)` are the pairs of the chart data of `u`
and of `v`. -/
theorem chartValueL_prodEquiv_symm_ae (u : SobolevSection A μ p k)
    (v : SobolevSection (A.ofBaseSet h) μ p k) (i : Fin A.n) :
    (A.prod h).sectionChartData.chartValueL μ p k i ((prodEquiv A h μ p k).symm (u, v))
      =ᵐ[μ.restrict (A.image i)] fun y ↦ (A.sectionChartData.chartValueL μ p k i u y,
        (A.ofBaseSet h).sectionChartData.chartValueL μ p k i v y) :=
  chartValueL_prodEquivOfCoord_symm_ae (.refl ℝ (F × F')) u v i

/-- **Components of sections.** If the chart data of `w` are the readings of a section `s` of
`V ×ᵇ V'`, then the chart data of the first component of `prodEquiv A h μ p k w` are the readings
of the first projection of `s`. -/
theorem chartValueL_prodEquiv_fst_ae_coord {w : SobolevSection (A.prod h) μ p k}
    {s : ∀ x, (V ×ᵇ V') x} {i : Fin A.n}
    (hs : (A.prod h).sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)]
      (A.prod h).coord i s) :
    A.sectionChartData.chartValueL μ p k i (prodEquiv A h μ p k w).1 =ᵐ[μ.restrict (A.image i)]
      A.coord i fun x ↦ (s x).1 := by
  filter_upwards [chartValueL_prodEquiv_fst_ae w i, hs] with y h₁ h₂
  exact h₁.trans (congrArg Prod.fst (h₂.trans (coord_prod A h i s y)))

/-- **Components of sections.** If the chart data of `w` are the readings of a section `s` of
`V ×ᵇ V'`, then the chart data of the second component of `prodEquiv A h μ p k w` are the readings
of the second projection of `s`. -/
theorem chartValueL_prodEquiv_snd_ae_coord {w : SobolevSection (A.prod h) μ p k}
    {s : ∀ x, (V ×ᵇ V') x} {i : Fin A.n}
    (hs : (A.prod h).sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)]
      (A.prod h).coord i s) :
    (A.ofBaseSet h).sectionChartData.chartValueL μ p k i (prodEquiv A h μ p k w).2
      =ᵐ[μ.restrict (A.image i)] (A.ofBaseSet h).coord i fun x ↦ (s x).2 := by
  filter_upwards [chartValueL_prodEquiv_snd_ae w i, hs] with y h₁ h₂
  exact h₁.trans (congrArg Prod.snd (h₂.trans (coord_prod A h i s y)))

/-- **Components of sections.** If the chart data of `u` and `v` are the readings of sections `s`
of `V` and `t` of `V'`, then the chart data of `(prodEquiv A h μ p k).symm (u, v)` are the
readings of the section `x ↦ (s x, t x)` of `V ×ᵇ V'`. -/
theorem chartValueL_prodEquiv_symm_ae_coord {u : SobolevSection A μ p k}
    {v : SobolevSection (A.ofBaseSet h) μ p k} {s : ∀ x, V x} {t : ∀ x, V' x} {i : Fin A.n}
    (hs : A.sectionChartData.chartValueL μ p k i u =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (ht : (A.ofBaseSet h).sectionChartData.chartValueL μ p k i v =ᵐ[μ.restrict (A.image i)]
      (A.ofBaseSet h).coord i t) :
    (A.prod h).sectionChartData.chartValueL μ p k i ((prodEquiv A h μ p k).symm (u, v))
      =ᵐ[μ.restrict (A.image i)] (A.prod h).coord i fun x ↦ ((s x, t x) : (V ×ᵇ V') x) := by
  filter_upwards [chartValueL_prodEquiv_symm_ae u v i, hs, ht] with y h₁ h₂ h₃
  exact h₁.trans ((Prod.ext h₂ h₃).trans (coord_prod A h i _ y).symm)

/-- `TauCeti.SobolevSection.prodEquiv` commutes with the inclusions of order `k + 1` into order
`k`. -/
theorem prodEquiv_lowerOrderL (w : SobolevSection (A.prod h) μ p (k + 1)) :
    prodEquiv A h μ p k ((A.prod h).sectionChartData.lowerOrderL μ p k w) =
      (A.sectionChartData.lowerOrderL μ p k (prodEquiv A h μ p (k + 1) w).1,
        (A.ofBaseSet h).sectionChartData.lowerOrderL μ p k (prodEquiv A h μ p (k + 1) w).2) := by
  refine Prod.ext (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦ ?_)
    (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
      (ae_restrict_image_ofBaseSet_iff (A := A) (hW := h)).2 ?_)
  · filter_upwards [chartValueL_prodEquiv_fst_ae ((A.prod h).sectionChartData.lowerOrderL μ p k w)
      i, chartValueL_prodEquiv_fst_ae w i] with y h₁ h₂
    rw [h₁, (A.prod h).sectionChartData.chartValueL_coe_lowerOrderL μ p k w i,
      A.sectionChartData.chartValueL_coe_lowerOrderL μ p k (prodEquiv A h μ p (k + 1) w).1 i, h₂]
  · filter_upwards [chartValueL_prodEquiv_snd_ae ((A.prod h).sectionChartData.lowerOrderL μ p k w)
      i, chartValueL_prodEquiv_snd_ae w i] with y h₁ h₂
    rw [h₁, (A.prod h).sectionChartData.chartValueL_coe_lowerOrderL μ p k w i,
      (A.ofBaseSet h).sectionChartData.chartValueL_coe_lowerOrderL μ p k
        (prodEquiv A h μ p (k + 1) w).2 i, h₂]

/-- The inverse of `TauCeti.SobolevSection.prodEquiv` commutes with the inclusions of order `k + 1`
into order `k`. -/
theorem prodEquiv_symm_lowerOrderL (u : SobolevSection A μ p (k + 1))
    (v : SobolevSection (A.ofBaseSet h) μ p (k + 1)) :
    (prodEquiv A h μ p k).symm (A.sectionChartData.lowerOrderL μ p k u,
        (A.ofBaseSet h).sectionChartData.lowerOrderL μ p k v) =
      (A.prod h).sectionChartData.lowerOrderL μ p k ((prodEquiv A h μ p (k + 1)).symm (u, v)) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, prodEquiv_lowerOrderL,
    ContinuousLinearEquiv.apply_symm_apply]

/-- `TauCeti.SobolevSection.prodEquiv` commutes with multiplication by a smooth function. -/
theorem prodEquiv_contMDiffSMulL [IsManifold 𝓘(ℝ, E) ∞ M] {φ : M → ℝ}
    (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (w : SobolevSection (A.prod h) μ p k) :
    prodEquiv A h μ p k (contMDiffSMulL (A.prod h) μ p k hφ w) =
      (contMDiffSMulL A μ p k hφ (prodEquiv A h μ p k w).1,
        contMDiffSMulL (A.ofBaseSet h) μ p k hφ (prodEquiv A h μ p k w).2) := by
  have hw (i : Fin A.n) := (ae_restrict_image_prod_iff (A := A) (h := h) (i := i)).1
    (chartValueL_contMDiffSMulL_ae hφ w i)
  refine Prod.ext (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦ ?_)
    (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
      (ae_restrict_image_ofBaseSet_iff (A := A) (hW := h)).2 ?_)
  · filter_upwards [chartValueL_prodEquiv_fst_ae (contMDiffSMulL (A.prod h) μ p k hφ w) i,
      chartValueL_prodEquiv_fst_ae w i, hw i,
      chartValueL_contMDiffSMulL_ae hφ (prodEquiv A h μ p k w).1 i] with y h₁ h₂ h₃ h₄
    rw [h₁, h₃, h₄, Prod.smul_fst, h₂]
    exact congrArg (fun e : OpenPartialHomeomorph M E ↦ φ (e.symm y) • _) (chart_prod (h := h) i)
  · filter_upwards [chartValueL_prodEquiv_snd_ae (contMDiffSMulL (A.prod h) μ p k hφ w) i,
      chartValueL_prodEquiv_snd_ae w i, hw i,
      (ae_restrict_image_ofBaseSet_iff (A := A) (hW := h)).1
        (chartValueL_contMDiffSMulL_ae hφ (prodEquiv A h μ p k w).2 i)] with y h₁ h₂ h₃ h₄
    rw [h₁, h₃, h₄, Prod.smul_snd, h₂]
    exact congrArg (fun e : OpenPartialHomeomorph M E ↦ φ (e.symm y) • _)
      ((chart_prod (h := h) i).trans (chart_ofBaseSet (h := h) i).symm)

/-- The inverse of `TauCeti.SobolevSection.prodEquiv` commutes with multiplication by a smooth
function. -/
theorem prodEquiv_symm_contMDiffSMulL [IsManifold 𝓘(ℝ, E) ∞ M] {φ : M → ℝ}
    (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (u : SobolevSection A μ p k)
    (v : SobolevSection (A.ofBaseSet h) μ p k) :
    (prodEquiv A h μ p k).symm
        (contMDiffSMulL A μ p k hφ u, contMDiffSMulL (A.ofBaseSet h) μ p k hφ v) =
      contMDiffSMulL (A.prod h) μ p k hφ ((prodEquiv A h μ p k).symm (u, v)) := by
  rw [ContinuousLinearEquiv.symm_apply_eq, prodEquiv_contMDiffSMulL,
    ContinuousLinearEquiv.apply_symm_apply]

/-- `TauCeti.SobolevSection.prodEquiv` sends the Sobolev section of a `Cᵏ` section
`σ = (s, t)` of `V ×ᵇ V'` to the pair of the Sobolev sections of `s` and `t`. -/
theorem prodEquiv_ofContMDiffSection [IsManifold 𝓘(ℝ, E) k M]
    [ContMDiffVectorBundle k F V 𝓘(ℝ, E)] [ContMDiffVectorBundle k F' V' 𝓘(ℝ, E)]
    {σ : Cₛ^k⟮𝓘(ℝ, E); F × F', V ×ᵇ V'⟯} {s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯} {t : Cₛ^k⟮𝓘(ℝ, E); F', V'⟯}
    (hσ : ∀ x, σ x = (s x, t x)) :
    prodEquiv A h μ p k (ofContMDiffSection (A.prod h) μ p k σ) =
      (ofContMDiffSection A μ p k s, ofContMDiffSection (A.ofBaseSet h) μ p k t) := by
  have hσ' : ∀ i, (A.prod h).sectionChartData.chartValueL μ p k i
      (ofContMDiffSection (A.prod h) μ p k σ) =ᵐ[μ.restrict (A.image i)] (A.prod h).coord i σ :=
    fun i ↦ (ae_restrict_image_prod_iff (A := A) (h := h) (i := i)).1
      (chartValueL_ofContMDiffSection_ae (A.prod h) μ p k σ i)
  have hs : (fun x ↦ (σ x).1) = s := funext fun x ↦ by rw [hσ]
  have ht : (fun x ↦ (σ x).2) = t := funext fun x ↦ by rw [hσ]
  refine Prod.ext (SobolevSection.eq_of_ae_eq_coord (s := s) (fun i ↦ ?_)
    (chartValueL_ofContMDiffSection_ae A μ p k s)) (SobolevSection.eq_of_ae_eq_coord (s := t)
      (fun i ↦ ?_) (chartValueL_ofContMDiffSection_ae (A.ofBaseSet h) μ p k t))
  · rw [← hs]
    exact chartValueL_prodEquiv_fst_ae_coord (hσ' i)
  · rw [← ht]
    exact (ae_restrict_image_ofBaseSet_iff (A := A) (hW := h)).2
      (chartValueL_prodEquiv_snd_ae_coord (hσ' i))

/-- The inverse of `TauCeti.SobolevSection.prodEquiv` sends the pair of the Sobolev sections of
`Cᵏ` sections `s` and `t` to the Sobolev section of `σ = (s, t)`. -/
theorem prodEquiv_symm_ofContMDiffSection [IsManifold 𝓘(ℝ, E) k M]
    [ContMDiffVectorBundle k F V 𝓘(ℝ, E)] [ContMDiffVectorBundle k F' V' 𝓘(ℝ, E)]
    {σ : Cₛ^k⟮𝓘(ℝ, E); F × F', V ×ᵇ V'⟯} {s : Cₛ^k⟮𝓘(ℝ, E); F, V⟯} {t : Cₛ^k⟮𝓘(ℝ, E); F', V'⟯}
    (hσ : ∀ x, σ x = (s x, t x)) :
    (prodEquiv A h μ p k).symm
        (ofContMDiffSection A μ p k s, ofContMDiffSection (A.ofBaseSet h) μ p k t) =
      ofContMDiffSection (A.prod h) μ p k σ := by
  rw [ContinuousLinearEquiv.symm_apply_eq, prodEquiv_ofContMDiffSection hσ]


/-! ### One-forms with values in a product bundle -/

section TangentHom

variable [IsManifold 𝓘(ℝ, E) 1 M] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [∀ x, IsTopologicalAddGroup (V' x)]
  [∀ x, ContinuousSMul ℝ (V' x)]

variable (E F F') in
/-- The model fibres of one-forms with values in `V ×ᵇ V'`, in `V` and in `V'`:
`(E →L[ℝ] F × F') ≃L[ℝ] (E →L[ℝ] F) × (E →L[ℝ] F')`. -/
private noncomputable abbrev tangentHomFiberEquiv :
    (E →L[ℝ] F × F') ≃L[ℝ] (E →L[ℝ] F) × (E →L[ℝ] F') :=
  (ContinuousLinearMap.prodₗᵢ ℝ).toContinuousLinearEquiv.symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ F'] in
private theorem tangentHomFiberEquiv_symm_apply (a : E →L[ℝ] F) (b : E →L[ℝ] F') :
    (tangentHomFiberEquiv E F F').symm (a, b) = a.prod b :=
  rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ F'] in
private theorem tangentHomFiberEquiv_prod (a : E →L[ℝ] F) (b : E →L[ℝ] F') :
    tangentHomFiberEquiv E F F' (a.prod b) = (a, b) :=
  (tangentHomFiberEquiv E F F').apply_symm_apply (a, b)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ F'] in
private theorem tangentHomFiberEquiv_apply (X : E →L[ℝ] F × F') :
    tangentHomFiberEquiv E F F' X =
      ((ContinuousLinearMap.fst ℝ F F').comp X, (ContinuousLinearMap.snd ℝ F F').comp X) := by
  rw [← ContinuousLinearEquiv.eq_symm_apply, tangentHomFiberEquiv_symm_apply]
  ext <;> simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ F'] in
/-- On the image of a chart, `tangentHomFiberEquiv` sends the reading of a one-form with values in
`V ×ᵇ V'` to the readings of its components. -/
private theorem tangentHomFiberEquiv_coord (i : Fin A.n)
    (θ : ∀ x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] (V ×ᵇ V') x) {y : E} (hy : y ∈ A.image i) :
    tangentHomFiberEquiv E F F' ((A.prod h).tangentHom.coord i θ y) =
      (A.tangentHom.coord i (fun x ↦ (ContinuousLinearMap.fst ℝ (V x) (V' x)).comp (θ x)) y,
        (A.ofBaseSet h).tangentHom.coord i
          (fun x ↦ (ContinuousLinearMap.snd ℝ (V x) (V' x)).comp (θ x)) y) :=
  (congrArg _ (coord_tangentHom_prod A h i θ hy)).trans (tangentHomFiberEquiv_prod _ _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ F'] in
/-- On the image of a chart, `tangentHomFiberEquiv` sends the reading of the `prod` of two
one-forms to their readings. -/
private theorem tangentHomFiberEquiv_coord_prod (i : Fin A.n)
    (s : ∀ x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V x) (t : ∀ x, TangentSpace 𝓘(ℝ, E) x →L[ℝ] V' x)
    {y : E} (hy : y ∈ A.image i) :
    tangentHomFiberEquiv E F F' ((A.prod h).tangentHom.coord i
        (fun x ↦ ((s x).prod (t x) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] (V ×ᵇ V') x)) y) =
      (A.tangentHom.coord i s y, (A.ofBaseSet h).tangentHom.coord i t y) := by
  rw [tangentHomFiberEquiv_coord (h := h) i _ hy]
  simp only [ContinuousLinearMap.fst_comp_prod, ContinuousLinearMap.snd_comp_prod]

variable (A h μ p k) in
/-- **One-forms with values in a product bundle.** The Sobolev space `W^{k,p}` of one-forms with
values in `V ×ᵇ V'`, on the charts of `(A.prod h).tangentHom`, is isomorphic to the product of the
Sobolev spaces of `V`-valued one-forms on the charts of `A.tangentHom` and of `V'`-valued
one-forms on the charts of `(A.ofBaseSet h).tangentHom`. Its chart data are the compositions of
the chart data with the two projections of `F × F'`
(`TauCeti.SobolevSection.chartValueL_tangentHomProdEquiv_fst_ae`,
`TauCeti.SobolevSection.chartValueL_tangentHomProdEquiv_snd_ae`). -/
def tangentHomProdEquiv :
    SobolevSection (A.prod h).tangentHom μ p k ≃L[ℝ]
      SobolevSection A.tangentHom μ p k × SobolevSection (A.ofBaseSet h).tangentHom μ p k :=
  prodEquivOfCoord A μ p k (fun i ↦ (A.prod h).tangentHom.closure_dom_subset_baseSet i)
    (fun i ↦ A.tangentHom.closure_dom_subset_baseSet i)
    (fun i ↦ (A.ofBaseSet h).tangentHom.closure_dom_subset_baseSet i)
    (tangentHomFiberEquiv E F F')
    (fun θ x ↦ (ContinuousLinearMap.fst ℝ (V x) (V' x)).comp (θ x))
    (fun θ x ↦ (ContinuousLinearMap.snd ℝ (V x) (V' x)).comp (θ x))
    (fun s t x ↦ ((s x).prod (t x) : TangentSpace 𝓘(ℝ, E) x →L[ℝ] (V ×ᵇ V') x))
    (fun i θ _ hy ↦ tangentHomFiberEquiv_coord (h := h) i θ hy)
    (fun i s t _ hy ↦ tangentHomFiberEquiv_coord_prod (h := h) i s t hy)

/-- The chart data of the first component of `tangentHomProdEquiv A h μ p k w` are the chart data
of `w` followed by the first projection. -/
theorem chartValueL_tangentHomProdEquiv_fst_ae (w : SobolevSection (A.prod h).tangentHom μ p k)
    (i : Fin A.n) :
    A.tangentHom.sectionChartData.chartValueL μ p k i (tangentHomProdEquiv A h μ p k w).1
      =ᵐ[μ.restrict (A.image i)] fun y ↦ (ContinuousLinearMap.fst ℝ F F').comp
        ((A.prod h).tangentHom.sectionChartData.chartValueL μ p k i w y) :=
  (chartValueL_prodEquivOfCoord_fst_ae (A := A)
    (hf := fun i θ _ hy ↦ tangentHomFiberEquiv_coord (h := h) i θ hy)
    (hg := fun i s t _ hy ↦ tangentHomFiberEquiv_coord_prod (h := h) i s t hy)
    _ w i).mono fun _ hy ↦
    hy.trans (congrArg Prod.fst (tangentHomFiberEquiv_apply _))

/-- The chart data of the second component of `tangentHomProdEquiv A h μ p k w` are the chart
data of `w` followed by the second projection. -/
theorem chartValueL_tangentHomProdEquiv_snd_ae (w : SobolevSection (A.prod h).tangentHom μ p k)
    (i : Fin A.n) :
    (A.ofBaseSet h).tangentHom.sectionChartData.chartValueL μ p k i
        (tangentHomProdEquiv A h μ p k w).2
      =ᵐ[μ.restrict (A.image i)] fun y ↦ (ContinuousLinearMap.snd ℝ F F').comp
        ((A.prod h).tangentHom.sectionChartData.chartValueL μ p k i w y) :=
  (chartValueL_prodEquivOfCoord_snd_ae (A := A)
    (hf := fun i θ _ hy ↦ tangentHomFiberEquiv_coord (h := h) i θ hy)
    (hg := fun i s t _ hy ↦ tangentHomFiberEquiv_coord_prod (h := h) i s t hy)
    _ w i).mono fun _ hy ↦
    hy.trans (congrArg Prod.snd (tangentHomFiberEquiv_apply _))

/-- The chart data of `(tangentHomProdEquiv A h μ p k).symm (u, v)` are the `prod` of the chart
data of `u` and of `v`. -/
theorem chartValueL_tangentHomProdEquiv_symm_ae (u : SobolevSection A.tangentHom μ p k)
    (v : SobolevSection (A.ofBaseSet h).tangentHom μ p k) (i : Fin A.n) :
    (A.prod h).tangentHom.sectionChartData.chartValueL μ p k i
        ((tangentHomProdEquiv A h μ p k).symm (u, v))
      =ᵐ[μ.restrict (A.image i)] fun y ↦
        (A.tangentHom.sectionChartData.chartValueL μ p k i u y).prod
          ((A.ofBaseSet h).tangentHom.sectionChartData.chartValueL μ p k i v y) :=
  chartValueL_prodEquivOfCoord_symm_ae (A := A)
    (hf := fun i θ _ hy ↦ tangentHomFiberEquiv_coord (h := h) i θ hy)
    (hg := fun i s t _ hy ↦ tangentHomFiberEquiv_coord_prod (h := h) i s t hy) _ u v i

end TangentHom

end SobolevSection

end TauCeti
