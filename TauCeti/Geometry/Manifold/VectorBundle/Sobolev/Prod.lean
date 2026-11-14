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

## Main definitions

* `TauCeti.SobolevSection.prodEquiv`: the isomorphism
  `W^{k,p}(V ×ᵇ V') ≃L[ℝ] W^{k,p}(V) × W^{k,p}(V')`.

## Main results

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

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ F'] [μ.IsAddHaarMeasure] in
/-- Almost everywhere on the image of chart `i`, the reading in the chart data of `A.prod h` of a
section of `V ×ᵇ V'` is the pair of the readings of its components in the charts of `A` and of
`A.ofBaseSet h`. -/
private theorem sectionChartData_coord_prod_ae (i : Fin A.n) (s : ∀ x, (V ×ᵇ V') x) :
    (A.prod h).sectionChartData.coord i s =ᵐ[μ.restrict (A.image i)]
      fun y ↦ (A.coord i (fun x ↦ (s x).1) y, (A.ofBaseSet h).coord i (fun x ↦ (s x).2) y) := by
  filter_upwards [ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy
  exact ((A.prod h).sectionChartData_coord_of_mem s
    ((FiniteBundleAtlas.image_prod (h := h) i).symm ▸ hy)).trans (coord_prod A h i s y)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [FiniteDimensional ℝ F]
  [FiniteDimensional ℝ F'] [μ.IsAddHaarMeasure] in
/-- An almost everywhere statement on the image of a chart of `A.prod h` is one on the image of
the corresponding chart of `A`. -/
private theorem ae_restrict_image_prod_iff {i : Fin A.n} {P : E → Prop} :
    (∀ᵐ y ∂μ.restrict ((A.prod h).sectionChartData.image i), P y) ↔
      ∀ᵐ y ∂μ.restrict (A.image i), P y := by
  rw [(A.prod h).sectionChartData_image i, FiniteBundleAtlas.image_prod]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [FiniteDimensional ℝ F'] [μ.IsAddHaarMeasure] in
/-- An almost everywhere statement on the image of a chart of `A.ofBaseSet h` is one on the image
of the corresponding chart of `A`. -/
private theorem ae_restrict_image_ofBaseSet_iff {i : Fin A.n} {P : E → Prop} :
    (∀ᵐ y ∂μ.restrict ((A.ofBaseSet h).sectionChartData.image i), P y) ↔
      ∀ᵐ y ∂μ.restrict (A.image i), P y := by
  rw [(A.ofBaseSet h).sectionChartData_image i, image_ofBaseSet]

variable (h μ p k) in
/-- The components of the first projection of a tuple of components on the charts of `A.prod h`.
-/
private def fstData :
    (A.prod h).sectionChartData.SobolevData μ p k →L[ℝ] A.sectionChartData.SobolevData μ p k :=
  fiberMapData μ p k (ContinuousLinearMap.fst ℝ F F') fun i ↦
    (FiniteBundleAtlas.image_prod (A := A) (h := h) i).ge

variable (h μ p k) in
/-- The components of the second projection of a tuple of components on the charts of
`A.prod h`. -/
private def sndData :
    (A.prod h).sectionChartData.SobolevData μ p k →L[ℝ]
      (A.ofBaseSet h).sectionChartData.SobolevData μ p k :=
  fiberMapData μ p k (ContinuousLinearMap.snd ℝ F F') fun i ↦
    ((image_ofBaseSet (A := A) (h := h) i).trans
      (FiniteBundleAtlas.image_prod (A := A) (h := h) i).symm).le

variable (h μ p k) in
/-- The components on the charts of `A.prod h` of the first inclusion of a tuple of components on
the charts of `A`. -/
private def inlData :
    A.sectionChartData.SobolevData μ p k →L[ℝ] (A.prod h).sectionChartData.SobolevData μ p k :=
  fiberMapData μ p k (ContinuousLinearMap.inl ℝ F F') fun i ↦
    (FiniteBundleAtlas.image_prod (A := A) (h := h) i).le

variable (h μ p k) in
/-- The components on the charts of `A.prod h` of the second inclusion of a tuple of components
on the charts of `A.ofBaseSet h`. -/
private def inrData :
    (A.ofBaseSet h).sectionChartData.SobolevData μ p k →L[ℝ]
      (A.prod h).sectionChartData.SobolevData μ p k :=
  fiberMapData μ p k (ContinuousLinearMap.inr ℝ F F') fun i ↦
    ((FiniteBundleAtlas.image_prod (A := A) (h := h) i).trans
      (image_ofBaseSet (A := A) (h := h) i).symm).le

private theorem chartValueL_fstData_ae (w : (A.prod h).sectionChartData.SobolevData μ p k)
    (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i (fstData h μ p k w) =ᵐ[μ.restrict (A.image i)]
      fun y ↦ ((A.prod h).sectionChartData.chartValueL μ p k i w y).1 :=
  chartValueL_ae_of_eq_fiberMap μ p k (C₁ := (A.prod h).sectionChartData)
    (C₂ := A.sectionChartData) (ContinuousLinearMap.fst ℝ F F') (i₁ := i) (i₂ := i)
    (FiniteBundleAtlas.image_prod (h := h) i).ge (w₁ := w) (fiberMapData_apply μ p k _ _ w i)

private theorem chartValueL_sndData_ae (w : (A.prod h).sectionChartData.SobolevData μ p k)
    (i : Fin A.n) :
    (A.ofBaseSet h).sectionChartData.chartValueL μ p k i (sndData h μ p k w)
      =ᵐ[μ.restrict (A.image i)]
      fun y ↦ ((A.prod h).sectionChartData.chartValueL μ p k i w y).2 :=
  (ae_restrict_image_ofBaseSet_iff (A := A) (h := h)).1 <| chartValueL_ae_of_eq_fiberMap μ p k
    (C₁ := (A.prod h).sectionChartData) (C₂ := (A.ofBaseSet h).sectionChartData)
    (ContinuousLinearMap.snd ℝ F F') (i₁ := i) (i₂ := i)
    ((image_ofBaseSet (A := A) (h := h) i).trans
      (FiniteBundleAtlas.image_prod (A := A) (h := h) i).symm).le (w₁ := w)
    (fiberMapData_apply μ p k _ _ w i)

private theorem chartValueL_inlData_add_inrData_ae (u : A.sectionChartData.SobolevData μ p k)
    (v : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) (i : Fin A.n) :
    (A.prod h).sectionChartData.chartValueL μ p k i (inlData h μ p k u + inrData h μ p k v)
      =ᵐ[μ.restrict (A.image i)] fun y ↦ (A.sectionChartData.chartValueL μ p k i u y,
        (A.ofBaseSet h).sectionChartData.chartValueL μ p k i v y) := by
  have hu := chartValueL_ae_of_eq_fiberMap μ p k (C₁ := A.sectionChartData)
    (C₂ := (A.prod h).sectionChartData) (ContinuousLinearMap.inl ℝ F F') (i₁ := i) (i₂ := i)
    (FiniteBundleAtlas.image_prod (A := A) (h := h) i).le (w₁ := u) (w₂ := inlData h μ p k u)
    (fiberMapData_apply μ p k _ _ u i)
  have hv := chartValueL_ae_of_eq_fiberMap μ p k (C₁ := (A.ofBaseSet h).sectionChartData)
    (C₂ := (A.prod h).sectionChartData) (ContinuousLinearMap.inr ℝ F F') (i₁ := i) (i₂ := i)
    ((FiniteBundleAtlas.image_prod (A := A) (h := h) i).trans
      (image_ofBaseSet (A := A) (h := h) i).symm).le (w₁ := v) (w₂ := inrData h μ p k v)
    (fiberMapData_apply μ p k _ _ v i)
  refine (ae_restrict_image_prod_iff (A := A) (h := h)).1 ?_
  filter_upwards [hu, hv, Lp.coeFn_add
    ((A.prod h).sectionChartData.chartValueL μ p k i (inlData h μ p k u))
    ((A.prod h).sectionChartData.chartValueL μ p k i (inrData h μ p k v))]
    with y hu hv hadd
  rw [map_add, hadd, Pi.add_apply, hu, hv]
  simp

variable (A h μ p k)

/-- The first component of `TauCeti.SobolevSection.prodEquiv`. -/
private def fstL : SobolevSection (A.prod h) μ p k →L[ℝ] SobolevSection A μ p k :=
  ((fstData h μ p k).comp ((A.prod h).sectionChartData.sobolevSections μ p k).subtypeL).codRestrict
    (A.sectionChartData.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := (A.prod h).sectionChartData.exists_section μ p k w
      refine (A.sectionChartData.mem_sobolevSections_iff μ p k).2 ⟨fun x ↦ (s x).1, fun i ↦ ?_⟩
      filter_upwards [chartValueL_fstData_ae (w : (A.prod h).sectionChartData.SobolevData μ p k) i,
        (ae_restrict_image_prod_iff (A := A) (h := h)).1 (hs i),
        sectionChartData_coord_prod_ae (μ := μ) (h := h) i s,
        A.sectionChartData_coord_ae_eq μ i fun x ↦ (s x).1] with y h₁ h₂ h₃ h₄
      exact h₁.trans ((congrArg Prod.fst (h₂.trans h₃)).trans h₄.symm)

/-- The second component of `TauCeti.SobolevSection.prodEquiv`. -/
private def sndL : SobolevSection (A.prod h) μ p k →L[ℝ] SobolevSection (A.ofBaseSet h) μ p k :=
  ((sndData h μ p k).comp ((A.prod h).sectionChartData.sobolevSections μ p k).subtypeL).codRestrict
    ((A.ofBaseSet h).sectionChartData.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := (A.prod h).sectionChartData.exists_section μ p k w
      refine ((A.ofBaseSet h).sectionChartData.mem_sobolevSections_iff μ p k).2
        ⟨fun x ↦ (s x).2, fun i ↦ (ae_restrict_image_ofBaseSet_iff (A := A) (h := h)).2 ?_⟩
      filter_upwards [chartValueL_sndData_ae (w : (A.prod h).sectionChartData.SobolevData μ p k) i,
        (ae_restrict_image_prod_iff (A := A) (h := h)).1 (hs i),
        sectionChartData_coord_prod_ae (μ := μ) (h := h) i s,
        (ae_restrict_image_ofBaseSet_iff (A := A) (h := h)).1
          ((A.ofBaseSet h).sectionChartData_coord_ae_eq μ i fun x ↦ (s x).2)] with y h₁ h₂ h₃ h₄
      exact h₁.trans ((congrArg Prod.snd (h₂.trans h₃)).trans h₄.symm)

/-- The inverse of `TauCeti.SobolevSection.prodEquiv`. -/
private def pairL :
    SobolevSection A μ p k × SobolevSection (A.ofBaseSet h) μ p k →L[ℝ]
      SobolevSection (A.prod h) μ p k :=
  ((inlData h μ p k).comp ((A.sectionChartData.sobolevSections μ p k).subtypeL.comp
      (ContinuousLinearMap.fst ℝ _ _)) +
    (inrData h μ p k).comp (((A.ofBaseSet h).sectionChartData.sobolevSections μ p k).subtypeL.comp
      (ContinuousLinearMap.snd ℝ _ _))).codRestrict
    ((A.prod h).sectionChartData.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := A.sectionChartData.exists_section μ p k w.1
      obtain ⟨t, ht⟩ := (A.ofBaseSet h).sectionChartData.exists_section μ p k w.2
      refine ((A.prod h).sectionChartData.mem_sobolevSections_iff μ p k).2
        ⟨fun x ↦ ((s x, t x) : (V ×ᵇ V') x), fun i ↦
          (ae_restrict_image_prod_iff (A := A) (h := h)).2 ?_⟩
      filter_upwards [chartValueL_inlData_add_inrData_ae (h := h)
          (w.1 : A.sectionChartData.SobolevData μ p k)
          (w.2 : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i,
        hs i, (ae_restrict_image_ofBaseSet_iff (A := A) (h := h)).1 (ht i),
        A.sectionChartData_coord_ae_eq μ i s,
        (ae_restrict_image_ofBaseSet_iff (A := A) (h := h)).1
          ((A.ofBaseSet h).sectionChartData_coord_ae_eq μ i t),
        sectionChartData_coord_prod_ae (μ := μ) (h := h) i fun x ↦ ((s x, t x) : (V ×ᵇ V') x)]
        with y h₁ h₂ h₃ h₄ h₅ h₆
      refine h₁.trans (h₆.trans ?_).symm
      exact Prod.ext (h₄.symm.trans h₂.symm) (h₅.symm.trans h₃.symm)

private theorem coe_fstL (w : SobolevSection (A.prod h) μ p k) :
    (fstL A h μ p k w : A.sectionChartData.SobolevData μ p k) = fstData h μ p k w := by
  simp [fstL]

private theorem coe_sndL (w : SobolevSection (A.prod h) μ p k) :
    (sndL A h μ p k w : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) =
      sndData h μ p k w := by
  simp [sndL]

private theorem coe_pairL (u : SobolevSection A μ p k) (v : SobolevSection (A.ofBaseSet h) μ p k) :
    (pairL A h μ p k (u, v) : (A.prod h).sectionChartData.SobolevData μ p k) =
      inlData h μ p k u + inrData h μ p k v := by
  simp [pairL]

/-- **Sobolev sections of a product bundle.** The Sobolev space `W^{k,p}(V ×ᵇ V')` on the charts
of `A.prod h` is isomorphic to the product of the Sobolev spaces `W^{k,p}(V)` on the charts of `A`
and `W^{k,p}(V')` on the charts of `A.ofBaseSet h`. Its chart data are the pair of projections of
the chart data (`TauCeti.SobolevSection.chartValueL_prodEquiv_fst_ae`,
`TauCeti.SobolevSection.chartValueL_prodEquiv_snd_ae`); on components, it acts by the constant
coordinates of the projections and inclusions of `F × F'` in the bases `Module.finBasis`. -/
def prodEquiv :
    SobolevSection (A.prod h) μ p k ≃L[ℝ]
      SobolevSection A μ p k × SobolevSection (A.ofBaseSet h) μ p k :=
  ContinuousLinearEquiv.equivOfInverse ((fstL A h μ p k).prod (sndL A h μ p k)) (pairL A h μ p k)
    (fun w ↦ SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
      (ae_restrict_image_prod_iff (A := A) (h := h)).2 <| by
      filter_upwards [chartValueL_inlData_add_inrData_ae (h := h) (fstData h μ p k w)
          (sndData h μ p k w) i,
        chartValueL_fstData_ae (w : (A.prod h).sectionChartData.SobolevData μ p k) i,
        chartValueL_sndData_ae (w : (A.prod h).sectionChartData.SobolevData μ p k) i]
        with y h₁ h₂ h₃
      rw [ContinuousLinearMap.prod_apply, coe_pairL, coe_fstL, coe_sndL]
      exact h₁.trans (Prod.ext h₂ h₃))
    fun w ↦ by
      obtain ⟨u, v⟩ := w
      refine Prod.ext (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦ ?_)
        (SectionChartData.eq_of_chartValueL_ae_eq fun i ↦
          (ae_restrict_image_ofBaseSet_iff (A := A) (h := h)).2 ?_)
      · filter_upwards [chartValueL_fstData_ae (pairL A h μ p k (u, v) :
            (A.prod h).sectionChartData.SobolevData μ p k) i,
          chartValueL_inlData_add_inrData_ae (h := h) (u : A.sectionChartData.SobolevData μ p k)
            (v : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i] with y h₁ h₂
        rw [ContinuousLinearMap.prod_apply, coe_fstL, coe_pairL]
        rw [coe_pairL] at h₁
        exact h₁.trans (congrArg Prod.fst h₂)
      · filter_upwards [chartValueL_sndData_ae (pairL A h μ p k (u, v) :
            (A.prod h).sectionChartData.SobolevData μ p k) i,
          chartValueL_inlData_add_inrData_ae (h := h) (u : A.sectionChartData.SobolevData μ p k)
            (v : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i] with y h₁ h₂
        rw [ContinuousLinearMap.prod_apply, coe_sndL, coe_pairL]
        rw [coe_pairL] at h₁
        exact h₁.trans (congrArg Prod.snd h₂)

private theorem prodEquiv_apply (w : SobolevSection (A.prod h) μ p k) :
    prodEquiv A h μ p k w = (fstL A h μ p k w, sndL A h μ p k w) := by
  rw [prodEquiv, ContinuousLinearEquiv.equivOfInverse_apply, ContinuousLinearMap.prod_apply]

private theorem prodEquiv_symm_apply
    (w : SobolevSection A μ p k × SobolevSection (A.ofBaseSet h) μ p k) :
    (prodEquiv A h μ p k).symm w = pairL A h μ p k w := by
  rw [prodEquiv, ContinuousLinearEquiv.symm_equivOfInverse,
    ContinuousLinearEquiv.equivOfInverse_apply]

variable {A h μ p k}

/-- The chart data of the first component of `prodEquiv A h μ p k w` are the first projections of
the chart data of `w`. -/
theorem chartValueL_prodEquiv_fst_ae (w : SobolevSection (A.prod h) μ p k) (i : Fin A.n) :
    A.sectionChartData.chartValueL μ p k i (prodEquiv A h μ p k w).1 =ᵐ[μ.restrict (A.image i)]
      fun y ↦ ((A.prod h).sectionChartData.chartValueL μ p k i w y).1 := by
  simp only [prodEquiv_apply, coe_fstL]
  exact chartValueL_fstData_ae (w : (A.prod h).sectionChartData.SobolevData μ p k) i

/-- The chart data of the second component of `prodEquiv A h μ p k w` are the second projections
of the chart data of `w`. -/
theorem chartValueL_prodEquiv_snd_ae (w : SobolevSection (A.prod h) μ p k) (i : Fin A.n) :
    (A.ofBaseSet h).sectionChartData.chartValueL μ p k i (prodEquiv A h μ p k w).2
      =ᵐ[μ.restrict (A.image i)]
      fun y ↦ ((A.prod h).sectionChartData.chartValueL μ p k i w y).2 := by
  simp only [prodEquiv_apply, coe_sndL]
  exact chartValueL_sndData_ae (w : (A.prod h).sectionChartData.SobolevData μ p k) i

/-- The chart data of `(prodEquiv A h μ p k).symm (u, v)` are the pairs of the chart data of `u`
and of `v`. -/
theorem chartValueL_prodEquiv_symm_ae (u : SobolevSection A μ p k)
    (v : SobolevSection (A.ofBaseSet h) μ p k) (i : Fin A.n) :
    (A.prod h).sectionChartData.chartValueL μ p k i ((prodEquiv A h μ p k).symm (u, v))
      =ᵐ[μ.restrict (A.image i)] fun y ↦ (A.sectionChartData.chartValueL μ p k i u y,
        (A.ofBaseSet h).sectionChartData.chartValueL μ p k i v y) := by
  rw [prodEquiv_symm_apply, coe_pairL]
  exact chartValueL_inlData_add_inrData_ae (h := h) (u : A.sectionChartData.SobolevData μ p k)
    (v : (A.ofBaseSet h).sectionChartData.SobolevData μ p k) i

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
      (ae_restrict_image_ofBaseSet_iff (A := A) (h := h)).2 ?_)
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
      (ae_restrict_image_ofBaseSet_iff (A := A) (h := h)).2 ?_)
  · filter_upwards [chartValueL_prodEquiv_fst_ae (contMDiffSMulL (A.prod h) μ p k hφ w) i,
      chartValueL_prodEquiv_fst_ae w i, hw i,
      chartValueL_contMDiffSMulL_ae hφ (prodEquiv A h μ p k w).1 i] with y h₁ h₂ h₃ h₄
    rw [h₁, h₃, h₄, Prod.smul_fst, h₂]
    exact congrArg (fun e : OpenPartialHomeomorph M E ↦ φ (e.symm y) • _) (chart_prod (h := h) i)
  · filter_upwards [chartValueL_prodEquiv_snd_ae (contMDiffSMulL (A.prod h) μ p k hφ w) i,
      chartValueL_prodEquiv_snd_ae w i, hw i,
      (ae_restrict_image_ofBaseSet_iff (A := A) (h := h)).1
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
    exact (ae_restrict_image_ofBaseSet_iff (A := A) (h := h)).2
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

end SobolevSection

end TauCeti
