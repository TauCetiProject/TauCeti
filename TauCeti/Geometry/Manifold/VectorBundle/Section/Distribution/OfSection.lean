/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Integral
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution
public import TauCeti.Geometry.Manifold.PartitionOfUnity.ChartCutoffs
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.MeasureTheory.Function.Jacobian
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Distributional sections of locally integrable sections

Let `W → M` be a smooth real vector bundle with model fibre `G` over a manifold modelled on a
finite-dimensional space `E`. Its distributional sections (`TauCeti.BundleDistribution`) act on the
tests `φ` of the dual-density bundle `W →L |Λ|` (`TauCeti.DualDensityTest`). A section `u` of `W`
pairs with such a test to the density `x ↦ φ x (u x)`, which can be integrated over `M` without a
measure (`TauCeti.integralDensity`). This file shows that, for locally integrable `u`, the result
is a distributional section `TauCeti.BundleDistribution.ofSection I G u`. This is the bundle
analogue of Mathlib's `Distribution.ofFun`, and follows its convention: the functional is zero when
`u` is not locally integrable, and `TauCeti.BundleDistribution.ofSection_apply` /
`TauCeti.BundleDistribution.ofSection_eq_zero_of_not_locallyIntegrableSection` correspond to
`Distribution.ofFun_apply` / `Distribution.ofFun_eq_zero`.

A section is **locally integrable** (`TauCeti.LocallyIntegrableSection`) when its local
representatives `TauCeti.FirstJetBundle.localRep I G u α` in the preferred chart and trivialization
at every point `α` are locally integrable where they are defined, for the Haar measure of the fixed
basis of the model. Local integrability can be checked in any cover of `M` by open sets lying in
the chart and trivialization domains of points `β j`
(`TauCeti.locallyIntegrableSection_iff_of_iUnion_eq_univ`), since a change of charts is a
diffeomorphism and a change of trivializations a continuous field of linear isomorphisms, which
preserve local integrability (`MeasureTheory.LocallyIntegrableOn.comp_contDiffOn_diffeo`,
`MeasureTheory.LocallyIntegrableOn.continuousOn_clm_apply`). For the same reason readings agreeing
almost everywhere in such a cover agree almost everywhere in every preferred chart
(`TauCeti.localRep_ae_eq_of_iUnion_eq_univ`), and the distributional section of `u` only depends
on its readings almost everywhere (`TauCeti.BundleDistribution.ofSection_congr_ae`, the analogue of
`Distribution.ofFun_congr_ae`).

The key computation is in a restriction `c` of the preferred chart at `α` and the preferred frame
of the dual-density bundle (`TauCeti.RoughDensity.inChartAt_pairing`): there the density paired
with the extension of a test function `ψ` is `y ↦ ψ y (u read at y)`, with no Jacobian factor,
because the preferred frame of the density line is the density of the inverse tangent frame of
the same chart. Hence the paired density is integrable and its integral is the integral of `ψ`
against the reading of `u` (`TauCeti.integralDensity_chartTestCLM`). Every test is a finite sum of
such extensions of its chart localizations along chart cutoffs (`TauCeti.ChartCutoffs`), so the
pairing is integrable for every test (`TauCeti.LocallyIntegrableSection.integrableDensity`), linear,
and continuous on each fixed-compact support stage, hence continuous for the test topology. The
local representative of `TauCeti.BundleDistribution.ofSection I G u` in such a chart and frame is
the reading of `u` (`TauCeti.chartDistributionCLM_ofSection_apply_apply`). The decomposition of
tests along chart cutoffs is `TauCeti.ChartCutoffs.sum_chartTestSection_chartLocalization`, read on
bundle tests as in the proof of `ContMDiffSection.span_iUnion_range_chartTestSection_eq_top`, and
the integrals in charts are Mathlib's `TestFunction.integralAgainstBilinCLM`, the map underlying
`Distribution.ofFun`.

## Main declarations

* `TauCeti.LocallyIntegrableSection`: local integrability of a section, with
  `TauCeti.locallyIntegrableSection_def`, `TauCeti.LocallyIntegrableSection.locallyIntegrableOn`,
  `TauCeti.LocallyIntegrableSection.zero`, `TauCeti.LocallyIntegrableSection.add` and
  `TauCeti.LocallyIntegrableSection.smul`.
* `TauCeti.locallyIntegrableSection_iff_of_iUnion_eq_univ`,
  `TauCeti.localRep_ae_eq_of_iUnion_eq_univ`: local integrability and almost everywhere equality of
  readings from a chart cover.
* `TauCeti.BundleDistribution.ofSection`: the distributional section of a section, zero unless
  the section is locally integrable, with `TauCeti.BundleDistribution.ofSection_apply`,
  `TauCeti.BundleDistribution.ofSection_zero`, `TauCeti.BundleDistribution.ofSection_add` and
  `TauCeti.BundleDistribution.ofSection_smul`; it only depends on the readings almost everywhere
  (`TauCeti.BundleDistribution.ofSection_congr_ae`).
* `TauCeti.integralDensity_chartTestCLM`: the pairing with a test extended through a restriction
  of a preferred chart.
* `TauCeti.chartDistributionCLM_ofSection_apply_apply`: the local representative.

## References

* J. J. Duistermaat, J. A. C. Kolk, *Distributions: Theory and Applications*, Birkhäuser, 2010,
  §§16, 19 (densities and distributional sections on manifolds).
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
-/

public section

noncomputable section

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Distributions

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {W : M → Type*} [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace G W)]
  [FiberBundle G W] [VectorBundle ℝ G W]

-- The preferred trivializations of the dual-density bundle `W →L |Λ|`, written with the section
-- variables `G`, `W`, `I`, `M`.
local macro "𝒯" : term =>
  `(trivializationAt ($(Lean.mkIdent `G) →L[ℝ] ℝ)
    (fun x ↦ $(Lean.mkIdent `W) x →L[ℝ] DensityBundle $(Lean.mkIdent `I) $(Lean.mkIdent `M) x))

/-- **Paired densities in preferred charts.** Read in the preferred chart at `α` and the fixed basis
of the model, the density `x ↦ φ x (u x)` paired from a section `φ` of the dual-density bundle and
a section `u` of `W` is the reading of `φ` in the preferred frame of the dual-density bundle,
applied to the reading of `u` in the preferred trivialization of `W`. -/
theorem RoughDensity.inChartAt_pairing (φ : (x : M) → W x →L[ℝ] DensityBundle I M x)
    (u : (x : M) → W x)
    (α : M) {y : E} (hy : y ∈ (extChartAt I α).target)
    (hyb : (extChartAt I α).symm y ∈ (trivializationAt G W α).baseSet) :
    RoughDensity.inChartAt (fun x ↦ φ x (u x)) (Module.finBasis ℝ E) α y =
      (𝒯 α
        ⟨(extChartAt I α).symm y, φ ((extChartAt I α).symm y)⟩).2
        (trivializationAt G W α ⟨(extChartAt I α).symm y, u ((extChartAt I α).symm y)⟩).2 := by
  have hx : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hy
  have hxd : (extChartAt I α).symm y ∈ (trivializationAt ℝ (DensityBundle I M) α).baseSet := by
    simpa [TauCeti.Density.trivializationAt_eq] using hx
  rw [RoughDensity.inChartAt_of_mem_target _ _ _ hy, hom_trivializationAt_apply,
    ContinuousLinearMap.inCoordinates_eq hyb hxd]
  rw [Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ _ _ hyb]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [Trivialization.continuousLinearEquivAt_apply, TauCeti.Density.trivializationAt_eq]
  beta_reduce
  rw [Trivialization.density_apply]
  congr 1
  funext i
  rw [← Trivialization.symmL_apply (R := ℝ) _ (by simpa using hx),
    TangentBundle.symmL_trivializationAt hx, (extChartAt I α).right_inv hy]
  -- The two sides differ only in reading `Module.finBasis ℝ E i` as a vector of
  -- `TangentSpace 𝓘(ℝ, E) y`, which unfolds to `E`.
  rfl

section Measure

variable [MeasurableSpace E] [BorelSpace E]

variable (I G) in
/-- A section is locally integrable when its readings in the preferred charts and trivializations
are locally integrable where they are defined: Mathlib's `MeasureTheory.LocallyIntegrableOn`, read
chart by chart. -/
def LocallyIntegrableSection (u : (x : M) → W x) : Prop :=
  ∀ α : M, LocallyIntegrableOn (FirstJetBundle.localRep I G u α)
    ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (trivializationAt G W α).baseSet)
    (Module.finBasis ℝ E).addHaar

omit [IsManifold I ∞ M] [NormedSpace ℝ G] [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [VectorBundle ℝ G W] in
/-- A section is locally integrable exactly when its readings in the preferred charts and
trivializations are locally integrable where they are defined. -/
theorem locallyIntegrableSection_def {u : (x : M) → W x} :
    LocallyIntegrableSection I G u ↔ ∀ α : M, LocallyIntegrableOn (FirstJetBundle.localRep I G u α)
      ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (trivializationAt G W α).baseSet)
      (Module.finBasis ℝ E).addHaar :=
  Iff.rfl

omit [IsManifold I ∞ M] [NormedSpace ℝ G] [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [VectorBundle ℝ G W] in
/-- The reading of a locally integrable section at `α` is locally integrable where it is
defined. -/
theorem LocallyIntegrableSection.locallyIntegrableOn {u : (x : M) → W x}
    (hu : LocallyIntegrableSection I G u) (α : M) :
    LocallyIntegrableOn (FirstJetBundle.localRep I G u α)
      ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (trivializationAt G W α).baseSet)
      (Module.finBasis ℝ E).addHaar :=
  locallyIntegrableSection_def.1 hu α

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [NormedSpace ℝ G] [∀ x, AddCommGroup (W x)]
  [∀ x, Module ℝ (W x)] [VectorBundle ℝ G W] in
/-- The readings of a section are defined on a measurable set. -/
private theorem measurableSet_inter_preimage_baseSet (α : M) :
    MeasurableSet ((extChartAt I α).target ∩
      (extChartAt I α).symm ⁻¹' (trivializationAt G W α).baseSet) := by
  rw [← (extChartAt I α).image_source_inter_eq']
  exact (trivializationAt G W α).open_baseSet.measurableSet_image_extChartAt_source_inter α

omit [IsManifold I ∞ M] in
/-- Sums of locally integrable sections are locally integrable. -/
theorem LocallyIntegrableSection.add {u v : (x : M) → W x} (hu : LocallyIntegrableSection I G u)
    (hv : LocallyIntegrableSection I G v) :
    LocallyIntegrableSection I G fun x ↦ u x + v x := locallyIntegrableSection_def.2 fun α ↦
  ((hu.locallyIntegrableOn α).add (hv.locallyIntegrableOn α)).congr
    ((ae_restrict_iff' (measurableSet_inter_preimage_baseSet α)).2 (ae_of_all _ fun y hy ↦ by
      simp only [Pi.add_apply, FirstJetBundle.localRep_apply,
        Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ _ _ hy.2, map_add]))

omit [IsManifold I ∞ M] in
/-- Constant multiples of locally integrable sections are locally integrable. -/
theorem LocallyIntegrableSection.smul {u : (x : M) → W x} (hu : LocallyIntegrableSection I G u)
    (a : ℝ) : LocallyIntegrableSection I G fun x ↦ a • u x := locallyIntegrableSection_def.2 fun α ↦
  ((hu.locallyIntegrableOn α).smul a).congr
    ((ae_restrict_iff' (measurableSet_inter_preimage_baseSet α)).2 (ae_of_all _ fun y hy ↦ by
      simp only [Pi.smul_apply, FirstJetBundle.localRep_apply,
        Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ _ _ hy.2, map_smul]))

omit [IsManifold I ∞ M] in
/-- The zero section is locally integrable. -/
theorem LocallyIntegrableSection.zero : LocallyIntegrableSection I G fun x ↦ (0 : W x) :=
  locallyIntegrableSection_def.2 fun α ↦ locallyIntegrableOn_zero.congr
    ((ae_restrict_iff' (measurableSet_inter_preimage_baseSet α)).2 (ae_of_all _ fun y hy ↦ by
      simp only [FirstJetBundle.localRep_apply,
        Trivialization.apply_eq_prod_continuousLinearEquivAt ℝ _ _ hy.2, map_zero]))

/-! ### Changes of chart -/

section ChangeOfChart

omit [IsManifold I ∞ M]

variable [I.Boundaryless] {α β : M} {D : Set M}

omit [I.Boundaryless] [FiniteDimensional ℝ E] [NormedSpace ℝ G] [∀ x, AddCommGroup (W x)]
  [∀ x, Module ℝ (W x)] [VectorBundle ℝ G W] [MeasurableSpace E] [BorelSpace E] in
/-- Every point where the readings at `α` are defined is the image in the preferred chart at `α` of
a point of one of the sets `D j ∩ baseSet α`, when the `D j` cover `M`. -/
private theorem exists_mem_image_inter_baseSet {ι : Type*} {D : ι → Set M}
    (hcover : ⋃ j, D j = univ) {y : E}
    (hy : y ∈ (extChartAt I α).target ∩
      (extChartAt I α).symm ⁻¹' (trivializationAt G W α).baseSet) :
    ∃ j, y ∈ extChartAt I α '' (D j ∩ FirstJetBundle.baseSet (H := H) G W α) := by
  obtain ⟨j, hj⟩ := mem_iUnion.1 (hcover ▸ mem_univ ((extChartAt I α).symm y))
  have hx := (extChartAt I α).map_target hy.1
  rw [extChartAt_source] at hx
  exact ⟨j, _, ⟨hj, (FirstJetBundle.mem_baseSet_iff G W).2 ⟨hy.2, hx⟩⟩,
    (extChartAt I α).right_inv hy.1⟩

omit [FiniteDimensional ℝ E] [NormedSpace ℝ G] [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [VectorBundle ℝ G W] [MeasurableSpace E] [BorelSpace E] in
/-- The image in the preferred chart at `α` of an open subset of the first-jet chart domain at `α`
is open. -/
private theorem isOpen_image_extChartAt (hD : IsOpen D)
    (hDα : D ⊆ FirstJetBundle.baseSet (H := H) G W α) : IsOpen (extChartAt I α '' D) := by
  have hDs : D ⊆ (extChartAt I α).source := fun x hx ↦ by
    rw [extChartAt_source]
    exact ((FirstJetBundle.mem_baseSet_iff G W).1 (hDα hx)).2
  rw [← inter_eq_right.2 hDs, (extChartAt I α).image_source_inter_eq']
  exact (continuousOn_extChartAt_symm α).isOpen_inter_preimage (isOpen_extChartAt_target α) hD

variable [IsManifold I 1 M]

omit [FiniteDimensional ℝ E] [NormedSpace ℝ G] [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [VectorBundle ℝ G W] [MeasurableSpace E] [BorelSpace E] in
/-- On the image in the preferred chart at `α` of an open set `D` of the first-jet chart domains at
`α` and `β`, the change of preferred charts from `α` to `β` is `C¹` with invertible derivative,
injective, and maps into the image of `D` in the chart at `β`; the inverse chart at `α` maps into
the base sets of both preferred trivializations. -/
private theorem image_extChartAt_props (hD : IsOpen D)
    (hDα : D ⊆ FirstJetBundle.baseSet (H := H) G W α)
    (hDβ : D ⊆ FirstJetBundle.baseSet (H := H) G W β) :
    ContDiffOn ℝ 1 (extChartAt I β ∘ (extChartAt I α).symm) (extChartAt I α '' D) ∧
      (∀ y ∈ extChartAt I α '' D,
        (fderiv ℝ (extChartAt I β ∘ (extChartAt I α).symm) y).det ≠ 0) ∧
      MapsTo (extChartAt I β ∘ (extChartAt I α).symm) (extChartAt I α '' D)
        (extChartAt I β '' D) ∧
      InjOn (extChartAt I β ∘ (extChartAt I α).symm) (extChartAt I α '' D) ∧
      MapsTo (extChartAt I α).symm (extChartAt I α '' D)
        ((trivializationAt G W β).baseSet ∩ (trivializationAt G W α).baseSet) := by
  have hb (γ : M) (hDγ : D ⊆ FirstJetBundle.baseSet (H := H) G W γ) {x : M} (hx : x ∈ D) :=
    (FirstJetBundle.mem_baseSet_iff G W).1 (hDγ hx)
  have hDs : D ⊆ (extChartAt I α).source ∩ (extChartAt I β).source := fun x hx ↦ by
    rw [extChartAt_source, extChartAt_source]
    exact ⟨(hb α hDα hx).2, (hb β hDβ hx).2⟩
  have hsrc : extChartAt I α '' D ⊆
      (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (chartAt H β).source := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(extChartAt I α).map_source (hDs hx).1, ?_⟩
    rw [mem_preimage, (extChartAt I α).left_inv (hDs hx).1]
    exact (hb β hDβ hx).2
  refine ⟨(contDiffOn_ext_coord_change (n := 1) β α).mono fun y hy ↦ ?_, fun y hy ↦ ?_, ?_,
    (injOn_extChartAt_coordChange α β hDs).congr fun _ _ ↦ (rfl), ?_⟩
  · rw [PartialEquiv.trans_source, PartialEquiv.symm_source, extChartAt_source]
    exact hsrc hy
  · exact I.det_fderiv_extendCoordChange_ne_zero one_ne_zero
      (IsManifold.chart_mem_maximalAtlas α) (IsManifold.chart_mem_maximalAtlas β)
      (interior_maximal hsrc (isOpen_image_extChartAt hD hDα) hy)
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, by rw [Function.comp_apply, (extChartAt I α).left_inv (hDs hx).1]⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [(extChartAt I α).left_inv (hDs hx).1]
    exact ⟨(hb β hDβ hx).1, (hb α hDα hx).1⟩

omit [I.Boundaryless] [IsManifold I 1 M] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- On the image in the preferred chart at `α` of a set `D` of the first-jet chart domains at `α`
and `β`, the reading of a section at `α` is the coordinate change of `W` applied to its reading at
`β` after the change of charts: the pointwise form of
`TauCeti.FirstJetBundle.localRep_eventuallyEq_fiberCoordChange_nhds`. -/
private theorem localRep_eq_fiberCoordChange (u : (x : M) → W x)
    (hDα : D ⊆ FirstJetBundle.baseSet (H := H) G W α)
    (hDβ : D ⊆ FirstJetBundle.baseSet (H := H) G W β) {y : E} (hy : y ∈ extChartAt I α '' D) :
    FirstJetBundle.localRep I G u α y = FirstJetBundle.fiberCoordChange I G W β α y
      (FirstJetBundle.localRep I G u β ((extChartAt I β ∘ (extChartAt I α).symm) y)) := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact (FirstJetBundle.localRep_eventuallyEq_fiberCoordChange_nhds I G u (hDβ hx)
    (hDα hx)).eq_of_nhds

/-- Local integrability of the readings of a section passes from the chart at `β` to the chart at
`α`, on the images of an open set of both first-jet chart domains. -/
private theorem locallyIntegrableOn_localRep_of_locallyIntegrableOn (μ : Measure E)
    [μ.IsAddHaarMeasure] {u : (x : M) → W x} (hD : IsOpen D)
    (hDα : D ⊆ FirstJetBundle.baseSet (H := H) G W α)
    (hDβ : D ⊆ FirstJetBundle.baseSet (H := H) G W β)
    (hu : LocallyIntegrableOn (FirstJetBundle.localRep I G u β) (extChartAt I β '' D) μ) :
    LocallyIntegrableOn (FirstJetBundle.localRep I G u α) (extChartAt I α '' D) μ := by
  have hO := isOpen_image_extChartAt (I := I) hD hDα
  obtain ⟨hT, hdet, hmaps, -, hsymm⟩ := image_extChartAt_props (I := I) hD hDα hDβ
  have hc : ContinuousOn (FirstJetBundle.fiberCoordChange I G W β α) (extChartAt I α '' D) := by
    refine ((continuousOn_coordChange ℝ (trivializationAt G W β) (trivializationAt G W α)).comp
      ((continuousOn_extChartAt_symm α).mono ?_) hsymm).congr
      fun z _ ↦ FirstJetBundle.fiberCoordChange_apply I G W β α z
    rintro _ ⟨x, hx, rfl⟩
    exact (extChartAt I α).map_source (by
      rw [extChartAt_source]
      exact ((FirstJetBundle.mem_baseSet_iff G W).1 (hDα hx)).2)
  exact ((hu.comp_contDiffOn_diffeo hO hT hdet hmaps).continuousOn_clm_apply hO.isLocallyClosed
    hc).congr ((ae_restrict_iff' hO.measurableSet).2 (ae_of_all _ fun y hy ↦
      (localRep_eq_fiberCoordChange u hDα hDβ hy).symm))

/-- Almost everywhere equality of the readings of two sections passes from the chart at `β` to the
chart at `α`, on the images of an open set of both first-jet chart domains. -/
private theorem localRep_ae_eq_of_ae_eq (μ : Measure E) [μ.IsAddHaarMeasure]
    {u v : (x : M) → W x} (hD : IsOpen D) (hDα : D ⊆ FirstJetBundle.baseSet (H := H) G W α)
    (hDβ : D ⊆ FirstJetBundle.baseSet (H := H) G W β)
    (h : FirstJetBundle.localRep I G u β =ᵐ[μ.restrict (extChartAt I β '' D)]
      FirstJetBundle.localRep I G v β) :
    FirstJetBundle.localRep I G u α =ᵐ[μ.restrict (extChartAt I α '' D)]
      FirstJetBundle.localRep I G v α := by
  have hO := isOpen_image_extChartAt (I := I) hD hDα
  obtain ⟨hT, hdet, hmaps, hinj, -⟩ := image_extChartAt_props (I := I) hD hDα hDβ
  filter_upwards [ae_restrict_comp_of_differentiableOn μ
      (P := fun z ↦ FirstJetBundle.localRep I G u β z = FirstJetBundle.localRep I G v β z) hO
      (hT.differentiableOn one_ne_zero) hinj hdet hmaps h,
    ae_restrict_mem hO.measurableSet] with y hy hyO
  rw [localRep_eq_fiberCoordChange u hDα hDβ hyO, localRep_eq_fiberCoordChange v hDα hDβ hyO, hy]

variable (I G) in
/-- **Local integrability in a chart cover.** Let the open sets `D j` cover `M`, each inside the
first-jet chart domain at a point `β j` (the chart source and the trivialization base set at
`β j`). A section is locally integrable exactly when its readings at `β j` are locally integrable on
the images of the `D j`, for any additive Haar measure `μ` of the model: the readings in all other
preferred charts follow by the change of charts, which preserves local integrability
(`MeasureTheory.LocallyIntegrableOn.comp_contDiffOn_diffeo`). -/
theorem locallyIntegrableSection_iff_of_iUnion_eq_univ {ι : Type*} (β : ι → M) (D : ι → Set M)
    (hD : ∀ j, IsOpen (D j)) (hDβ : ∀ j, D j ⊆ FirstJetBundle.baseSet (H := H) G W (β j))
    (hcover : ⋃ j, D j = univ) (μ : Measure E) [μ.IsAddHaarMeasure] {u : (x : M) → W x} :
    LocallyIntegrableSection I G u ↔
      ∀ j, LocallyIntegrableOn (FirstJetBundle.localRep I G u (β j)) (extChartAt I (β j) '' D j)
        μ := by
  refine ⟨fun hu j ↦ ((hu.locallyIntegrableOn (β j)).mono_set ?_).of_isAddHaarMeasure μ,
    fun h ↦ locallyIntegrableSection_def.2 fun α y hy ↦ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' := (FirstJetBundle.mem_baseSet_iff G W).1 (hDβ j hx)
    have hxs : x ∈ (extChartAt I (β j)).source := by
      rw [extChartAt_source]
      exact hx'.2
    refine ⟨(extChartAt I (β j)).map_source hxs, ?_⟩
    rw [mem_preimage, (extChartAt I (β j)).left_inv hxs]
    exact hx'.1
  · obtain ⟨j, hj⟩ := exists_mem_image_inter_baseSet (I := I) (G := G) (W := W) hcover hy
    have hD' := (hD j).inter (FirstJetBundle.isOpen_baseSet (H := H) G W α)
    have hloc := locallyIntegrableOn_localRep_of_locallyIntegrableOn (Module.finBasis ℝ E).addHaar
      hD' inter_subset_right (inter_subset_left.trans (hDβ j))
      (((h j).of_isAddHaarMeasure _).mono_set (image_mono inter_subset_left))
    refine (hloc y hj).filter_mono ?_
    rw [(isOpen_image_extChartAt (I := I) hD' inter_subset_right).nhdsWithin_eq hj]
    exact nhdsWithin_le_nhds

variable (I G) in
/-- **Almost everywhere equality in a chart cover.** Let the open sets `D j`, countably many, cover
`M`, each inside the first-jet chart domain at a point `β j`. If the readings at `β j` of two
sections agree almost everywhere on the images of the `D j`, for an additive Haar measure `μ` of
the model, then their readings in every preferred chart agree almost everywhere where they are
defined. -/
theorem localRep_ae_eq_of_iUnion_eq_univ {ι : Type*} [Countable ι] (β : ι → M) (D : ι → Set M)
    (hD : ∀ j, IsOpen (D j)) (hDβ : ∀ j, D j ⊆ FirstJetBundle.baseSet (H := H) G W (β j))
    (hcover : ⋃ j, D j = univ) (μ : Measure E) [μ.IsAddHaarMeasure] {u v : (x : M) → W x}
    (h : ∀ j, FirstJetBundle.localRep I G u (β j) =ᵐ[μ.restrict (extChartAt I (β j) '' D j)]
      FirstJetBundle.localRep I G v (β j)) (α : M) :
    FirstJetBundle.localRep I G u α =ᵐ[(Module.finBasis ℝ E).addHaar.restrict
      ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (trivializationAt G W α).baseSet)]
      FirstJetBundle.localRep I G v α := by
  have hac := Measure.absolutelyContinuous_isAddHaarMeasure (Module.finBasis ℝ E).addHaar μ
  refine ae_restrict_of_ae_restrict_of_subset (fun y hy ↦ mem_iUnion.2
    (exists_mem_image_inter_baseSet (I := I) (G := G) (W := W) hcover hy)) ?_
  refine (ae_restrict_iUnion_iff _ _).2 fun j ↦ (hac.restrict _).ae_le ?_
  exact localRep_ae_eq_of_ae_eq μ ((hD j).inter (FirstJetBundle.isOpen_baseSet (H := H) G W α))
    inter_subset_right (inter_subset_left.trans (hDβ j))
    (ae_restrict_of_ae_restrict_of_subset (image_mono inter_subset_left) (h j))

end ChangeOfChart

variable [ContMDiffVectorBundle ∞ G W I] [T2Space M]
  {u : (x : M) → W x} {α : M}
  (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
  (hct : c.source ⊆
    (𝒯 α).baseSet)
  (hcα : ∀ x ∈ c.source, c x = extChartAt I α x)

omit [ContMDiffVectorBundle ∞ G W I] [MeasurableSpace E] [BorelSpace E] [T2Space M] in
include hct in
/-- A chart whose source lies over the base set of the preferred frame of the dual-density bundle
at `α` has its source in the chart source and in the base set of `W` at `α`. -/
private theorem source_subset_of_subset_baseSet :
    c.source ⊆ (chartAt H α).source ∩ (trivializationAt G W α).baseSet := by
  intro x hx
  have h := hct hx
  rw [hom_trivializationAt_baseSet, TauCeti.Density.trivializationAt_eq,
    Trivialization.density_baseSet, TangentBundle.trivializationAt_baseSet] at h
  exact ⟨h.2, h.1⟩

omit [ContMDiffVectorBundle ∞ G W I] [MeasurableSpace E] [BorelSpace E] [T2Space M] in
include hct hcα in
/-- A restriction of the preferred chart at `α` has the inverse of the preferred chart. -/
private theorem symm_eq_extChartAt_symm {y : E} (hy : y ∈ c.target) :
    c.symm y = (extChartAt I α).symm y := by
  have hx := c.map_target hy
  have hxs : c.symm y ∈ (extChartAt I α).source := by
    rw [extChartAt_source]
    exact (source_subset_of_subset_baseSet c hct hx).1
  rw [← c.right_inv hy, c.left_inv hx, hcα _ hx, (extChartAt I α).left_inv hxs]

omit [ContMDiffVectorBundle ∞ G W I] [MeasurableSpace E] [BorelSpace E] [T2Space M] in
include hct hcα in
/-- The target of a restriction of the preferred chart at `α` lies where the readings at `α` are
defined. -/
private theorem target_subset_inter_preimage_baseSet :
    c.target ⊆ (extChartAt I α).target ∩
      (extChartAt I α).symm ⁻¹' (trivializationAt G W α).baseSet := by
  intro y hy
  have hx := c.map_target hy
  have h := source_subset_of_subset_baseSet c hct hx
  refine ⟨?_, by rw [mem_preimage, ← symm_eq_extChartAt_symm c hct hcα hy]; exact h.2⟩
  rw [← c.right_inv hy, hcα _ hx]
  exact (extChartAt I α).map_source (by rw [extChartAt_source]; exact h.1)

omit [MeasurableSpace E] [BorelSpace E] in
include hcα in
/-- In a restriction `c` of the preferred chart at `α`, the density paired from a section `u` and
the extension of a test function `ψ` through `c` and the preferred frame is read as
`y ↦ ψ y (u read at y)`. -/
private theorem inChartAt_chartTestCLM (ψ : 𝓓(⟨c.target, c.open_target⟩, G →L[ℝ] ℝ)) (y : E) :
    RoughDensity.inChartAt
        (fun x ↦ (𝒯 α
          |>.chartTestCLM c hc hct ψ) x (u x)) (Module.finBasis ℝ E) α y =
      ψ y (FirstJetBundle.localRep I G u α y) := by
  by_cases hy : y ∈ c.target
  · have hx := c.map_target hy
    have hyt := target_subset_inter_preimage_baseSet c hct hcα hy
    rw [RoughDensity.inChartAt_pairing _ _ _ hyt.1 hyt.2, ← symm_eq_extChartAt_symm c hct hcα hy,
      Bundle.Trivialization.chartTestCLM_apply_of_mem _ _ _ _ _ hx, c.right_inv hy,
      Trivialization.symmL_apply _ (hct hx), Trivialization.apply_mk_symm _ (hct hx),
      FirstJetBundle.localRep_apply,
      symm_eq_extChartAt_symm c hct hcα hy]
  · rw [show ψ y = 0 from ψ.zero_on_compl hy, zero_apply]
    by_cases hyt : y ∈ (extChartAt I α).target
    · have hxc : (extChartAt I α).symm y ∉ c.source := fun hx ↦ by
        have h := c.map_source hx
        rw [hcα _ hx, (extChartAt I α).right_inv hyt] at h
        exact hy h
      rw [RoughDensity.inChartAt_of_mem_target _ _ _ hyt,
        Bundle.Trivialization.chartTestCLM_apply_of_notMem _ _ _ _ _ hxc]
      -- The zero map gives the zero density, whose value on any basis is zero.
      rfl
    · exact RoughDensity.inChartAt_of_notMem_target _ _ _ hyt

omit [ContMDiffVectorBundle ∞ G W I] [MeasurableSpace E] [BorelSpace E] [T2Space M] in
/-- The density paired from a test and a section vanishes where the test does. -/
private theorem tsupport_pairing_subset
    (φ : DualDensityTest I M G W) (u : (x : M) → W x) :
    _root_.tsupport (α := Density E (Module.finrank ℝ E)) (fun x ↦ φ x (u x)) ⊆
      closure {x | φ x ≠ 0} :=
  -- The zero map gives the zero density.
  closure_mono fun x hx h0 ↦ (Function.mem_support.1 hx) (by rw [h0]; rfl)

omit [MeasurableSpace E] [BorelSpace E] in
include hct in
/-- The density paired with a test extended through a chart has compact support in the chart
source. -/
private theorem isCompact_tsupport_pairing_chartTestCLM_and_subset_source
    (ψ : 𝓓(⟨c.target, c.open_target⟩, G →L[ℝ] ℝ)) :
    IsCompact (_root_.tsupport (α := Density E (Module.finrank ℝ E)) fun x ↦
        ((𝒯 α).chartTestCLM c hc hct ψ) x (u x)) ∧
      _root_.tsupport (α := Density E (Module.finrank ℝ E)) (fun x ↦
        ((𝒯 α).chartTestCLM c hc hct ψ) x (u x)) ⊆ c.source := by
  have hsub := tsupport_pairing_subset ((𝒯 α).chartTestCLM c hc hct ψ) u
  refine ⟨(BundleTest.isCompact_tsupport _).of_isClosed_subset (isClosed_tsupport _) hsub,
    hsub.trans ?_⟩
  rw [Bundle.Trivialization.coe_chartTestCLM, ← ContMDiffSection.tsupport_def]
  exact (𝒯 α).tsupport_chartTestSection_subset_source c hc hct ψ

include hcα in
/-- The density paired from a section with locally integrable reading and a test extended through a
restriction of the preferred chart at `α` and the preferred frame is integrable. -/
private theorem integrableDensity_chartTestCLM
    (hu : LocallyIntegrableOn (FirstJetBundle.localRep I G u α) c.target
      (Module.finBasis ℝ E).addHaar)
    (ψ : 𝓓(⟨c.target, c.open_target⟩, G →L[ℝ] ℝ)) :
    IntegrableDensity fun x ↦
      (𝒯 α
        |>.chartTestCLM c hc hct ψ) x (u x) := by
  obtain ⟨hK, hs⟩ := isCompact_tsupport_pairing_chartTestCLM_and_subset_source c hc hct ψ (u := u)
  rw [RoughDensity.integrableDensity_iff_of_tsupport_subset_chart (Module.finBasis ℝ E) α hK
    (hs.trans fun x hx ↦ (source_subset_of_subset_baseSet c hct hx).1)]
  have h := ψ.integrable_bilin (ContinuousLinearMap.id ℝ (G →L[ℝ] ℝ)) hu
    (μ := (Module.finBasis ℝ E).addHaar)
  exact h.congr (ae_of_all _ fun y ↦ (inChartAt_chartTestCLM c hc hct hcα ψ y).symm)

include hcα in
/-- The integral of the density paired from a locally integrable section and a test extended
through a restriction of the preferred chart at `α` and the preferred frame is the integral of the
test against the reading of the section, provided that reading is locally integrable on the chart
target. -/
theorem integralDensity_chartTestCLM
    (hu : LocallyIntegrableOn (FirstJetBundle.localRep I G u α) c.target
      (Module.finBasis ℝ E).addHaar)
    (ψ : 𝓓(⟨c.target, c.open_target⟩, G →L[ℝ] ℝ)) :
    integralDensity (fun x ↦
      (𝒯 α
        |>.chartTestCLM c hc hct ψ) x (u x)) =
      TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.id ℝ (G →L[ℝ] ℝ))
        (Module.finBasis ℝ E).addHaar (FirstJetBundle.localRep I G u α) ψ := by
  obtain ⟨-, hs⟩ := isCompact_tsupport_pairing_chartTestCLM_and_subset_source c hc hct ψ (u := u)
  rw [integralDensity_eq_integral_inChartAt (integrableDensity_chartTestCLM c hc hct hcα hu ψ)
      (Module.finBasis ℝ E) α fun x hx ↦ by
        rw [extChartAt_source]
        exact (source_subset_of_subset_baseSet c hct (hs (subset_tsupport _ hx))).1,
    TestFunction.integralAgainstBilinCLM_eq_integral hu]
  simp_rw [inChartAt_chartTestCLM c hc hct hcα ψ, ContinuousLinearMap.id_apply]

/-! ### The functional of a section -/

section Global

variable [I.Boundaryless] [SigmaCompactSpace M]

omit [ContMDiffVectorBundle ∞ G W I] [MeasurableSpace E] [BorelSpace E] in
/-- Chart cutoffs along the preferred charts restricted to the base sets of the preferred
trivializations of the dual-density bundle. -/
private theorem exists_chartCutoffs :
    ∃ A : ChartCutoffs I M ⊤ M, (∀ α, (A.chart α).source ⊆
        (𝒯 α).baseSet) ∧
      ∀ α, ∀ x ∈ (A.chart α).source, A.chart α x = extChartAt I α x := by
  obtain ⟨A, hA⟩ := ChartCutoffs.exists_chart_eq
    (baseSetChart (G →L[ℝ] ℝ) I (fun x ↦ W x →L[ℝ] DensityBundle I M x))
    (contMDiffOn_baseSetChart (n := ((⊤ : ℕ∞) : ℕ∞ω)) _)
    (contMDiffOn_baseSetChart_symm (n := ((⊤ : ℕ∞) : ℕ∞ω)) _) (mem_baseSetChart_source _)
  refine ⟨A, fun α ↦ hA ▸ baseSetChart_source_subset _ α, fun α x _ ↦ ?_⟩
  rw [hA, coe_baseSetChart]

omit [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
/-- The localization of dual-density tests along the `α`-th chart cutoff, read in the `α`-th chart
and the preferred frame, as test functions on the chart target. -/
private def cutoffTestCLM (A : ChartCutoffs I M ⊤ M) (hA : ∀ α, (A.chart α).source ⊆ (𝒯 α).baseSet)
    (α : M) :
    DualDensityTest I M G W →L[ℝ] 𝓓(⟨(A.chart α).target, (A.chart α).open_target⟩, G →L[ℝ] ℝ) :=
  (TestFunction.ofSupportedInCLM ℝ (A.chartSupport_subset_target α)).comp
    ((𝒯 α).chartLocalizationCLM (A.chart α) (A.contMDiffOn_chart_symm α) (hA α) (A.cutoff α)
      (A.chartSupport α) (A.chartSupport_subset_target α) (A.mapsTo_chartSupport α))

omit [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- The localization along the `α`-th cutoff is the chart localization, as a test function on the
chart target. -/
private theorem cutoffTestCLM_apply (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ α, (A.chart α).source ⊆ (𝒯 α).baseSet) (α : M) (φ : DualDensityTest I M G W) :
    cutoffTestCLM A hA α φ = TestFunction.ofSupportedIn (A.chartSupport_subset_target α)
      ((𝒯 α).chartLocalizationCLM (A.chart α) (A.contMDiffOn_chart_symm α) (hA α) (A.cutoff α)
        (A.chartSupport α) (A.chartSupport_subset_target α) (A.mapsTo_chartSupport α) φ) := by
  rw [cutoffTestCLM, ContinuousLinearMap.comp_apply, TestFunction.coe_ofSupportedInCLM]

omit [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
/-- A dual-density test supported in a compact set `K` is the sum of the extensions of its chart
localizations along chart cutoffs meeting `K`:
`ChartCutoffs.sum_chartTestSection_chartLocalization` read on bundle tests, as in the proof of
`ContMDiffSection.span_iUnion_range_chartTestSection_eq_top`. -/
private theorem eq_sum_chartTestCLM (A : ChartCutoffs I M ⊤ M)
    (hA : ∀ α, (A.chart α).source ⊆ (𝒯 α).baseSet)
    (φ : DualDensityTest I M G W) {K : Set M} (hK : IsCompact K)
    (hφ : closure {x | φ x ≠ 0} ⊆ K) :
    φ = ∑ α ∈ A.meeting K hK,
      (𝒯 α).chartTestCLM (A.chart α) (A.contMDiffOn_chart α) (hA α) (cutoffTestCLM A hA α φ) := by
  have h := A.sum_chartTestSection_chartLocalization (fun α ↦ 𝒯 α) hA hK
    ((BundleTest.ofCompactlySupported _ _ _).symm φ).val
    (by rw [ContMDiffSection.tsupport_def]; exact hφ)
  refine BundleTest.ext fun x ↦ ?_
  rw [BundleTest.sum_apply]
  simp only [cutoffTestCLM_apply, Bundle.Trivialization.coe_chartTestCLM,
    Bundle.Trivialization.chartLocalizationCLM_apply]
  have hx := DFunLike.congr_fun h x
  simp only [ContMDiffSection.coe_sum, Finset.sum_apply] at hx
  exact hx.symm

omit [I.Boundaryless] [SigmaCompactSpace M] in
/-- The density paired from a locally integrable section and a dual-density test supported in a
compact set `K` is integrable, and its integral is the sum over the chart cutoffs meeting `K` of
the integrals of the chart localizations of the test against the readings of the section. -/
private theorem integrableDensity_and_integralDensity_eq_sum (hu : LocallyIntegrableSection I G u)
    (A : ChartCutoffs I M ⊤ M) (hA : ∀ α, (A.chart α).source ⊆ (𝒯 α).baseSet)
    (hAα : ∀ α, ∀ x ∈ (A.chart α).source, A.chart α x = extChartAt I α x)
    (φ : DualDensityTest I M G W) {K : Set M} (hK : IsCompact K)
    (hφ : closure {x | φ x ≠ 0} ⊆ K) :
    IntegrableDensity (fun x ↦ φ x (u x)) ∧
      integralDensity (fun x ↦ φ x (u x)) = ∑ α ∈ A.meeting K hK,
        TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.id ℝ (G →L[ℝ] ℝ))
          (Module.finBasis ℝ E).addHaar (FirstJetBundle.localRep I G u α)
          (cutoffTestCLM A hA α φ) := by
  have hd : (fun x ↦ φ x (u x) : RoughDensity I M (Module.finrank ℝ E)) =
      ∑ α ∈ A.meeting K hK, fun x ↦ ((𝒯 α).chartTestCLM (A.chart α) (A.contMDiffOn_chart α)
        (hA α) (cutoffTestCLM A hA α φ)) x (u x) := by
    conv_lhs => rw [eq_sum_chartTestCLM A hA φ hK hφ]
    funext x
    rw [BundleTest.sum_apply, sum_apply, Finset.sum_apply]
  have hi (α : M) (_ : α ∈ A.meeting K hK) := integrableDensity_chartTestCLM (A.chart α)
    (A.contMDiffOn_chart α) (hA α) (hAα α)
    ((hu.locallyIntegrableOn α).mono_set
      (target_subset_inter_preimage_baseSet (A.chart α) (hA α) (hAα α)))
    (cutoffTestCLM A hA α φ)
  rw [hd]
  refine ⟨IntegrableDensity.sum (Module.finBasis ℝ E) _ _ hi, ?_⟩
  rw [integralDensity_sum _ _ hi]
  exact Finset.sum_congr rfl fun α _ ↦ integralDensity_chartTestCLM _ _ _ (hAα α)
    ((hu.locallyIntegrableOn α).mono_set
      (target_subset_inter_preimage_baseSet (A.chart α) (hA α) (hAα α))) _

/-- The density paired from a locally integrable section and a dual-density test is integrable. -/
theorem LocallyIntegrableSection.integrableDensity (hu : LocallyIntegrableSection I G u)
    (φ : DualDensityTest I M G W) : IntegrableDensity fun x ↦ φ x (u x) := by
  obtain ⟨A, hA, hAα⟩ := exists_chartCutoffs (I := I) (G := G) (W := W)
  exact (integrableDensity_and_integralDensity_eq_sum hu A hA hAα φ
    (BundleTest.isCompact_tsupport φ) subset_rfl).1

/-- Pairing a locally integrable section with dual-density tests, as a linear functional. -/
private def ofSectionₗ (hu : LocallyIntegrableSection I G u) :
    DualDensityTest I M G W →ₗ[ℝ] ℝ where
  toFun φ := integralDensity fun x ↦ φ x (u x)
  map_add' φ ψ := by
    have h : (fun x ↦ (φ + ψ) x (u x) : RoughDensity I M (Module.finrank ℝ E)) =
        (fun x ↦ φ x (u x)) + fun x ↦ ψ x (u x) := by
      funext x
      rw [BundleTest.add_apply]
      -- Sums of maps and of densities are both pointwise.
      rfl
    rw [h, integralDensity_add (hu.integrableDensity φ) (hu.integrableDensity ψ)]
  map_smul' a φ := by
    have h : (fun x ↦ (a • φ) x (u x) : RoughDensity I M (Module.finrank ℝ E)) =
        a • fun x ↦ φ x (u x) := by
      funext x
      rw [BundleTest.smul_apply]
      -- Multiples of maps and of densities are both pointwise.
      rfl
    rw [h, integralDensity_smul, smul_eq_mul, RingHom.id_apply]

/-- Pairing a locally integrable section with dual-density tests is continuous: on the tests
supported in a fixed compact set it is a finite sum of chart localizations integrated against the
readings of the section. -/
private theorem continuous_ofSectionₗ (hu : LocallyIntegrableSection I G u) :
    Continuous (ofSectionₗ hu) := by
  obtain ⟨A, hA, hAα⟩ := exists_chartCutoffs (I := I) (G := G) (W := W)
  let := ContMDiffSection.frameTopology (I := I) (n := ∞)
    (fun x : M ↦ 𝒯 x)
    (fun x ↦ ⟨_, (𝒯 x
      ).open_baseSet⟩) fun _ ↦ subset_rfl
  refine (BundleTest.continuous_iff_continuous_comp (ofSectionₗ hu)).2 fun K ↦ ?_
  have heq : ⇑(ofSectionₗ hu) ∘ BundleTest.ofCompactlySupported _ _ _ ∘
      ContMDiffSection.ofSupportedIn K = fun σ ↦ ∑ α ∈ A.meeting K K.isCompact,
        TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.id ℝ (G →L[ℝ] ℝ))
          (Module.finBasis ℝ E).addHaar (FirstJetBundle.localRep I G u α) (cutoffTestCLM A hA α
            (BundleTest.ofCompactlySupported _ _ _ (ContMDiffSection.ofSupportedIn K σ))) :=
    funext fun σ ↦ (integrableDensity_and_integralDensity_eq_sum hu A hA hAα _ K.isCompact
      (BundleTest.tsupport_ofSupportedIn_subset K σ)).2
  rw [heq]
  exact continuous_finsetSum _ fun α _ ↦
    ((TestFunction.integralAgainstBilinCLM _ _ _).comp (cutoffTestCLM A hA α)).continuous.comp
      (BundleTest.continuous_ofSupportedIn K)

/-- Pairing a locally integrable section with dual-density tests, as a distributional section. -/
private def ofSectionCLM (hu : LocallyIntegrableSection I G u) : BundleDistribution I M G W :=
  { ofSectionₗ hu with cont := continuous_ofSectionₗ hu }

variable (I G) in
open scoped Classical in
/-- The **distributional section of a locally integrable section** `u` of `W`: the functional
`φ ↦ ∫ φ (u)` on the dual-density tests, integrating the density `x ↦ φ x (u x)`. This is the
bundle analogue of Mathlib's `Distribution.ofFun`, and follows its convention of being zero when
the input is not locally integrable. -/
def BundleDistribution.ofSection (u : (x : M) → W x) : BundleDistribution I M G W :=
  if hu : LocallyIntegrableSection I G u then ofSectionCLM hu else 0

/-- For a locally integrable section, `BundleDistribution.ofSection` is the pairing. -/
private theorem ofSection_eq_ofSectionCLM (hu : LocallyIntegrableSection I G u) :
    BundleDistribution.ofSection I G u = ofSectionCLM hu :=
  dite_eq_left hu

/-- A locally integrable section acts on a dual-density test by integrating the paired
density. -/
theorem BundleDistribution.ofSection_apply (hu : LocallyIntegrableSection I G u)
    (φ : DualDensityTest I M G W) :
    BundleDistribution.ofSection I G u φ = integralDensity fun x ↦ φ x (u x) := by
  rw [ofSection_eq_ofSectionCLM hu]
  -- `ofSectionCLM hu` applies the linear functional `ofSectionₗ hu`.
  rfl

/-- The distributional section of a section that is not locally integrable is zero. -/
theorem BundleDistribution.ofSection_eq_zero_of_not_locallyIntegrableSection
    (hu : ¬LocallyIntegrableSection I G u) : BundleDistribution.ofSection I G u = 0 := by
  exact dite_eq_right hu

/-- The distributional section of a section only depends on its readings almost everywhere where
they are defined: the analogue of Mathlib's `Distribution.ofFun_congr_ae`. -/
theorem BundleDistribution.ofSection_congr_ae {v : (x : M) → W x}
    (h : ∀ α, FirstJetBundle.localRep I G u α =ᵐ[(Module.finBasis ℝ E).addHaar.restrict
      ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' (trivializationAt G W α).baseSet)]
      FirstJetBundle.localRep I G v α) :
    BundleDistribution.ofSection I G u = BundleDistribution.ofSection I G v := by
  by_cases hu : LocallyIntegrableSection I G u
  · have hv : LocallyIntegrableSection I G v :=
      locallyIntegrableSection_def.2 fun α ↦ (hu.locallyIntegrableOn α).congr (h α)
    obtain ⟨A, hA, hAα⟩ := exists_chartCutoffs (I := I) (G := G) (W := W)
    ext φ
    rw [BundleDistribution.ofSection_apply hu, BundleDistribution.ofSection_apply hv,
      (integrableDensity_and_integralDensity_eq_sum hu A hA hAα φ
        (BundleTest.isCompact_tsupport φ) subset_rfl).2,
      (integrableDensity_and_integralDensity_eq_sum hv A hA hAα φ
        (BundleTest.isCompact_tsupport φ) subset_rfl).2]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [TestFunction.integralAgainstBilinCLM_congr_ae _ (ae_restrict_of_ae_restrict_of_subset
      (target_subset_inter_preimage_baseSet (A.chart α) (hA α) (hAα α)) (h α))]
  · rw [BundleDistribution.ofSection_eq_zero_of_not_locallyIntegrableSection hu,
      BundleDistribution.ofSection_eq_zero_of_not_locallyIntegrableSection fun hv ↦ hu
        (locallyIntegrableSection_def.2 fun α ↦ (hv.locallyIntegrableOn α).congr (h α).symm)]

variable [FiniteDimensional ℝ G] in
include hcα in
/-- **The local representative of the distributional section of `u`.** In a restriction `c` of the
preferred chart at `α` and the preferred frame of the dual-density bundle, the distributional
section of a locally integrable section `u` pairs a test function `φ` and a covector `v` of the
model fibre as the integral of `φ` against `v` applied to the reading of `u` in the preferred chart
and trivialization at `α`, for the Haar measure of the fixed basis of the model. -/
theorem chartDistributionCLM_ofSection_apply_apply (hu : LocallyIntegrableSection I G u)
    (φ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) (v : G →L[ℝ] ℝ) :
    (𝒯 α).chartDistributionCLM
        c hc hct (BundleDistribution.ofSection I G u) φ v =
      ∫ y, φ y * v (FirstJetBundle.localRep I G u α y) ∂(Module.finBasis ℝ E).addHaar := by
  have hloc := (hu.locallyIntegrableOn α).mono_set (target_subset_inter_preimage_baseSet c hct hcα)
  rw [Bundle.Trivialization.chartDistributionCLM_apply_apply, BundleDistribution.ofSection_apply hu,
    integralDensity_chartTestCLM c hc hct hcα hloc,
    TestFunction.integralAgainstBilinCLM_eq_integral hloc]
  simp

/-- The distributional section of a sum of locally integrable sections is the sum of their
distributional sections. -/
theorem BundleDistribution.ofSection_add {u v : (x : M) → W x}
    (hu : LocallyIntegrableSection I G u) (hv : LocallyIntegrableSection I G v) :
    BundleDistribution.ofSection I G (fun x ↦ u x + v x) =
      BundleDistribution.ofSection I G u + BundleDistribution.ofSection I G v := by
  ext φ
  rw [add_apply, BundleDistribution.ofSection_apply (hu.add hv),
    BundleDistribution.ofSection_apply hu, BundleDistribution.ofSection_apply hv,
    ← integralDensity_add (hu.integrableDensity φ) (hv.integrableDensity φ)]
  congr 1
  funext x
  exact map_add (φ x) (u x) (v x)

/-- The distributional section of the zero section is zero. -/
@[simp]
theorem BundleDistribution.ofSection_zero :
    BundleDistribution.ofSection I G (fun x ↦ (0 : W x)) = 0 := by
  ext φ
  rw [BundleDistribution.ofSection_apply LocallyIntegrableSection.zero, zero_apply]
  simp only [map_zero]
  exact integralDensity_zero

/-- The distributional section of a constant multiple of a section is the multiple of its
distributional section. -/
theorem BundleDistribution.ofSection_smul (u : (x : M) → W x) (a : ℝ) :
    BundleDistribution.ofSection I G (fun x ↦ a • u x) =
      a • BundleDistribution.ofSection I G u := by
  by_cases hu : LocallyIntegrableSection I G u
  · ext φ
    rw [smul_apply, BundleDistribution.ofSection_apply (hu.smul a),
      BundleDistribution.ofSection_apply hu, smul_eq_mul, ← integralDensity_smul]
    congr 1
    funext x
    exact map_smul (φ x) a (u x)
  · rcases eq_or_ne a 0 with rfl | ha
    · simp only [zero_smul]
      exact BundleDistribution.ofSection_zero
    · rw [BundleDistribution.ofSection_eq_zero_of_not_locallyIntegrableSection hu, smul_zero]
      refine BundleDistribution.ofSection_eq_zero_of_not_locallyIntegrableSection fun h ↦ hu ?_
      simpa [smul_smul, inv_mul_cancel₀ ha] using h.smul a⁻¹

end Global

end Measure

end TauCeti
