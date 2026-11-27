/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.OfSection
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Sobolev sections as distributional sections

Let `M` be a smooth Hausdorff manifold without boundary modelled on a finite-dimensional real inner
product space `E`, let `V → M` be a smooth real vector bundle with finite-dimensional model fibre
`F`, and let `A` be a finite bundle atlas, so that `M` is compact. An element `w` of the Sobolev
space `W^{k,p}(V)` of `TauCeti.SobolevSection A μ p k`, for `1 ≤ p ≤ ∞` and an additive Haar measure
`μ` of `E`, consists of the chartwise components of a section `s`, determined almost everywhere in
the charts of `A` (`TauCeti.SobolevSection.exists_ae_eq_coord`). This file sends `w` to the
distributional section `TauCeti.BundleDistribution.ofSection` of `s`
(`TauCeti.SobolevSection.toBundleDistribution`), which pairs a test `φ` of the dual-density bundle
`V →L |Λ|` with `w` as the integral of the density `x ↦ φ x (s x)`
(`TauCeti.SobolevSection.toBundleDistribution_apply`). This is the bundle analogue of the map
`MeasureTheory.Lp` to distributions given by Mathlib's `Distribution.ofFun`.

Two facts make this well defined and linear. The section `s` is locally integrable in the sense of
`TauCeti.LocallyIntegrableSection` (`TauCeti.SobolevSection.locallyIntegrableSection`): its
readings in the charts of `A`, the chart data of `w`, are `Lᵖ` and so locally integrable, and the
readings in every other preferred chart follow by the change of charts
(`TauCeti.locallyIntegrableSection_iff_of_iUnion_eq_univ`). Two sections with the same chart data
have readings agreeing almost everywhere in every preferred chart
(`TauCeti.localRep_ae_eq_of_iUnion_eq_univ`), so they have the same distributional section
(`TauCeti.BundleDistribution.ofSection_congr_ae`).

## Main declarations

* `TauCeti.SobolevSection.locallyIntegrableSection`: the sections of elements of `W^{k,p}(V)` are
  locally integrable.
* `TauCeti.SobolevSection.toBundleDistribution`: the linear map from `W^{k,p}(V)` to the
  distributional sections of `V`, with `TauCeti.SobolevSection.toBundleDistribution_apply` and
  `TauCeti.SobolevSection.toBundleDistribution_eq_ofSection`.

## References

* J. J. Duistermaat, J. A. C. Kolk, *Distributions: Theory and Applications*, Birkhäuser, 2010,
  §§16, 19 (distributional sections of vector bundles).
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace TauCeti

namespace SobolevSection

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas E M F V} {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {k : ℕ}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- The reading of a section in the preferred charts at the centre of chart `i` of `A` is its
reading in chart `i`. -/
private theorem localRep_center (s : ∀ x, V x) (i : Fin A.n) :
    FirstJetBundle.localRep 𝓘(ℝ, E) F s (A.center i) = A.coord i s := by
  funext y
  rw [FirstJetBundle.localRep_apply, extChartAt_model_symm_eq_chartAt_symm, A.coord_def]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- The image of the domain of chart `i` of `A` in the preferred chart at its centre is the chart
image. -/
private theorem image_extChartAt_center (i : Fin A.n) :
    extChartAt 𝓘(ℝ, E) (A.center i) '' A.dom i = A.image i := by
  ext y
  rw [image_congr fun x _ ↦ extChartAt_model_apply_eq_chartAt_apply x]
  exact A.mem_image.symm

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [VectorBundle ℝ F V] in
/-- The chart domains of `A` lie in the first-jet chart domains at their centres. -/
private theorem dom_subset_baseSet (i : Fin A.n) :
    A.dom i ⊆ FirstJetBundle.baseSet (H := E) F V (A.center i) := fun _ hx ↦
  (FirstJetBundle.mem_baseSet_iff F V).2 ⟨A.dom_subset_baseSet i hx, A.dom_subset_chart_source i hx⟩

section Readings

variable [IsManifold 𝓘(ℝ, E) 1 M]

/-- **Sobolev sections are locally integrable.** A section whose readings in the charts of `A` are
almost everywhere the chart data of an element of `W^{k,p}(V)` is locally integrable: its readings
in every preferred chart are locally integrable where they are defined. -/
theorem locallyIntegrableSection {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    LocallyIntegrableSection 𝓘(ℝ, E) F s := by
  refine (locallyIntegrableSection_iff_of_iUnion_eq_univ 𝓘(ℝ, E) F A.center A.dom A.isOpen_dom
    dom_subset_baseSet A.iUnion_dom μ).2 fun i ↦ ?_
  rw [localRep_center, image_extChartAt_center]
  exact (Lp.locallyIntegrableOn _ Fact.out).congr (hs i)

/-- Two sections whose readings in the charts of `A` are almost everywhere the chart data of the
same element of `W^{k,p}(V)` have readings agreeing almost everywhere in every preferred chart. -/
private theorem localRep_ae_eq {w : SobolevSection A μ p k} {s t : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (ht : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i t)
    (α : M) :
    FirstJetBundle.localRep 𝓘(ℝ, E) F s α =ᵐ[(Module.finBasis ℝ E).addHaar.restrict
      ((extChartAt 𝓘(ℝ, E) α).target ∩
        (extChartAt 𝓘(ℝ, E) α).symm ⁻¹' (trivializationAt F V α).baseSet)]
      FirstJetBundle.localRep 𝓘(ℝ, E) F t α :=
  localRep_ae_eq_of_iUnion_eq_univ 𝓘(ℝ, E) F A.center A.dom A.isOpen_dom dom_subset_baseSet
    A.iUnion_dom μ (fun i ↦ by
      rw [localRep_center, localRep_center, image_extChartAt_center]
      exact (hs i).symm.trans (ht i)) α

end Readings

variable [IsManifold 𝓘(ℝ, E) ∞ M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] [T2Space M]

/-- Sections with the chart data of the same element of `W^{k,p}(V)` have the same distributional
section. -/
private theorem ofSection_eq [SigmaCompactSpace M] {w : SobolevSection A μ p k} {s t : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (ht : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i t) :
    BundleDistribution.ofSection 𝓘(ℝ, E) F s = BundleDistribution.ofSection 𝓘(ℝ, E) F t :=
  BundleDistribution.ofSection_congr_ae (localRep_ae_eq hs ht)

variable (A μ p k) in
/-- **The distributional section of a Sobolev section**: an element `w` of `W^{k,p}(V)` acts on the
tests `φ` of the dual-density bundle `V →L |Λ|` by integrating the density `x ↦ φ x (s x)`, for a
section `s` whose readings in the charts of `A` are the chart data of `w`
(`TauCeti.SobolevSection.toBundleDistribution_apply`). It is `TauCeti.BundleDistribution.ofSection`
of any such `s` (`TauCeti.SobolevSection.toBundleDistribution_eq_ofSection`). -/
def toBundleDistribution : SobolevSection A μ p k →ₗ[ℝ] BundleDistribution 𝓘(ℝ, E) M F V :=
  have := A.compactSpace
  { toFun w := BundleDistribution.ofSection 𝓘(ℝ, E) F (exists_ae_eq_coord w).choose
    map_add' w w' := by
      have hw := (exists_ae_eq_coord w).choose_spec
      have hw' := (exists_ae_eq_coord w').choose_spec
      rw [← BundleDistribution.ofSection_add (locallyIntegrableSection hw)
        (locallyIntegrableSection hw')]
      exact ofSection_eq (exists_ae_eq_coord (w + w')).choose_spec
        fun i ↦ chartValueL_add_ae_coord (hw i) (hw' i)
    map_smul' c w := by
      have hw := (exists_ae_eq_coord w).choose_spec
      rw [RingHom.id_apply, ← BundleDistribution.ofSection_smul]
      exact ofSection_eq (exists_ae_eq_coord (c • w)).choose_spec
        fun i ↦ chartValueL_smul_ae_coord c (hw i) }

/-- `TauCeti.SobolevSection.toBundleDistribution` is `TauCeti.BundleDistribution.ofSection` of any
section whose readings in the charts of `A` are the chart data. -/
theorem toBundleDistribution_eq_ofSection [SigmaCompactSpace M] {w : SobolevSection A μ p k}
    {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    toBundleDistribution A μ p k w = BundleDistribution.ofSection 𝓘(ℝ, E) F s :=
  -- `toBundleDistribution A μ p k w` is the distributional section of the chosen section of `w`.
  ofSection_eq (exists_ae_eq_coord w).choose_spec hs

/-- An element of `W^{k,p}(V)` acts on a test `φ` of the dual-density bundle by integrating the
density `x ↦ φ x (s x)`, for any section `s` whose readings in the charts of `A` are its chart
data. -/
theorem toBundleDistribution_apply {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (φ : DualDensityTest 𝓘(ℝ, E) M F V) :
    toBundleDistribution A μ p k w φ = integralDensity fun x ↦ φ x (s x) := by
  have := A.compactSpace
  rw [toBundleDistribution_eq_ofSection hs,
    BundleDistribution.ofSection_apply (locallyIntegrableSection hs)]

end SobolevSection

end TauCeti
