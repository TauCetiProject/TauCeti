/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.OfSection
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.BesselPotential
import TauCeti.Analysis.Distribution.OfFun
import TauCeti.Analysis.Sobolev.BesselPotential.NormEquivalence.Local
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.LocalRep
import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.OfSection.ChartComponent
import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalSobolev
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

The map is injective (`TauCeti.SobolevSection.toBundleDistribution_injective`), and for `p = 2` and
`μ = volume` its image consists of functionals that are `H^k` with respect to every square chart
partition of the dual-density bundle (`TauCeti.SobolevSection.memSobolev_toBundleDistribution`).
Both are read off in the chart `baseSetChart` at the centre of each chart of `A` and the preferred
frame of the dual-density bundle: there the component of the distributional section along a covector
`v` is the regular distribution of `v` applied to the chart data
(`TauCeti.chartComponent_ofSection`), for the Haar measure of the fixed basis of `E`, a constant
multiple of `volume`. Injectivity follows from Mathlib's `Distribution.ofFun_injective`. For `H^k`,
the chart data are `W^{k,2}` on the chart image, so the component is locally `H^k` there
(`Distribution.isLocallySobolevAt_ofFun_iff_exists_wkp`), and `H^k` regularity with respect to a
square chart partition is local
(`TauCeti.SquareChartPartition.memSobolev_iff_forall_isLocallySobolevAt`,
`TauCeti.BundleTest.isLocallySobolevAt_iff`).

## Main declarations

* `TauCeti.SobolevSection.locallyIntegrableSection`: the sections of elements of `W^{k,p}(V)` are
  locally integrable.
* `TauCeti.SobolevSection.toBundleDistribution`: the linear map from `W^{k,p}(V)` to the
  distributional sections of `V`, with `TauCeti.SobolevSection.toBundleDistribution_apply` and
  `TauCeti.SobolevSection.toBundleDistribution_eq_ofSection`.
* `TauCeti.SobolevSection.toBundleDistribution_injective`: injectivity.
* `TauCeti.SobolevSection.memSobolev_toBundleDistribution`: for `μ = volume`, the distributional
  sections of elements of `W^{k,2}(V)` are `H^k` with respect to every square chart partition of
  `V →L |Λ|`.
* `TauCeti.SobolevSection.exists_wkp_comp_coord`: a covector applied to the chart data of an
  element of `W^{k,p}(V)` is `W^{k,p}` on the chart image.

## References

* J. J. Duistermaat, J. A. C. Kolk, *Distributions: Theory and Applications*, Birkhäuser, 2010,
  §§16, 19 (distributional sections of vector bundles).
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3.
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

section Readings

variable [IsManifold 𝓘(ℝ, E) 1 M]

/-- **Sobolev sections are locally integrable.** A section whose readings in the charts of `A` are
almost everywhere the chart data of an element of `W^{k,p}(V)` is locally integrable: its readings
in every preferred chart are locally integrable where they are defined. -/
theorem locallyIntegrableSection {w : SobolevSection A μ p k} {s : ∀ x, V x}
    (hs : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    LocallyIntegrableSection 𝓘(ℝ, E) F s := by
  refine (locallyIntegrableSection_iff_of_iUnion_eq_univ 𝓘(ℝ, E) F A.center A.dom A.isOpen_dom
    A.dom_subset_firstJetBaseSet A.iUnion_dom μ).2 fun i ↦ ?_
  rw [A.localRep_center, A.image_extChartAt_center]
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
  localRep_ae_eq_of_iUnion_eq_univ 𝓘(ℝ, E) F A.center A.dom A.isOpen_dom
    A.dom_subset_firstJetBaseSet
    A.iUnion_dom μ (fun i ↦ by
      rw [A.localRep_center, A.localRep_center, A.image_extChartAt_center]
      exact (hs i).symm.trans (ht i)) α

omit [IsManifold 𝓘(ℝ, E) 1 M] in
/-- A covector `v` applied to the chart data of an element of `W^{k,p}(V)` is the value of a
`W^{k,p}` function on the chart image: the combination `∑ₐ v(bₐ) wᵢₐ` of its components. -/
theorem exists_wkp_comp_coord {w : SobolevSection A μ p k} {s : ∀ x, V x} {i : Fin A.n}
    (hs : A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (v : F →L[ℝ] ℝ) :
    ∃ u : Wkp μ (A.image i) p k,
      (Wkp.value k u : E → ℝ) =ᵐ[μ.restrict (A.image i)] fun y ↦ v (A.coord i s y) := by
  refine ⟨∑ a, v (Module.finBasis ℝ F a) • (w : A.sectionChartData.SobolevData μ p k) i a, ?_⟩
  have hsmul (a : Fin (Module.finrank ℝ F)) := Lp.coeFn_smul (v (Module.finBasis ℝ F a))
    (Wkp.value k ((w : A.sectionChartData.SobolevData μ p k) i a))
  filter_upwards [Wkp.value_finsetSum_ae k Finset.univ fun a ↦
      v (Module.finBasis ℝ F a) • (w : A.sectionChartData.SobolevData μ p k) i a,
    ae_all_iff.2 hsmul, A.sectionChartData.chartValueL_apply_ae μ p k i w, hs]
    with y h1 h2 h3 h4
  refine h1.trans ?_
  rw [← h4, h3, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Wkp.value_smul, h2 a, Pi.smul_apply, smul_eq_mul, map_smul, smul_eq_mul, mul_comm]

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

/-! ### Injectivity and Sobolev regularity of the distributional section -/

variable (A) in
/-- The chart `baseSetChart` of the dual-density bundle at the centre of chart `i` of `A`. -/
private abbrev centreChart (i : Fin A.n) : OpenPartialHomeomorph M E :=
  baseSetChart (F →L[ℝ] ℝ) 𝓘(ℝ, E) (fun x ↦ V x →L[ℝ] DensityBundle 𝓘(ℝ, E) M x) (A.center i)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] [T2Space M] in
/-- The chart domains of `A` lie in the sources of the charts `baseSetChart` at their centres for
the dual-density bundle. -/
private theorem dom_subset_baseSetChart_source (i : Fin A.n) : A.dom i ⊆ (centreChart A i).source :=
  fun x hx ↦ by
    rw [baseSetChart_source, hom_trivializationAt_baseSet, TauCeti.Density.trivializationAt_eq,
      Trivialization.density_baseSet, TangentBundle.trivializationAt_baseSet]
    exact ⟨A.dom_subset_chart_source i hx, A.dom_subset_baseSet i hx,
      A.dom_subset_chart_source i hx⟩

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] [T2Space M] in
/-- The image of the domain of chart `i` in the chart `baseSetChart` at its centre is the chart
image, which therefore lies in the target of `baseSetChart`. -/
private theorem image_baseSetChart_dom (i : Fin A.n) :
    (centreChart A i) '' A.dom i = A.image i ∧ (A.image i : Set E) ⊆ (centreChart A i).target := by
  have h : (centreChart A i) '' A.dom i = A.image i := by
    rw [← A.image_extChartAt_center (𝕜 := ℝ), coe_baseSetChart]
  exact ⟨h, h ▸ image_subset_iff.2 fun z hz ↦
    (centreChart A i).map_source (dom_subset_baseSetChart_source i hz)⟩

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] [T2Space M] in
/-- The chart `baseSetChart` at the centre of chart `i` is the preferred extended chart there. -/
private theorem baseSetChart_eq_extChartAt (i : Fin A.n) :
    ∀ x ∈ (centreChart A i).source, (centreChart A i) x = extChartAt 𝓘(ℝ, E) (A.center i) x :=
  fun _ _ ↦ by
  rw [coe_baseSetChart]

omit [FiniteDimensional ℝ F] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] [T2Space M] in
/-- The reading at the centre of chart `i` of a locally integrable section is locally integrable on
the target of the chart `baseSetChart` there. -/
private theorem locallyIntegrableOn_localRep_center {s : ∀ x, V x}
    (hs : LocallyIntegrableSection 𝓘(ℝ, E) F s) (i : Fin A.n) :
    LocallyIntegrableOn (FirstJetBundle.localRep 𝓘(ℝ, E) F s (A.center i)) (centreChart A i).target
      (Module.finBasis ℝ E).addHaar :=
  hs.locallyIntegrableOn_target (centreChart A i) (baseSetChart_source_subset _ _)
    (baseSetChart_eq_extChartAt i)

/-- In the chart `baseSetChart` at the centre of chart `i` and the preferred frame of the
dual-density bundle, the component along `v` of the distributional section of a locally
integrable section is the regular distribution of `v` applied to its reading at the centre. -/
private theorem chartComponent_center [SigmaCompactSpace M] {s : ∀ x, V x}
    (hs : LocallyIntegrableSection 𝓘(ℝ, E) F s) (i : Fin A.n) (v : F →L[ℝ] ℝ) :
    (trivializationAt (F →L[ℝ] ℝ) (fun x ↦ V x →L[ℝ] DensityBundle 𝓘(ℝ, E) M x)
        (A.center i)).chartComponent (centreChart A i) (contMDiffOn_baseSetChart _ _)
        (baseSetChart_source_subset _ _) (BundleDistribution.ofSection 𝓘(ℝ, E) F s) v =
      Distribution.ofFun ⟨(centreChart A i).target, (centreChart A i).open_target⟩
        (fun y ↦ (v (FirstJetBundle.localRep 𝓘(ℝ, E) F s (A.center i) y) : ℂ))
        (Module.finBasis ℝ E).addHaar ⊤ :=
  chartComponent_ofSection _ _ _ (baseSetChart_eq_extChartAt i) hs v

/-- **Injectivity.** An element of `W^{k,p}(V)` is determined by its distributional section. -/
theorem toBundleDistribution_injective : Function.Injective (toBundleDistribution A μ p k) := by
  have := A.compactSpace
  refine (injective_iff_map_eq_zero _).2 fun w hw ↦ ?_
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  have hsl := locallyIntegrableSection hs
  rw [toBundleDistribution_eq_ofSection hs] at hw
  have hac := Measure.absolutelyContinuous_isAddHaarMeasure μ (Module.finBasis ℝ E).addHaar
  have hz (i : Fin A.n) (j : Fin (Module.finrank ℝ F)) :
      ∀ᵐ y ∂μ.restrict (A.image i), (Module.finBasis ℝ F).coord j (A.coord i s y) = 0 := by
    set v := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord j)
    have hloc := (Complex.ofRealCLM.comp v).locallyIntegrableOn_comp
      (locallyIntegrableOn_localRep_center hsl i)
    have h := Distribution.ofFun_injective
      (Ω := ⟨(centreChart A i).target, (centreChart A i).open_target⟩) (f' := 0) hloc
      locallyIntegrableOn_zero ((chartComponent_center hsl i v).symm.trans (by
        rw [hw, Bundle.Trivialization.chartComponent_zero, Distribution.ofFun_zero]))
    filter_upwards [(hac.restrict _).ae_le
      (ae_restrict_of_ae_restrict_of_subset (image_baseSetChart_dom i).2 h)] with y hy
    rw [← A.localRep_center (𝕜 := ℝ)]
    simpa [v] using hy
  refine eq_of_ae_eq_coord (w' := 0) hs fun i ↦ ?_
  rw [ZeroMemClass.coe_zero, map_zero]
  -- The chart count `A.sectionChartData.n` of the section chart data is `A.n` by definition
  -- (`TauCeti.FiniteBundleAtlas.sectionChartData`), so `i` indexes a chart of `A`.
  filter_upwards [Lp.coeFn_zero F p _, ae_all_iff.2 (hz (show Fin A.n from i))] with y h0 hy
  refine h0.trans ?_
  rw [Pi.zero_apply, eq_comm]
  exact (Module.finBasis ℝ F).forall_coord_eq_zero_iff.1 hy

/-- **Sobolev sections are `H^k`.** For every square chart partition `B` of the dual-density bundle
`V →L |Λ|`, the distributional section of an element of `W^{k,2}(V)` is `H^k` with respect to `B`
(`TauCeti.SquareChartPartition.MemSobolev`). -/
theorem memSobolev_toBundleDistribution {κ : Type*} [Fintype κ]
    (B : SquareChartPartition κ 𝓘(ℝ, E) (F →L[ℝ] ℝ)
      (fun x ↦ V x →L[ℝ] DensityBundle 𝓘(ℝ, E) M x))
    (w : SobolevSection A volume 2 k) :
    B.MemSobolev k (toBundleDistribution A volume 2 k w) := by
  have := A.compactSpace
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  have hsl := locallyIntegrableSection hs
  rw [B.memSobolev_iff_forall_isLocallySobolevAt, toBundleDistribution_eq_ofSection hs]
  intro x
  obtain ⟨i, hi⟩ := A.exists_mem_dom x
  rw [BundleTest.isLocallySobolevAt_iff _ (contMDiffOn_baseSetChart _ _)
    (contMDiffOn_baseSetChart_symm _ _) (baseSetChart_source_subset _ _)
    (dom_subset_baseSetChart_source i hi)]
  intro v
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : NNReal, (Module.finBasis ℝ E).addHaar = (c₀ : ℝ≥0∞) • volume :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (Module.finBasis ℝ E).addHaar volume⟩
  set g : E → ℝ := fun y ↦ c₀ * v (FirstJetBundle.localRep 𝓘(ℝ, E) F s (A.center i) y)
  have hloc : LocallyIntegrableOn (fun y ↦ v (FirstJetBundle.localRep 𝓘(ℝ, E) F s (A.center i) y))
      (centreChart A i).target volume :=
    (v.locallyIntegrableOn_comp (locallyIntegrableOn_localRep_center hsl i)).of_isAddHaarMeasure
      volume
  rw [chartComponent_center hsl i v, hc₀,
    Distribution.ofFun_smul_measure (Ω := ⟨(centreChart A i).target, (centreChart A i).open_target⟩)
      (fun y ↦ (v (FirstJetBundle.localRep 𝓘(ℝ, E) F s (A.center i) y) : ℂ)) volume c₀,
    ← Distribution.ofFun_smul]
  have hg : ((c₀ : ℝ) • fun y ↦ (v (FirstJetBundle.localRep 𝓘(ℝ, E) F s (A.center i) y) : ℂ)) =
      fun y ↦ (g y : ℂ) := by
    funext y
    simp [g, Complex.real_smul]
  rw [hg, Distribution.isLocallySobolevAt_ofFun_iff_exists_wkp k (hloc.smul (c₀ : ℝ))]
  obtain ⟨u, hu⟩ := exists_wkp_comp_coord (hs i) ((c₀ : ℝ) • v)
  refine ⟨A.image i, by
    rw [← SetLike.mem_coe, ← (image_baseSetChart_dom i).1]
    exact mem_image_of_mem _ hi, (image_baseSetChart_dom i).2,
    u, ?_⟩
  filter_upwards [hu] with y hy
  rw [hy, smul_apply, smul_eq_mul]
  simp only [g, A.localRep_center]

end SobolevSection

end TauCeti
