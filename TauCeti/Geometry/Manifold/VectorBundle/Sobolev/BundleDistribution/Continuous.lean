/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.BundleDistribution
import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.LocalRep
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartCutoffs
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Continuity of the evaluations of Sobolev sections as distributional sections

Let `A` be a finite bundle atlas of a smooth vector bundle `V → M` over a smooth Hausdorff manifold
without boundary modelled on a finite-dimensional real inner product space `E`, and let
`TauCeti.SobolevSection.toBundleDistribution` send an element `w` of `W^{k,p}(V)` to the
distributional section of a section whose chart data are those of `w`. For each test `φ` of the
dual-density bundle `V →L |Λ|`, the evaluation `w ↦ toBundleDistribution w φ` is continuous
(`TauCeti.SobolevSection.continuous_toBundleDistribution_apply`).

A smooth partition of unity subordinate to the chart domains `A.dom i` gives chart cutoffs whose
charts are the preferred charts at the centres `A.center i`, restricted to the base sets of the
dual-density bundle and to `A.dom i` (`TauCeti.ChartCutoffs`). Every test is the sum of the
extensions of its localizations `ψᵢ` along these cutoffs
(`TauCeti.ChartCutoffs.sum_chartTestCLM_localize`), and the distributional section pairs each
extension with `w` as `∫ ψᵢ (y) (s read at y)` over the chart image `A.image i`
(`TauCeti.integralDensity_chartTestCLM`), where the reading is the chart data of `w`. Up to the
constant relating the Haar measure of the fixed basis to `μ`, this is the pairing of the chart data
`TauCeti.SectionChartData.chartValueL`, a continuous linear map to `Lᵖ`, with the class of `ψᵢ` in
the conjugate `L^q` (Mathlib's `ContinuousLinearMap.lpPairing`).

This is the test-by-test continuity used by the closed graph theorem to identify `W^{k,2}(V)` with
the Sobolev space of a square chart partition.

## Main results

* `TauCeti.SobolevSection.continuous_toBundleDistribution_apply`: each evaluation of the
  distributional section is continuous on `W^{k,p}(V)`.
-/

public section

noncomputable section

open Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal NNReal Distributions

namespace TauCeti

namespace SobolevSection

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  {A : FiniteBundleAtlas E M F V} {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {k : ℕ}

-- The preferred trivialization of the dual-density bundle at the centre of chart `i` of `A`.
local macro "𝒯" i:term:max : term =>
  `(trivializationAt ($(Lean.mkIdent `F) →L[ℝ] ℝ)
    (fun x ↦ $(Lean.mkIdent `V) x →L[ℝ] DensityBundle 𝓘(ℝ, $(Lean.mkIdent `E)) $(Lean.mkIdent `M) x)
    (FiniteBundleAtlas.center $(Lean.mkIdent `A) $i))

-- The chart `baseSetChart` at the centre of chart `i` of `A`, for the dual-density bundle,
-- restricted to the domain of chart `i`.
local macro "𝒸" i:term:max : term =>
  `((baseSetChart ($(Lean.mkIdent `F) →L[ℝ] ℝ) 𝓘(ℝ, $(Lean.mkIdent `E))
    (fun x ↦ $(Lean.mkIdent `V) x →L[ℝ] DensityBundle 𝓘(ℝ, $(Lean.mkIdent `E)) $(Lean.mkIdent `M) x)
    (FiniteBundleAtlas.center $(Lean.mkIdent `A) $i)).restrOpen
      (FiniteBundleAtlas.dom $(Lean.mkIdent `A) $i) (FiniteBundleAtlas.isOpen_dom _ $i))

omit [MeasurableSpace E] [BorelSpace E] [T2Space M] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] in
/-- The restricted chart at the centre of chart `i` has source `A.dom i` and image `A.image i`,
lies over the base set of the preferred frame of the dual-density bundle, and is the preferred
extended chart at the centre. -/
private theorem restrChart_props (i : Fin A.n) :
    (𝒸 i).source = A.dom i ∧ (𝒸 i).target = A.image i ∧ (𝒸 i).source ⊆ (𝒯 i).baseSet ∧
      ∀ x ∈ (𝒸 i).source, (𝒸 i) x = extChartAt 𝓘(ℝ, E) (A.center i) x := by
  have hdom : A.dom i ⊆ (baseSetChart (F →L[ℝ] ℝ) 𝓘(ℝ, E)
      (fun x ↦ V x →L[ℝ] DensityBundle 𝓘(ℝ, E) M x) (A.center i)).source := fun x hx ↦ by
    rw [baseSetChart_source, hom_trivializationAt_baseSet, TauCeti.Density.trivializationAt_eq,
      Trivialization.density_baseSet, TangentBundle.trivializationAt_baseSet]
    exact ⟨A.dom_subset_chart_source i hx, A.dom_subset_baseSet i hx,
      A.dom_subset_chart_source i hx⟩
  have hsrc : (𝒸 i).source = A.dom i := by
    rw [OpenPartialHomeomorph.restrOpen_source, inter_eq_right.2 hdom]
  refine ⟨hsrc, ?_, by rw [hsrc]; exact hdom.trans (baseSetChart_source_subset _ _),
    fun x _ ↦ ?_⟩
  · rw [← (𝒸 i).image_source_eq_target, hsrc, OpenPartialHomeomorph.coe_restrOpen,
      coe_baseSetChart, A.image_extChartAt_center (𝕜 := ℝ)]
  · rw [OpenPartialHomeomorph.coe_restrOpen, coe_baseSetChart]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] in
/-- Chart cutoffs along the restricted charts at the centres of the charts of `A`, from a smooth
partition of unity subordinate to the chart domains. -/
private theorem exists_chartCutoffs [SigmaCompactSpace M] :
    ∃ C : ChartCutoffs 𝓘(ℝ, E) M ⊤ (Fin A.n), ∀ i, C.chart i = 𝒸 i := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ A.dom
    A.isOpen_dom fun x _ ↦ by rw [A.iUnion_dom]; exact mem_univ x
  exact ⟨{
    chart := fun i ↦ 𝒸 i
    contMDiffOn_chart := fun i ↦ (contMDiffOn_baseSetChart _ _).mono fun x hx ↦ by
      rw [OpenPartialHomeomorph.restrOpen_source] at hx
      exact hx.1
    contMDiffOn_chart_symm := fun i ↦ (contMDiffOn_baseSetChart_symm _ _).mono fun y hy ↦ by
      have hz := (𝒸 i).map_target hy
      rw [← (𝒸 i).right_inv hy, OpenPartialHomeomorph.coe_restrOpen]
      rw [OpenPartialHomeomorph.restrOpen_source] at hz
      exact (baseSetChart _ _ _ _).map_source hz.1
    cutoff := fun i ↦ ⟨ρ i, (ρ i).contMDiff.of_le (WithTop.coe_le_coe.2 le_top)⟩
    tsupport_subset := fun i ↦ by rw [(restrChart_props i).1]; exact hρ i
    isCompact_tsupport := fun i ↦ (A.isCompact_closure_dom i).of_isClosed_subset
      (isClosed_tsupport _) ((hρ i).trans subset_closure)
    finite := fun _ _ ↦ toFinite _
    sum_eq_one := fun z ↦ ρ.sum_eq_one (mem_univ z) }, fun _ ↦ rfl⟩

/-- The pairing of chart data with a test function on the image of chart `i`, through the
evaluation `(F →L[ℝ] ℝ) × F → ℝ`, as a continuous linear functional of `W^{k,p}(V)`: Mathlib's
`ContinuousLinearMap.lpPairing` with the class of the test function in the conjugate `L^q`. -/
private def pairingCLM (i : Fin A.sectionChartData.n) {Ω : TopologicalSpace.Opens E}
    (ψ : 𝓓(Ω, F →L[ℝ] ℝ)) : SobolevSection A μ p k →L[ℝ] ℝ :=
  haveI : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  ((((ContinuousLinearMap.id ℝ (F →L[ℝ] ℝ)).flip.lpPairing
      (μ.restrict (A.sectionChartData.image i)) p p.conjExponent).flip
      (TestFunction.ambientToLp ℝ p.conjExponent (μ.restrict (A.sectionChartData.image i)) ψ)).comp
    (A.sectionChartData.chartValueL μ p k i)).comp (Submodule.subtypeL _)

omit [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] in
/-- `pairingCLM i ψ w` is the integral of `ψ` against the chart data of `w` over the image of
chart `i`. -/
private theorem pairingCLM_apply (i : Fin A.sectionChartData.n) {Ω : TopologicalSpace.Opens E}
    (ψ : 𝓓(Ω, F →L[ℝ] ℝ)) (w : SobolevSection A μ p k) :
    pairingCLM i ψ w =
      ∫ y in A.sectionChartData.image i, ψ y (A.sectionChartData.chartValueL μ p k i w y) ∂μ := by
  have : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le _ p⟩
  rw [pairingCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [TestFunction.coeFn_ambientToLp (𝕜 := ℝ) (p := p.conjExponent)
    (ν := μ.restrict (A.sectionChartData.image i)) ψ] with y hy
  rw [hy, ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply]

/-- Paired with the extension of a test function `ψ` through a restriction `c` of the preferred
chart at the centre of chart `i` with image `A.image i`, the distributional section of `w` is the
integral of `ψ` against the chart data of `w`, times the constant `c₀` relating the Haar measure of
the fixed basis to `μ`. -/
private theorem toBundleDistribution_chartTestCLM [SigmaCompactSpace M] (i : Fin A.n)
    (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ c c.source)
    (hct : c.source ⊆ (𝒯 i).baseSet)
    (hcα : ∀ x ∈ c.source, c x = extChartAt 𝓘(ℝ, E) (A.center i) x)
    (htgt : c.target = A.image i) (ψ : 𝓓(⟨c.target, c.open_target⟩, F →L[ℝ] ℝ)) (c₀ : ℝ≥0)
    (hc₀ : (Module.finBasis ℝ E).addHaar = c₀ • μ) (w : SobolevSection A μ p k) :
    toBundleDistribution A μ p k w ((𝒯 i).chartTestCLM c hc hct ψ) = c₀ *
        ∫ y in A.image i, ψ y (A.sectionChartData.chartValueL μ p k i w y) ∂μ := by
  obtain ⟨s, hs⟩ := exists_ae_eq_coord w
  have hsl := locallyIntegrableSection hs
  have hu : LocallyIntegrableOn (FirstJetBundle.localRep 𝓘(ℝ, E) F s (A.center i)) c.target
      (Module.finBasis ℝ E).addHaar := by
    rw [htgt, A.localRep_center]
    exact ((Lp.locallyIntegrableOn _ Fact.out).congr (hs i)).of_isAddHaarMeasure _
  rw [toBundleDistribution_eq_ofSection hs, BundleDistribution.ofSection_apply hsl,
    integralDensity_chartTestCLM c hc hct hcα hu ψ,
    TestFunction.integralAgainstBilinCLM_eq_integral hu,
    hc₀, integral_smul_nnreal_measure,
    NNReal.smul_def, smul_eq_mul,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := A.image i) fun y hy ↦ by
      rw [ψ.zero_on_compl fun h ↦ hy (htgt ▸ h), Pi.zero_apply,
        ContinuousLinearMap.id_apply, zero_apply]]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hs i] with y hy
  rw [A.localRep_center, ← hy, ContinuousLinearMap.id_apply]

/-- **Continuity of the evaluations.** For every test `φ` of the dual-density bundle, the
evaluation `w ↦ toBundleDistribution w φ` is continuous on `W^{k,p}(V)`. -/
theorem continuous_toBundleDistribution_apply (φ : DualDensityTest 𝓘(ℝ, E) M F V) :
    Continuous fun w : SobolevSection A μ p k ↦ toBundleDistribution A μ p k w φ := by
  have := A.compactSpace
  obtain ⟨C, hC⟩ := exists_chartCutoffs (A := A)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ≥0, (Module.finBasis ℝ E).addHaar = c₀ • μ :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (Module.finBasis ℝ E).addHaar μ⟩
  have ht (i : Fin A.n) : (C.chart i).source ⊆ (𝒯 i).baseSet := by
    rw [hC]
    exact (restrChart_props i).2.2.1
  rw [← C.sum_chartTestCLM_localize (fun i ↦ 𝒯 i) ht (BundleTest.isCompact_tsupport φ)
    subset_rfl]
  simp_rw [map_sum]
  refine continuous_finsetSum _ fun i _ ↦ ?_
  refine ((continuous_const (y := (c₀ : ℝ))).mul (pairingCLM (A := A) (μ := μ) (p := p) (k := k) i
    (C.localize (fun i ↦ 𝒯 i) ht i φ)).continuous).congr fun w ↦ ?_
  have hp := restrChart_props (A := A) i
  rw [← hC] at hp
  exact ((toBundleDistribution_chartTestCLM i (C.chart i) (C.contMDiffOn_chart i) (ht i)
    hp.2.2.2 hp.2.1 _ c₀ hc₀ w).trans (congrArg _ (pairingCLM_apply i _ w).symm)).symm

end SobolevSection

end TauCeti
