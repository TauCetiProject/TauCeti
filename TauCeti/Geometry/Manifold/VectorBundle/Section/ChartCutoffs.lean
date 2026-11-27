/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmulLeft

/-!
# Bundle tests along chart cutoffs

Let `(cᵢ, ρᵢ)` be chart cutoffs on `M` (`TauCeti.ChartCutoffs`) and `tᵢ` trivializations of the
atlas whose base sets contain the chart sources. The *localization* of a bundle test `Φ` to the
chart `cᵢ` is the test function `(ρᵢ Φ) ∘ cᵢ⁻¹` on the chart target, read in `tᵢ`; it is a
continuous linear map for the test topologies (`TauCeti.ChartCutoffs.localize`). Extending it back
through the chart gives `ρᵢ Φ` (`TauCeti.ChartCutoffs.chartTestCLM_localize`), and a bundle test
supported in a compact set `K` is the sum of these extensions over the cutoffs meeting `K`
(`TauCeti.ChartCutoffs.sum_chartTestCLM_localize`).

## Main declarations

* `TauCeti.ChartCutoffs.localize`: the localization of bundle tests to a chart target.
* `TauCeti.ChartCutoffs.chartTestCLM_localize`: its chart extension is `ρᵢ Φ`.
* `TauCeti.ChartCutoffs.sum_smulLeftCLM`: the cutoffs meeting a compact set `K` decompose every
  bundle test supported in `K`.
* `TauCeti.ChartCutoffs.sum_chartTestCLM_localize`: a bundle test supported in `K` is the sum of
  the chart extensions of its localizations to the charts whose cutoffs meet `K`.
-/

public noncomputable section

open Bundle Set TopologicalSpace ContMDiffSection
open scoped ContDiff Manifold Distributions

namespace TauCeti.ChartCutoffs

open BundleTest (smulLeftCLM smulLeftCLM_apply)

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  {ι : Type*} (A : ChartCutoffs I M ⊤ ι)
  (t : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (t i)]
  (ht : ∀ i, (A.chart i).source ⊆ (t i).baseSet)

/-- The **localization** `Φ ↦ (ρᵢ Φ) ∘ cᵢ⁻¹` of bundle tests to the target of the chart `cᵢ`, read
in the trivialization `tᵢ`, for the cutoff `ρᵢ`. -/
def localize (i : ι) :
    BundleTest I F V →L[ℝ] 𝓓(⟨(A.chart i).target, (A.chart i).open_target⟩, F) :=
  TestFunction.ofSupportedInCLM ℝ (A.chartSupport_subset_target i) ∘L
    (t i).chartLocalizationCLM (A.chart i) (A.contMDiffOn_chart_symm i) (ht i) (A.cutoff i)
      (A.chartSupport i) (A.chartSupport_subset_target i) (A.mapsTo_chartSupport i)

/-- The localization of `Φ` is the chart localization of the underlying section of `Φ`. -/
theorem localize_apply (i : ι) (Φ : BundleTest I F V) :
    A.localize t ht i Φ = TestFunction.ofSupportedIn (A.chartSupport_subset_target i)
      ((t i).chartLocalization (A.chart i) (A.contMDiffOn_chart_symm i) (ht i) (A.cutoff i)
        (A.chartSupport i) (A.chartSupport_subset_target i) (A.mapsTo_chartSupport i)
        ((BundleTest.ofCompactlySupported I F V).symm Φ).val) := by
  rw [localize, ContinuousLinearMap.comp_apply, Bundle.Trivialization.chartLocalizationCLM_apply,
    TestFunction.coe_ofSupportedInCLM]

omit [LocallyCompactSpace E] in
/-- A cutoff not meeting a compact set `K` kills every bundle test supported in `K`. -/
theorem smulLeftCLM_eq_zero {K : Set M} {hK : IsCompact K} {i : ι} (hi : i ∉ A.meeting K hK)
    {Φ : BundleTest I F V} (hΦ : closure {x | Φ x ≠ 0} ⊆ K) : smulLeftCLM (A.cutoff i) Φ = 0 := by
  refine BundleTest.ext fun z ↦ ?_
  rw [smulLeftCLM_apply, BundleTest.zero_apply]
  by_cases hz : z ∈ closure {x | Φ x ≠ 0}
  · rw [A.cutoff_eq_zero hi (hΦ hz), zero_smul]
  · rw [Bundle.apply_eq_zero_of_notMem_closure hz, smul_zero]

omit [LocallyCompactSpace E] in
/-- The cutoffs meeting a compact set `K` decompose every bundle test supported in `K`. -/
theorem sum_smulLeftCLM {K : Set M} (hK : IsCompact K) {Φ : BundleTest I F V}
    (hΦ : closure {x | Φ x ≠ 0} ⊆ K) :
    ∑ i ∈ A.meeting K hK, smulLeftCLM (A.cutoff i) Φ = Φ := by
  refine BundleTest.ext fun z ↦ ?_
  rw [BundleTest.sum_apply]
  simp_rw [smulLeftCLM_apply, ← Finset.sum_smul]
  by_cases hz : z ∈ K
  · rw [A.sum_meeting_eq_one hK hz, one_smul]
  · rw [Bundle.apply_eq_zero_of_notMem_closure fun h ↦ hz (hΦ h), smul_zero]

variable [T2Space M]

/-- Extending the localization of `Φ` back through the chart gives `ρᵢ Φ`. -/
theorem chartTestCLM_localize (i : ι) (Φ : BundleTest I F V) :
    (t i).chartTestCLM (A.chart i) (A.contMDiffOn_chart i) (ht i) (A.localize t ht i Φ) =
      smulLeftCLM (A.cutoff i) Φ := by
  refine BundleTest.ext fun z ↦ ?_
  rw [Bundle.Trivialization.coe_chartTestCLM, localize_apply,
    Bundle.Trivialization.chartTestSection_chartLocalization _ _ _ _ _ _ _ _
      (A.contMDiffOn_chart i) (A.tsupport_subset i), ContMDiffSection.smul_apply,
    smulLeftCLM_apply]

/-- A localization to a chart whose cutoff does not meet a compact set `K` vanishes on the bundle
tests supported in `K`. -/
theorem localize_eq_zero {K : Set M} {hK : IsCompact K} {i : ι} (hi : i ∉ A.meeting K hK)
    {Φ : BundleTest I F V} (hΦ : closure {x | Φ x ≠ 0} ⊆ K) : A.localize t ht i Φ = 0 :=
  (t i).chartTestCLM_injective _ (A.contMDiffOn_chart i) (ht i) <| by
    rw [A.chartTestCLM_localize, A.smulLeftCLM_eq_zero hi hΦ, map_zero]

/-- A bundle test supported in a compact set `K` is the sum of the chart extensions of its
localizations to the charts whose cutoffs meet `K`. -/
theorem sum_chartTestCLM_localize {K : Set M} (hK : IsCompact K) {Φ : BundleTest I F V}
    (hΦ : closure {x | Φ x ≠ 0} ⊆ K) :
    ∑ i ∈ A.meeting K hK,
      (t i).chartTestCLM (A.chart i) (A.contMDiffOn_chart i) (ht i) (A.localize t ht i Φ) = Φ := by
  simp_rw [A.chartTestCLM_localize]
  exact A.sum_smulLeftCLM hK hΦ

end TauCeti.ChartCutoffs
