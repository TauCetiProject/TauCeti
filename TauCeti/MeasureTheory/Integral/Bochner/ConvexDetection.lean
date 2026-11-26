/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp

/-!
# Detecting convex constraints by set averages

An integrable function takes values almost everywhere in a closed convex set if all of its
averages over measurable sets of finite positive measure belong to that set. For a semifinite
measure this holds for every closed convex set. For arbitrary measures the set must contain
zero: an integrable function vanishes outside a sigma-finite support, but averages cannot
detect values on a purely infinite part of the measure.

The finite-measure argument uses Mathlib's countable half-space representation on the closed
separable span of a strongly measurable representative. Scalar set-integral inequalities then
give a single exceptional null set. Localization supplies the general measure statements.

## References

* Hytönen, van Neerven, Veraar and Weis, *Analysis in Banach Spaces*, Volume I,
  Propositions 1.2.13–1.2.14.
-/

public section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal

namespace TauCeti

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} {f : α → E} {C : Set E}

private theorem ae_mem_of_set_averages_separable [SeparableSpace E] [IsFiniteMeasure μ]
    (hf : Integrable f μ) (hC : Convex ℝ C) (hCc : IsClosed C)
    (hav : ∀ s, MeasurableSet s → μ s ≠ 0 → μ s < ∞ → (⨍ x in s, f x ∂μ) ∈ C) :
    ∀ᵐ x ∂μ, f x ∈ C := by
  obtain ⟨l, c, hrep⟩ := RCLike.iInter_countable_halfSpaces_eq (𝕜 := ℝ) hC hCc
  have htest : ∀ n, ∀ᵐ x ∂μ, l n (f x) ≤ c n := by
    intro n
    refine ae_le_of_forall_setIntegral_le ((l n).integrable_comp hf)
      (integrable_const _) fun s hs hfin ↦ ?_
    by_cases hzero : μ s = 0
    · simp [Measure.restrict_eq_zero.mpr hzero]
    have hmem := hav s hs hzero hfin
    rw [← hrep, mem_iInter] at hmem
    have hn := hmem n
    simp only [mem_ofPred_eq, RCLike.re_to_real, setAverage_eq, map_smul,
      smul_eq_mul] at hn
    rw [← (l n).integral_comp_comm hf.integrableOn] at hn
    rw [setIntegral_const, smul_eq_mul]
    exact (inv_mul_le_iff₀ (ENNReal.toReal_pos hzero hfin.ne)).mp hn
  filter_upwards [ae_all_iff.mpr htest] with x hx
  rw [← hrep, mem_iInter]
  simpa using hx

private theorem ae_mem_of_set_averages_finite [IsFiniteMeasure μ]
    (hf : Integrable f μ) (hC : Convex ℝ C) (hCc : IsClosed C)
    (hav : ∀ s, MeasurableSet s → μ s ≠ 0 → μ s < ∞ → (⨍ x in s, f x ∂μ) ∈ C) :
    ∀ᵐ x ∂μ, f x ∈ C := by
  let g := hf.aestronglyMeasurable.mk f
  have hgm := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hfg := hf.aestronglyMeasurable.ae_eq_mk
  let S := (Submodule.span ℝ (range g)).topologicalClosure
  have : SeparableSpace S := hgm.isSeparable_range.span.closure.separableSpace
  have : CompleteSpace S :=
    (Submodule.span ℝ (range g)).isClosed_topologicalClosure.completeSpace_coe
  let gS : α → S := fun x ↦ ⟨g x, (Submodule.span ℝ (range g)).le_topologicalClosure
    (Submodule.subset_span (mem_range_self x))⟩
  have hgS : StronglyMeasurable gS :=
    (Embedding.comp_stronglyMeasurable_iff Topology.IsEmbedding.subtypeVal).mp hgm
  have hgSi : Integrable gS μ := (hf.congr hfg).norm.mono' hgS.aestronglyMeasurable
    (Eventually.of_forall fun _ ↦ le_rfl)
  have havS : ∀ s, MeasurableSet s → μ s ≠ 0 → μ s < ∞ →
      (⨍ x in s, gS x ∂μ) ∈ S.subtype ⁻¹' C := by
    intro s hs hzero hfin
    have heq : S.subtypeL (⨍ x in s, gS x ∂μ) = ⨍ x in s, g x ∂μ := by
      simp only [setAverage_eq, map_smul]
      rw [← S.subtypeL.integral_comp_comm hgSi.integrableOn]
      simp only [gS, Submodule.subtypeL_apply]
    have hgav := hav s hs hzero hfin
    rw [average_congr (ae_restrict_of_ae hfg)] at hgav
    rw [mem_preimage]
    exact heq.symm ▸ hgav
  have hS := ae_mem_of_set_averages_separable hgSi (hC.linear_preimage S.subtype)
    (hCc.preimage S.subtypeL.continuous) havS
  filter_upwards [hS, hfg] with x hx hfx
  exact hfx ▸ hx

private theorem ae_mem_of_set_averages_restrict
    (hf : Integrable f μ) (hC : Convex ℝ C) (hCc : IsClosed C)
    (hav : ∀ s, MeasurableSet s → μ s ≠ 0 → μ s < ∞ → (⨍ x in s, f x ∂μ) ∈ C)
    {t : Set α} (ht : MeasurableSet t) (hfin : μ t < ∞) :
    ∀ᵐ x ∂μ.restrict t, f x ∈ C := by
  have : IsFiniteMeasure (μ.restrict t) := ⟨by simpa using hfin⟩
  refine ae_mem_of_set_averages_finite hf.integrableOn hC hCc fun s hs hzero hsfin ↦ ?_
  rw [Measure.restrict_apply hs] at hzero hsfin
  rw [Measure.restrict_restrict hs]
  exact hav (s ∩ t) (hs.inter ht) hzero hsfin

/-- On a semifinite measure space, averages on all measurable sets of finite positive measure
detect membership in a closed convex set. Semifiniteness is stated explicitly as the existence
of a measurable subset of finite positive measure in every measurable nonnull set. -/
theorem ae_mem_of_set_averages
    (hμ : ∀ s, MeasurableSet s → μ s ≠ 0 →
      ∃ t ⊆ s, MeasurableSet t ∧ μ t ≠ 0 ∧ μ t < ∞)
    (hf : Integrable f μ) (hC : Convex ℝ C) (hCc : IsClosed C)
    (hav : ∀ s, MeasurableSet s → μ s ≠ 0 → μ s < ∞ → (⨍ x in s, f x ∂μ) ∈ C) :
    ∀ᵐ x ∂μ, f x ∈ C := by
  borelize E
  let g := hf.aestronglyMeasurable.mk f
  have hgm := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hfg := hf.aestronglyMeasurable.ae_eq_mk
  suffices hg : ∀ᵐ x ∂μ, g x ∈ C by
    filter_upwards [hg, hfg] with x hx hfx using hfx ▸ hx
  rw [ae_iff]
  by_contra hbad
  have hB : MeasurableSet {x | g x ∉ C} := hCc.measurableSet.compl.preimage hgm.measurable
  obtain ⟨t, htB, ht, htzero, htfin⟩ := hμ _ hB hbad
  have hgood := ae_mem_of_set_averages_restrict hf hC hCc hav ht htfin
  have hfalse : ∀ᵐ _ ∂μ.restrict t, False := by
    filter_upwards [hgood, ae_restrict_of_ae hfg, ae_restrict_mem ht] with _ hx hfx hxt
    exact htB hxt (by simpa only [g, ← hfx] using hx)
  exact htzero (by simpa using hfalse)

/-- For an arbitrary measure, set averages detect a closed convex constraint containing zero.
The zero condition handles the complement of the integrable function's sigma-finite support. -/
theorem ae_mem_of_set_averages_of_zero_mem
    (hf : Integrable f μ) (hC : Convex ℝ C) (hCc : IsClosed C) (hzero : (0 : E) ∈ C)
    (hav : ∀ s, MeasurableSet s → μ s ≠ 0 → μ s < ∞ → (⨍ x in s, f x ∂μ) ∈ C) :
    ∀ᵐ x ∂μ, f x ∈ C := by
  let hfm := hf.aefinStronglyMeasurable
  have : SigmaFinite (μ.restrict hfm.sigmaFiniteSet) := hfm.sigmaFinite_restrict
  refine ae_of_ae_restrict_of_ae_restrict_compl hfm.sigmaFiniteSet ?_ ?_
  · refine ae_of_forall_measure_lt_top_ae_restrict _ fun s hs hsfin ↦ ?_
    rw [Measure.restrict_apply hs] at hsfin
    rw [Measure.restrict_restrict hs]
    exact ae_mem_of_set_averages_restrict hf hC hCc hav (hs.inter hfm.measurableSet) hsfin
  · filter_upwards [hfm.ae_eq_zero_compl] with x hx
    simpa only [hx, Pi.zero_apply] using hzero

end TauCeti

/-- If all finite-measure set integrals of an integrable function belong to a closed submodule,
then its values belong to that submodule almost everywhere, for an arbitrary measure. -/
theorem Submodule.ae_mem_of_setIntegral_mem
    {𝕜 α E : Type*} [RCLike 𝕜] [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [IsScalarTower ℝ 𝕜 E] [CompleteSpace E]
    (S : Submodule 𝕜 E) (hS : IsClosed (S : Set E))
    {μ : Measure α} {f : α → E} (hf : Integrable f μ)
    (hint : ∀ s, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) ∈ S) :
    ∀ᵐ x ∂μ, f x ∈ S := by
  refine TauCeti.ae_mem_of_set_averages_of_zero_mem hf (S.restrictScalars ℝ).convex hS
    S.zero_mem
    fun s hs _ hfin ↦ ?_
  rw [setAverage_eq]
  exact (S.restrictScalars ℝ).smul_mem _ (hint s hs hfin)
