/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Strong measurability and continuous maps on supporting subsets

Composition preserves strong measurability when the outer map is continuous only on a
subset containing the range. The subset need not be measurable or closed. For a.e. strong
measurability, containment of the range is required only almost everywhere.

The finite-support versions hold for arbitrary measures when the outer map preserves zero.
For sigma-finite measures the zero-preserving condition is unnecessary. These results allow
continuous operations on a supporting subspace without extending them continuously to the
ambient space.

The underlying formal ingredients are Mathlib's strong-measurability criteria for topological
embeddings and its sigma-finite-support characterization of finite strong measurability.

## References

* Hytönen, van Neerven, Veraar and Weis, *Analysis in Banach Spaces*, Volume I, §1.1,
  continuous composition on supporting subsets (with the correction to p. 7 in the errata).
-/

public section

open Filter MeasureTheory Set Topology TopologicalSpace

variable {α β γ : Type*} [MeasurableSpace α]

/-- A continuous map on a supporting subset preserves strong measurability. The supporting
subset need not be measurable or closed. -/
theorem ContinuousOn.comp_stronglyMeasurable [TopologicalSpace β] [PseudoMetrizableSpace β]
    [TopologicalSpace γ] {g : β → γ} {s : Set β} (hg : ContinuousOn g s)
    {f : α → β} (hf : StronglyMeasurable f) (hfs : ∀ a, f a ∈ s) :
    StronglyMeasurable (fun a ↦ g (f a)) := by
  have hsub : StronglyMeasurable (fun a ↦ (⟨f a, hfs a⟩ : s)) :=
    Embedding.comp_stronglyMeasurable_iff IsEmbedding.subtypeVal |>.mp hf
  exact hg.domRestrict.comp_stronglyMeasurable hsub

/-- Continuity on a supporting subset preserves a.e. strong measurability when the values
belong to that subset only almost everywhere. No measurability of the subset is assumed. -/
theorem ContinuousOn.comp_aestronglyMeasurable [TopologicalSpace β]
    [PseudoMetrizableSpace β] [TopologicalSpace γ] {g : β → γ} {s : Set β}
    (hg : ContinuousOn g s) {f : α → β} {μ : Measure α} (hf : AEStronglyMeasurable f μ)
    (hfs : ∀ᵐ a ∂μ, f a ∈ s) : AEStronglyMeasurable (fun a ↦ g (f a)) μ := by
  classical
  by_cases hs : s.Nonempty
  · let F (a : α) : s := if ha : f a ∈ s then ⟨f a, ha⟩ else ⟨hs.choose, hs.choose_spec⟩
    have hF : (fun a ↦ (F a : β)) =ᵐ[μ] f := by
      filter_upwards [hfs] with a ha
      simp [F, ha]
    have hFm : AEStronglyMeasurable F μ :=
      IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.mp (hf.congr hF.symm)
    refine (hg.domRestrict.comp_aestronglyMeasurable hFm).congr ?_
    exact hF.fun_comp g
  · have hμ : μ = 0 := by
      have : ∀ᵐ _ ∂μ, False := hfs.mono fun _ ha ↦ hs ⟨_, ha⟩
      simpa using this
    simp [hμ]

/-- A zero-preserving continuous map preserves finite strong measurability, without any
finiteness assumption on the measure or separation assumption on the target spaces. -/
theorem Continuous.comp_finStronglyMeasurable [TopologicalSpace β] [Zero β]
    [TopologicalSpace γ] [Zero γ] {g : β → γ} (hg : Continuous g)
    {f : α → β} {μ : Measure α} (hf : FinStronglyMeasurable f μ) (hg0 : g 0 = 0) :
    FinStronglyMeasurable (fun a ↦ g (f a)) μ := by
  refine ⟨fun n ↦ (hf.approx n).map g, fun n ↦ ?_,
    fun a ↦ (hg.tendsto _).comp (hf.tendsto_approx a)⟩
  exact SimpleFunc.FinMeasSupp.map (hf.fin_support_approx n) hg0

/-- A zero-preserving continuous map preserves a.e. finite strong measurability for an
arbitrary measure. -/
theorem Continuous.comp_aefinStronglyMeasurable [TopologicalSpace β] [Zero β]
    [TopologicalSpace γ] [Zero γ] {g : β → γ} (hg : Continuous g)
    {f : α → β} {μ : Measure α} (hf : AEFinStronglyMeasurable f μ) (hg0 : g 0 = 0) :
    AEFinStronglyMeasurable (fun a ↦ g (f a)) μ :=
  ⟨_, hg.comp_finStronglyMeasurable hf.finStronglyMeasurable_mk hg0,
    hf.ae_eq_mk.fun_comp g⟩

/-- A map continuous on a supporting subset and preserving zero preserves finite strong
measurability for arbitrary measures. -/
theorem ContinuousOn.comp_finStronglyMeasurable [TopologicalSpace β]
    [PseudoMetrizableSpace β] [T2Space β] [Zero β] [TopologicalSpace γ] [Zero γ]
    {g : β → γ} {s : Set β} (hg : ContinuousOn g s) {f : α → β} {μ : Measure α}
    (hf : FinStronglyMeasurable f μ) (hfs : ∀ a, f a ∈ s) (hg0 : g 0 = 0) :
    FinStronglyMeasurable (fun a ↦ g (f a)) μ := by
  obtain ⟨t, ht, hft, hσ⟩ := hf.exists_set_sigmaFinite
  have hcomp := hg.comp_stronglyMeasurable hf.stronglyMeasurable hfs
  exact hcomp.finStronglyMeasurable_of_set_sigmaFinite
    ht (fun a ha ↦ by rw [hft a ha, hg0]) hσ

/-- The a.e. finite-support transport theorem allows membership in the supporting subset
only almost everywhere. The outer map must preserve zero for arbitrary measures. -/
theorem ContinuousOn.comp_aefinStronglyMeasurable [TopologicalSpace β]
    [PseudoMetrizableSpace β] [T2Space β] [Zero β] [TopologicalSpace γ] [Zero γ]
    {g : β → γ} {s : Set β} (hg : ContinuousOn g s) {f : α → β} {μ : Measure α}
    (hf : AEFinStronglyMeasurable f μ) (hfs : ∀ᵐ a ∂μ, f a ∈ s) (hg0 : g 0 = 0) :
    AEFinStronglyMeasurable (fun a ↦ g (f a)) μ := by
  classical
  have hfa : AEStronglyMeasurable f μ :=
    ⟨_, hf.finStronglyMeasurable_mk.stronglyMeasurable, hf.ae_eq_mk⟩
  have hcomp := hg.comp_aestronglyMeasurable hfa hfs
  obtain ⟨t, ht, hft, hσ⟩ := hf.exists_set_sigmaFinite
  refine ⟨t.indicator (hcomp.mk _),
    (hcomp.stronglyMeasurable_mk.indicator ht).finStronglyMeasurable_of_set_sigmaFinite ht
      (fun a ha ↦ indicator_of_notMem ha _) hσ, ?_⟩
  have hz : ∀ᵐ a ∂μ, a ∉ t → f a = 0 := (ae_restrict_iff' ht.compl).mp hft
  filter_upwards [hcomp.ae_eq_mk, hz] with a he hz
  by_cases ha : a ∈ t
  · simpa [ha] using he
  · simp [ha, hz ha, hg0]
