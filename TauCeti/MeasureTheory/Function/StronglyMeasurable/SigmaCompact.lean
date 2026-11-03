/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Compactness.SigmaCompact
import TauCeti.MeasureTheory.Measure.Regular

/-!
# σ-compact supports of functions with σ-finite support

Let `μ` be a measure on a Hausdorff space that is inner regular for compact sets on sets of finite
measure, such as a regular measure (`MeasureTheory.Measure.Regular`). No σ-finiteness of `μ` is
assumed. A function that is almost everywhere finitely strongly measurable, in particular an
integrable function (`MeasureTheory.Integrable.aefinStronglyMeasurable`) or a function in `Lᵖ`
with `0 < p < ∞` (`MeasureTheory.MemLp.aefinStronglyMeasurable`), vanishes almost everywhere
outside a σ-compact set. This sharpens Mathlib's
`MeasureTheory.AEFinStronglyMeasurable.exists_set_sigmaFinite`, which provides a measurable set
with σ-finite restriction outside which the function vanishes. Since countable unions of σ-compact
sets are σ-compact, countably many such functions vanish outside one σ-compact set.

When `μ` is also finite on compact sets, its restriction to a σ-compact set is σ-finite
(`IsSigmaCompact.sigmaFinite_restrict`). An argument about countably many integrable functions for
a measure that is not σ-finite, such as a regular Haar measure on a locally compact group that is
not σ-compact, can therefore take place inside a σ-compact set, where Fubini's theorem applies.

## Main results

* `MeasureTheory.AEFinStronglyMeasurable.exists_isSigmaCompact`: an almost everywhere finitely
  strongly measurable function vanishes almost everywhere outside a σ-compact set.
* `MeasureTheory.exists_isSigmaCompact_forall_ae_eq_zero`: countably many such functions vanish
  almost everywhere outside a single σ-compact set.
-/

public section

open Set Filter

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
  [T2Space α] {μ : Measure α} [μ.InnerRegularCompactLTTop] [Zero β] [TopologicalSpace β] [T2Space β]

/-- **Finitely strongly measurable functions have σ-compact support.** For a measure that is inner
regular for compact sets on sets of finite measure, an almost everywhere finitely strongly
measurable function vanishes almost everywhere outside some σ-compact set. -/
theorem AEFinStronglyMeasurable.exists_isSigmaCompact {f : α → β}
    (hf : AEFinStronglyMeasurable f μ) : ∃ t, IsSigmaCompact t ∧ f =ᵐ[μ.restrict tᶜ] 0 := by
  obtain ⟨s, hs, hfs, hσ⟩ := hf.exists_set_sigmaFinite
  obtain ⟨t, -, ht, hst⟩ :=
    (hs.nullMeasurableSet (μ := μ.restrict s)).exists_isSigmaCompact_subset_ae_eq
  refine ⟨t, ht, ?_⟩
  -- Outside `t`, either we are outside `s`, where `f` vanishes, or in the null set `s \ t`.
  have hnull : μ (s \ t) = 0 := by
    simpa [Measure.restrict_apply' hs, inter_eq_left.2 sdiff_subset] using (ae_eq_set.1 hst).2
  refine ae_restrict_of_ae_restrict_of_subset (t := sᶜ ∪ s \ t)
    (fun x hx ↦ (em (x ∈ s)).symm.imp id fun hxs ↦ ⟨hxs, hx⟩) ?_
  refine (ae_restrict_union_iff _ _ _).2 ⟨hfs, ?_⟩
  rw [Measure.restrict_eq_zero.2 hnull, ae_zero]
  exact eventually_bot

/-- **Countably many functions have a common σ-compact support.** For a measure that is inner
regular for compact sets on sets of finite measure, countably many almost everywhere finitely
strongly measurable functions vanish almost everywhere outside a single σ-compact set. -/
theorem exists_isSigmaCompact_forall_ae_eq_zero {ι : Type*} [Countable ι] {f : ι → α → β}
    (hf : ∀ i, AEFinStronglyMeasurable (f i) μ) :
    ∃ t, IsSigmaCompact t ∧ ∀ i, f i =ᵐ[μ.restrict tᶜ] 0 := by
  choose t ht hft using fun i ↦ (hf i).exists_isSigmaCompact
  exact ⟨⋃ i, t i, isSigmaCompact_iUnion t ht, fun i ↦
    ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.2 (subset_iUnion t i)) (hft i)⟩

end MeasureTheory
