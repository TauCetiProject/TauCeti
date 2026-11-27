/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Almost everywhere finite strong measurability and sigma-finite support

Almost everywhere finite strong measurability is equivalent to almost everywhere strong
measurability together with vanishing off a measurable sigma-finite support. This criterion
separates the topological condition from the support condition, allowing each to be transported
independently under maps of the target.

Countably many almost everywhere finitely strongly measurable functions share one such support
(`AEFinStronglyMeasurable.exists_set_sigmaFinite_of_countable`).

The pointwise criterion is Mathlib's
`finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite`.
-/

public section

open Filter MeasureTheory Set

namespace TauCeti

/-- A function is a.e. finitely strongly measurable exactly when it is a.e. strongly measurable
and vanishes a.e. outside a measurable set on which the measure is sigma-finite. -/
theorem aefinStronglyMeasurable_iff_aestronglyMeasurable_and_exists_set_sigmaFinite
    {α E : Type*} [MeasurableSpace α] [TopologicalSpace E] [T2Space E] [Zero E]
    {μ : Measure α} {f : α → E} :
    AEFinStronglyMeasurable f μ ↔ AEStronglyMeasurable f μ ∧
      ∃ s, MeasurableSet s ∧ f =ᵐ[μ.restrict sᶜ] 0 ∧ SigmaFinite (μ.restrict s) := by
  refine ⟨fun hf ↦ ⟨?_, hf.exists_set_sigmaFinite⟩, ?_⟩
  · exact ⟨hf.mk f, hf.finStronglyMeasurable_mk.stronglyMeasurable, hf.ae_eq_mk⟩
  rintro ⟨hf, s, hs, hzero, hσ⟩
  refine ⟨s.indicator (hf.mk f),
    (hf.stronglyMeasurable_mk.indicator hs).finStronglyMeasurable_of_set_sigmaFinite hs
      (fun x hx ↦ indicator_of_notMem hx _) hσ, ?_⟩
  refine (indicator_ae_eq_of_restrict_compl_ae_eq_zero hs hzero).symm.trans ?_
  filter_upwards [hf.ae_eq_mk] with x hx
  simp only [Set.indicator, hx]

end TauCeti

namespace MeasureTheory

/-- Countably many almost everywhere finitely strongly measurable functions have a common
measurable support on which the measure is sigma-finite: the union of the supports of the simple
approximants of their finitely strongly measurable representatives. -/
theorem AEFinStronglyMeasurable.exists_set_sigmaFinite_of_countable {α ι E : Type*}
    [MeasurableSpace α] [TopologicalSpace E] [T2Space E] [Zero E] [Countable ι]
    {μ : Measure α} {g : ι → α → E} (hg : ∀ i, AEFinStronglyMeasurable (g i) μ) :
    ∃ t, MeasurableSet t ∧ (∀ i, g i =ᵐ[μ.restrict tᶜ] 0) ∧ SigmaFinite (μ.restrict t) := by
  classical
  have hu i : FinStronglyMeasurable ((hg i).mk (g i)) μ := (hg i).finStronglyMeasurable_mk
  let T (p : ι × ℕ) := Function.support ((hu p.1).approx p.2)
  let t := ⋃ p, T p
  have ht : MeasurableSet t :=
    MeasurableSet.iUnion fun p ↦ ((hu p.1).approx p.2).measurableSet_support
  refine ⟨t, ht, fun i ↦ ?_, ?_⟩
  · rw [EventuallyEq, ae_restrict_iff' ht.compl]
    filter_upwards [(hg i).ae_eq_mk] with x hx hxt
    have hz m : (hu i).approx m x = 0 :=
      Function.notMem_support.mp fun h ↦ hxt (mem_iUnion.mpr ⟨(i, m), h⟩)
    exact hx.trans (tendsto_nhds_unique ((hu i).tendsto_approx x)
      (tendsto_const_nhds.congr fun m ↦ (hz m).symm))
  · refine Measure.sigmaFinite_of_countable ((countable_range T).insert tᶜ) ?_
      (by rw [sUnion_insert, sUnion_range, compl_union_self])
    rintro _ (rfl | ⟨p, rfl⟩)
    · simp [Measure.restrict_apply ht.compl]
    · exact (Measure.restrict_le_self _).trans_lt ((hu p.1).fin_support_approx p.2)

end MeasureTheory
