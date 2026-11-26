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

The pointwise criterion is Mathlib's
`finStronglyMeasurable_iff_stronglyMeasurable_and_exists_set_sigmaFinite`.
-/

public section

open MeasureTheory Set

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
