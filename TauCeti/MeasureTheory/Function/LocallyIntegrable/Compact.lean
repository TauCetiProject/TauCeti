/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrability for measures carried by a compact set

A function continuous on a compact set of full measure is integrable if that set has finite
measure.
-/

public section

open MeasureTheory Set

/-- A function continuous on a compact set of full, finite measure is integrable. -/
theorem ContinuousOn.integrable_of_ae_mem_isCompact {X E : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} {s : Set X} {f : X → E} (hf : ContinuousOn f s)
    (hs : IsCompact s) (hμ : ∀ᵐ x ∂μ, x ∈ s) (hfin : μ s ≠ ⊤) : Integrable f μ := by
  obtain ⟨t, hst, ht, hzero⟩ := exists_measurable_superset_of_null
    (mem_ae_iff.1 (show s ∈ ae μ from hμ))
  have hts : tᶜ ⊆ s := by simpa only [compl_compl] using compl_subset_compl.mpr hst
  have hi := hf.integrableOn_of_subset_isCompact hs ht.compl hts (ne_top_of_le_ne_top hfin
    (measure_mono hts))
  have hae : ∀ᵐ x ∂μ, x ∈ tᶜ := compl_mem_ae_iff.2 hzero
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] using hi
