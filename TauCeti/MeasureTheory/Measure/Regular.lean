/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Inner regularity under almost everywhere continuous maps

A measurable map that is continuous on a measurable set of full measure sends an inner regular
measure to an inner regular measure. Global continuity is unnecessary: compact approximation
can be performed inside the set where the map is continuous. This applies, for example, to
spectral character assignments whose exceptional set has measure zero.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {α β : Type*} [MeasurableSpace α] [TopologicalSpace α]
  [MeasurableSpace β] [TopologicalSpace β]

/-- A measurable map continuous on a measurable set of full measure preserves inner regularity.
No separation, countability or finiteness assumption is required. -/
theorem innerRegular_map_of_continuousOn {μ : Measure α} [μ.InnerRegular]
    {f : α → β} {s : Set α} (hf : Measurable f) (hs : MeasurableSet s)
    (hcont : ContinuousOn f s) (hmem : ∀ᵐ x ∂μ, x ∈ s) :
    (Measure.map f μ).InnerRegular := by
  constructor
  intro t ht r hr
  rw [Measure.map_apply hf ht] at hr
  rw [← μ.measure_inter_eq_of_ae hmem, inter_comm] at hr
  obtain ⟨K, hKsub, hK, hrK⟩ := ((hf ht).inter hs).exists_lt_isCompact hr
  refine ⟨f '' K, image_subset_iff.mpr (hKsub.trans inter_subset_left),
    hK.image_of_continuousOn (hcont.mono (hKsub.trans inter_subset_right)), ?_⟩
  exact hrK.trans_le (Measure.le_map_apply_image hf.aemeasurable K)

end TauCeti
