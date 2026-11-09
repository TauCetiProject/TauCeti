/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.UnifTight

/-!
# Uniform tightness under almost everywhere domination

* `MeasureTheory.UnifTight.ae_mono`: uniform tightness passes to families which are dominated
  almost everywhere in norm by a uniformly tight family.
-/

public section

namespace MeasureTheory

open scoped ENNReal

/-- Uniform tightness passes to families dominated almost everywhere in norm by a uniformly
tight family. -/
protected theorem UnifTight.ae_mono {α β ι : Type*} {m : MeasurableSpace α}
    [NormedAddCommGroup β] {μ : Measure α} {p : ℝ≥0∞} {f g : ι → α → β}
    (hg : UnifTight g p μ) (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ)
    (hfg : ∀ i, (‖f i ·‖ₑ) ≤ᵐ[μ] (‖g i ·‖ₑ)) : UnifTight f p μ := by
  intro ε hε
  obtain ⟨s, hs, hfinite, hbound⟩ := hg.exists_measurableSet_indicator hε.ne'
  refine ⟨s, hfinite.ne, fun n ↦ (eLpNorm_mono_enorm_ae
    ((hf_meas n).indicator hs.compl) ?_).trans (hbound n)⟩
  filter_upwards [hfg n] with x hx
  by_cases hxs : x ∈ sᶜ
  · simpa only [Set.indicator_of_mem hxs] using hx
  · simp only [Set.indicator_of_notMem hxs, enorm_zero, le_refl]

end MeasureTheory
