/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Almost everywhere measurable functions

Restricting a measure before pushing it forward along an almost everywhere measurable map can only
decrease the pushforward. This complements Mathlib's
`MeasureTheory.Measure.map_mono_of_aemeasurable`.

For an ordered target with a greatest element, an a.e. measurable function has a measurable
majorant agreeing with it almost everywhere. This permits replacement of representatives
while preserving pointwise upper bounds.

## Main results

* `MeasureTheory.Measure.map_restrict_le_map` — `(μ.restrict s).map f ≤ μ.map f` for an
  almost everywhere measurable `f`, with no hypothesis on `s`.
* `MeasureTheory.AEMeasurable.exists_measurable_ge_ae_eq`: a measurable majorant in the same
  a.e. equivalence class.
-/

public section

namespace MeasureTheory.AEMeasurable

/-- An a.e. measurable function into an ordered space with a greatest element admits a
measurable majorant that agrees with it almost everywhere. -/
theorem exists_measurable_ge_ae_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Preorder β] [OrderTop β] {μ : Measure α} {f : α → β} (hf : AEMeasurable f μ) :
    ∃ g : α → β, Measurable g ∧ f ≤ g ∧ f =ᵐ[μ] g := by
  classical
  obtain ⟨s, hs, hsm, hsμ⟩ := exists_measurable_superset_of_null hf.ae_eq_mk
  refine ⟨s.piecewise (fun _ => ⊤) (hf.mk f),
    measurable_const.piecewise hsm hf.measurable_mk, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ s
    · simp [hx]
    · have heq : f x = hf.mk f x := by
        by_contra h
        exact hx (hs h)
      simp [hx, heq]
  · filter_upwards [hf.ae_eq_mk, compl_mem_ae_iff.mpr hsμ] with x hx hxs
    simpa only [Set.piecewise_eq_of_notMem s _ _ hxs] using hx

end MeasureTheory.AEMeasurable

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {f : α → β}

/-- Pushing forward the part of `μ` carried by `s` gives a measure below the pushforward of `μ`.
No hypothesis on `s` is needed. -/
theorem map_restrict_le_map (hf : AEMeasurable f μ) (s : Set α) :
    (μ.restrict s).map f ≤ μ.map f :=
  map_mono_of_aemeasurable restrict_le_self hf

end MeasureTheory.Measure
