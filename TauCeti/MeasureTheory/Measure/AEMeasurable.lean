/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Pushforwards and measurable majorants

Restricting a measure before pushing it forward along an almost everywhere measurable map can only
decrease the pushforward. This complements Mathlib's
`MeasureTheory.Measure.map_mono_of_aemeasurable`. Pushing a measure forward along a measurable
embedding `f` and then along any function `g` is pushing it forward along `g ∘ f`, even for a
function `g` that is not almost everywhere measurable. In that case Mathlib's pushforward of a
nonzero measure is a fallback Dirac measure, the same for `g` and for `g ∘ f`, and for the zero
measure both pushforwards are zero.

For an ordered target with a greatest element, an a.e. measurable function has a measurable
majorant agreeing with it almost everywhere. This permits replacement of representatives
while preserving pointwise upper bounds.

## Main results

* `MeasureTheory.Measure.map_restrict_le_map` — `(μ.restrict s).map f ≤ μ.map f` for an
  almost everywhere measurable `f`, with no hypothesis on `s`.
* `MeasurableEmbedding.map_map_measure` — `(μ.map f).map g = μ.map (g ∘ f)` for a measurable
  embedding `f`, with no measurability assumption on `g`.
* `AEMeasurable.exists_measurable_ge_ae_eq`: a measurable majorant in the same
  a.e. equivalence class.
-/

public section

namespace AEMeasurable

open MeasureTheory

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

end AEMeasurable

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {f : α → β}

/-- Pushing forward the part of `μ` carried by `s` gives a measure below the pushforward of `μ`.
No hypothesis on `s` is needed. -/
theorem map_restrict_le_map (hf : AEMeasurable f μ) (s : Set α) :
    (μ.restrict s).map f ≤ μ.map f :=
  map_mono_of_aemeasurable restrict_le_self hf

end MeasureTheory.Measure

namespace MeasurableEmbedding

open MeasureTheory

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] {f : α → β}

/-- Pushing a measure forward along a measurable embedding `f` and then along any function `g`
is pushing it forward along `g ∘ f`, with no measurability assumption on `g`. -/
theorem map_map_measure (hf : MeasurableEmbedding f) (μ : Measure α) (g : β → γ) :
    (μ.map f).map g = μ.map (g ∘ f) := by
  by_cases hg : AEMeasurable g (μ.map f)
  · exact AEMeasurable.map_map_of_aemeasurable hg hf.measurable.aemeasurable
  · by_cases hμ : μ = 0
    · simp [hμ]
    · have hμ' : μ.map f ≠ 0 := fun h ↦
        hμ ((Measure.map_eq_zero_iff hf.measurable.aemeasurable).1 h)
      rw [Measure.map_of_not_aemeasurable_of_ne_zero hg hμ',
        Measure.map_of_not_aemeasurable_of_ne_zero (hf.aemeasurable_map_iff.not.1 hg) hμ]

end MeasurableEmbedding
