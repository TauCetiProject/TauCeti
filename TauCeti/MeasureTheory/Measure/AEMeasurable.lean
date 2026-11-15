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
while preserving pointwise upper bounds. Canonical measurable modifications `hf.mk f` also preserve
pushforward measures and preimage or predicate-fiber measures without measurability assumptions on
the target set.

## Main results

* `MeasureTheory.Measure.map_restrict_le_map` — `(μ.restrict s).map f ≤ μ.map f` for an
  almost everywhere measurable `f`, with no hypothesis on `s`.
* `MeasurableEmbedding.map_map_measure` — `(μ.map f).map g = μ.map (g ∘ f)` for a measurable
  embedding `f`, with no measurability assumption on `g`.
* `AEMeasurable.exists_measurable_ge_ae_eq`: a measurable majorant in the same
  a.e. equivalence class.
* `AEMeasurable.map_mk`, `AEMeasurable.measure_preimage_mk`, `AEMeasurable.measure_setOf_mk`:
  invariance of pushforwards and preimage or predicate-fiber measures under `AEMeasurable.mk`.
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

section Mk

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {f : α → β}

/-- Replacing an almost everywhere measurable function `f` by its measurable modification `hf.mk f`
preserves its pushforward measure. -/
@[simp]
theorem map_mk (hf : AEMeasurable f μ) : μ.map (hf.mk f) = μ.map f :=
  Measure.map_congr hf.ae_eq_mk.symm

/-- Replacing an almost everywhere measurable function `f` by its measurable modification `hf.mk f`
preserves the measure of every preimage `f ⁻¹' s`, without requiring measurability of `s`. -/
@[simp]
theorem measure_preimage_mk (hf : AEMeasurable f μ) (s : Set β) :
    μ (hf.mk f ⁻¹' s) = μ (f ⁻¹' s) :=
  measure_congr (Filter.eventuallyEqSet_iff.2 (hf.ae_eq_mk.symm.mono fun _ hx ↦ by
    rw [Set.mem_preimage, Set.mem_preimage, hx]))

/-- Replacing an almost everywhere measurable function `f` by its measurable modification `hf.mk f`
preserves the measure of every predicate fiber `{x | p (f x)}`, without requiring measurability of
`{y | p y}`. -/
theorem measure_setOf_mk (hf : AEMeasurable f μ) (p : β → Prop) :
    μ {x | p (hf.mk f x)} = μ {x | p (f x)} :=
  hf.measure_preimage_mk {y | p y}

end Mk

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
