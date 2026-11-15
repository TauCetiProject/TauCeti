/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Event probabilities from restricted pushforwards

A restricted pushforward equal to a scalar multiple of a measure gives a factorization
of preimage-event probabilities. This converts restricted distribution identities into
independence identities without requiring the restricting event to be measurable.

On a finite type, the restriction of a measure to its points of finite mass is a finite measure
(`MeasureTheory.Measure.isFiniteMeasure_restrict_setOf_measure_singleton_ne_top`).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- Evaluate a restricted distribution identity on a measurable event. -/
theorem measure_preimage_inter_eq_of_map_restrict_eq_smul
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {μ : Measure E} {f : Ω → E} {H : Set Ω} {C : Set E} {c : ℝ≥0∞}
    (hf : Measurable f) (hC : MeasurableSet C) (h : (P.restrict H).map f = c • μ) :
    P (f ⁻¹' C ∩ H) = c * μ C := by
  simpa only [Measure.map_apply hf hC, Measure.restrict_apply (hf hC),
    smul_apply, smul_eq_mul] using congrArg (fun ν : Measure E ↦ ν C) h

end TauCeti

namespace MeasureTheory.Measure

/-- On a finite type, the restriction of a measure to the points of finite mass is finite. -/
theorem isFiniteMeasure_restrict_setOf_measure_singleton_ne_top {α : Type*} [Finite α]
    [MeasurableSpace α] (ν : Measure α) :
    IsFiniteMeasure (ν.restrict {x | ν {x} ≠ ⊤}) := by
  rw [isFiniteMeasure_restrict]
  have h := measure_biUnion_ne_top (μ := ν) (Set.toFinite {x | ν {x} ≠ ⊤})
    (f := fun x ↦ {x}) fun x hx ↦ hx
  rwa [Set.biUnion_of_singleton] at h

end MeasureTheory.Measure
