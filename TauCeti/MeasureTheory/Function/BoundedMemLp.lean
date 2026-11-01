/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# `Lᵖ` membership of a bounded observable of an a.e.-measurable map

On a finite measure space, a bounded measurable observable of an a.e.-measurable map lies in every
`Lᵖ`.  This is the pointwise composition fact underlying the bounded-observable entry point to the
L² lane of the Exchangeability roadmap; it carries no probabilistic content and applies to a single
map.

* `memLp_comp_of_bound` — if `f` is measurable, `g` is a.e. measurable, and `f ∘ g` is a.e. bounded,
  then `fun ω => f (g ω)` is in `Lᵖ` for every exponent.
* `memLp_coe_unitSphere` — the unit-sphere embedding is in every `Lᵖ` for any finite measure.

Credit for the reused material goes to Mathlib's `MemLp.of_bound`.
-/

public section

namespace TauCeti

open MeasureTheory Metric
open scoped ENNReal

/-- The unit-sphere embedding belongs to every `Lᵖ`, including `L∞`, for any finite measure. -/
@[simp]
theorem memLp_coe_unitSphere {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] (p : ℝ≥0∞)
    (μ : Measure (sphere (0 : E) 1)) [IsFiniteMeasure μ] :
    MemLp ((↑) : sphere (0 : E) 1 → E) p μ := by
  exact MemLp.of_bound (by fun_prop) 1 (by filter_upwards with x; simp)

variable {Ω α E : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace E]
  [NormedAddCommGroup E] [OpensMeasurableSpace E] [SecondCountableTopology E]

/-- A bounded measurable observable of an a.e.-measurable map belongs to every `Lᵖ` on a finite
measure space: if `f` is measurable, `g` is a.e. measurable, and `f ∘ g` is a.e. bounded, then
`fun ω => f (g ω)` is in `Lᵖ` for every exponent. -/
theorem memLp_comp_of_bound {μ : Measure Ω} [IsFiniteMeasure μ] {g : Ω → α} {f : α → E}
    (hf : Measurable f) (hg : AEMeasurable g μ) (C : ℝ) (hbound : ∀ᵐ ω ∂μ, ‖f (g ω)‖ ≤ C)
    (p : ENNReal) : MemLp (fun ω => f (g ω)) p μ :=
  MemLp.of_bound (hf.comp_aemeasurable hg).aestronglyMeasurable C hbound

end TauCeti
