/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Basic

/-!
# The parts of a set inside and outside another set

If `s` has finite measure and `t ∩ s` is null measurable, the measures of `t ∩ s` and `s \ t` add
up to that of `s`. So a lower bound `η μ s ≤ μ (s \ t)` on the part of `s` outside `t` is an upper
bound `μ (t ∩ s) ≤ (1 - η) μ s` on the part inside it. Density arguments such as the
Krylov–Safonov covering iteration use this form to pass from "`u` is small on a fixed fraction of
a cube" to "`u` is large on at most the complementary fraction".

## Main declarations

* `TauCeti.measure_inter_le_one_sub_mul`: a fraction `η` of `s` outside `t` leaves at most a
  fraction `1 - η` of `s` inside `t`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s t : Set α} {η : ℝ≥0∞}

/-- If a fraction `η` of a set `s` of finite measure lies outside `t`, and `t ∩ s` is null
measurable, then at most a fraction `1 - η` of `s` lies inside `t`. -/
theorem measure_inter_le_one_sub_mul (hts : NullMeasurableSet (t ∩ s) μ) (hs : μ s ≠ ∞)
    (h : η * μ s ≤ μ (s \ t)) : μ (t ∩ s) ≤ (1 - η) * μ s := by
  have hsplit := measure_inter_add_sdiff₀ (μ := μ) s hts
  rw [inter_eq_right.2 inter_subset_right, sdiff_inter_self_eq_sdiff] at hsplit
  rw [ENNReal.sub_mul fun _ _ ↦ hs, one_mul]
  exact ENNReal.le_sub_of_add_le_right
    (ne_top_of_le_ne_top hs (h.trans (measure_mono sdiff_subset)))
    ((add_le_add_right h _).trans_eq hsplit)

end TauCeti
