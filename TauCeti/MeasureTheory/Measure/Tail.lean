/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Real

/-!
# Elementary tail bounds

## Main results

* `TauCeti.measureReal_le_abs_le_add`: the tail event of an absolute value is the union of the
  upper and lower tails, so its measure is at most the sum of their measures.
-/

public section

open MeasureTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The measure of the event `ε ≤ |f|` is at most the sum of the measures of the upper tail
`ε ≤ f` and the lower tail `ε ≤ -f`. -/
theorem measureReal_le_abs_le_add {f : Ω → ℝ} {ε : ℝ} :
    μ.real {ω | ε ≤ |f ω|} ≤
      μ.real {ω | ε ≤ f ω} + μ.real {ω | ε ≤ -f ω} := by
  have hset : {ω | ε ≤ |f ω|} = {ω | ε ≤ f ω} ∪ {ω | ε ≤ -f ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · intro h
      rcases le_abs'.1 h with h' | h'
      · exact Or.inr (by linarith)
      · exact Or.inl h'
    · rintro (h | h)
      · exact le_abs'.2 (Or.inr h)
      · exact le_abs'.2 (Or.inl (by linarith))
  rw [hset]
  exact measureReal_union_le _ _

end TauCeti
