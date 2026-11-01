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

* `TauCeti.measureReal_le_abs_le_add`: the tail event of an absolute value is contained in the
  union of the upper and lower tails, so its measure is at most the sum of their measures.
-/

public section

open MeasureTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The tail event for an absolute value is contained in the union of the upper and lower tails. -/
theorem measureReal_le_abs_le_add [IsFiniteMeasure μ] {f : Ω → ℝ} {ε : ℝ} :
    μ.real {ω | ε ≤ |f ω|} ≤
      μ.real {ω | ε ≤ f ω} + μ.real {ω | ε ≤ -f ω} := by
  calc
    μ.real {ω | ε ≤ |f ω|}
      ≤ μ.real ({ω | ε ≤ f ω} ∪ {ω | ε ≤ -f ω}) := by
        refine measureReal_mono fun ω hω ↦ ?_
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
        rcases le_abs'.1 hω with h | h
        · exact Or.inr (by linarith)
        · exact Or.inl h
    _ ≤ μ.real {ω | ε ≤ f ω} + μ.real {ω | ε ≤ -f ω} :=
      measureReal_union_le _ _

end TauCeti
