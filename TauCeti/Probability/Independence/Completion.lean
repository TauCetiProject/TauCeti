/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Independence and completion

Completing a measure does not change independence of sigma-algebras. Adjoining ambient
null events to either of two independent sigma-algebras also preserves independence.
These facts allow filtrations to be augmented without changing increment independence.
-/

public section

open MeasureTheory Filter

namespace ProbabilityTheory

variable {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Independence is unchanged when the ambient measure is completed. -/
@[simp]
theorem indep_completion_iff :
    @Indep (NullMeasurableSpace Ω P) m₁ m₂ inferInstance P.completion ↔ Indep m₁ m₂ P := by
  -- Completion changes the ambient measurable space, not the measure of any set.
  exact (@Indep_iff (NullMeasurableSpace Ω P) m₁ m₂ inferInstance P.completion).trans
    (Indep_iff m₁ m₂ P).symm

/-- Adjoining ambient null events to the second sigma-algebra preserves independence. -/
theorem Indep.eventuallyMeasurableSpace_right (h : Indep m₁ m₂ P) :
    Indep m₁ (eventuallyMeasurableSpace m₂ (ae P)) P := by
  rw [Indep_iff] at h ⊢
  rintro A B hA ⟨B', hB', hBB'⟩
  rw [measure_congr (EventuallyEqSet.inter EventuallyEq.rfl hBB'),
    measure_congr hBB']
  exact h A B' hA hB'

/-- Adjoining ambient null events to the first sigma-algebra preserves independence. -/
theorem Indep.eventuallyMeasurableSpace_left (h : Indep m₁ m₂ P) :
    Indep (eventuallyMeasurableSpace m₁ (ae P)) m₂ P :=
  h.symm.eventuallyMeasurableSpace_right.symm

end ProbabilityTheory
