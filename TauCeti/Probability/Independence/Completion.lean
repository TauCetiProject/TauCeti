/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import TauCeti.Probability.Process.Filtration.AmbientNullAugmentation
import TauCeti.MeasureTheory.MeasurableSpace.EventuallyMeasurable

/-!
# Independence and completion

Completing a measure does not change independence of sigma-algebras. Adjoining ambient
null events to either of two independent sigma-algebras also preserves independence, and
replacing a random variable by an almost-everywhere equal one preserves independence of its
generated sigma-algebra. These facts allow filtrations to be augmented without changing
increment independence.
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
  rw [measure_congr (EventuallyEqSet.inter Filter.EventuallyEqSet.rfl hBB'),
    measure_congr hBB']
  exact h A B' hA hB'

/-- Adjoining ambient null events to the first sigma-algebra preserves independence. -/
theorem Indep.eventuallyMeasurableSpace_left (h : Indep m₁ m₂ P) :
    Indep (eventuallyMeasurableSpace m₁ (ae P)) m₂ P :=
  h.symm.eventuallyMeasurableSpace_right.symm

/-- Replacing the map in the first `comap` sigma-algebra by an almost-everywhere equal map
preserves independence. -/
theorem Indep.comap_congr_left {α : Type*} [MeasurableSpace α] {f g : Ω → α}
    (h : Indep (.comap f inferInstance) m₂ P) (hfg : f =ᵐ[P] g) :
    Indep (.comap g inferInstance) m₂ P :=
  indep_of_indep_of_le_left h.eventuallyMeasurableSpace_left <| by
    rw [TauCeti.eventuallyMeasurableSpace_comap_congr f g hfg]
    exact le_eventuallyMeasurableSpace

/-- Replacing the map in the second `comap` sigma-algebra by an almost-everywhere equal map
preserves independence. -/
theorem Indep.comap_congr_right {α : Type*} [MeasurableSpace α] {f g : Ω → α}
    (h : Indep m₁ (.comap f inferInstance) P) (hfg : f =ᵐ[P] g) :
    Indep m₁ (.comap g inferInstance) P :=
  (h.symm.comap_congr_left hfg).symm

/-- Adjoining ambient-measurable null events to a filtration preserves independence on the right. -/
theorem Indep.ambientNullAugmentation_right {ι : Type*} [Preorder ι] {ℱ : Filtration ι mΩ} {i : ι}
    (h : Indep m₁ (ℱ i) P) : Indep m₁ (ℱ.ambientNullAugmentation P i) P :=
  indep_of_indep_of_le_right h.eventuallyMeasurableSpace_right <| by
    simp [Filtration.ambientNullAugmentation_apply, Filtration.nullAugment_apply]

/-- Completing the ambient space and adjoining all ambient null events to a filtration preserves
independence on the right. -/
theorem Indep.nullAugment_right {ι : Type*} [Preorder ι] {ℱ : Filtration ι mΩ} {i : ι}
    (h : Indep m₁ (ℱ i) P) :
    @Indep (NullMeasurableSpace Ω P) m₁ (ℱ.nullAugment P i) inferInstance P.completion :=
  indep_completion_iff.mpr <| by
    simpa [Filtration.nullAugment_apply] using h.eventuallyMeasurableSpace_right

end ProbabilityTheory
