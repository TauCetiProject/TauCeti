/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.Projection
public import TauCeti.Probability.Process.Filtration.Progressive
public import Mathlib.Probability.Process.Stopping

/-!
# Debuts of progressive sets

The debut of a set in nonnegative time × sample space is the infimum of its time fiber,
with infinity for an empty fiber. It need not belong to that fiber. Its strict sublevel
events are projections of the set restricted to a bounded time interval.

For a progressive set these projections are null-measurable in the current sigma algebra.
On a complete finite measure space whose filtration contains the ambient null sets at time
zero, they are measurable there. Right continuity of the filtration then makes the debut a
stopping time. This proof uses measurable projection alone and does not select a point of the
set or use an optional/predictable section theorem.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, §2 (the debut theorem).
-/

public section

open Set MeasureTheory
open scoped NNReal

namespace TauCeti

variable {Ω : Type*}

/-- The first possible time in a set's time fiber. Empty fibers have debut infinity;
the infimum need not be attained. -/
noncomputable def debut (s : Set (ℝ≥0 × Ω)) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ t : ℝ≥0, ⨅ (_ : (t, ω) ∈ s), (t : WithTop ℝ≥0)

/-- The debut is the infimum of the times in its fiber. -/
theorem debut_def (s : Set (ℝ≥0 × Ω)) (ω : Ω) :
    debut s ω = ⨅ t : ℝ≥0, ⨅ (_ : (t, ω) ∈ s), (t : WithTop ℝ≥0) := (rfl)

/-- Strict debut sublevels mean that the fiber has a point strictly before the threshold. -/
theorem debut_lt_iff {s : Set (ℝ≥0 × Ω)} {ω : Ω} {t : ℝ≥0} :
    debut s ω < t ↔ ∃ u < t, (u, ω) ∈ s := by
  simp only [debut, iInf_lt_iff, WithTop.coe_lt_coe]
  tauto

/-- The debut is no later than any point in its time fiber. -/
theorem debut_le_of_mem {s : Set (ℝ≥0 × Ω)} {ω : Ω} {t : ℝ≥0}
    (ht : (t, ω) ∈ s) : debut s ω ≤ t :=
  iInf_le_of_le t (iInf_le _ ht)

/-- A fiber has infinite debut exactly when it is empty. -/
@[simp]
theorem debut_eq_top_iff {s : Set (ℝ≥0 × Ω)} {ω : Ω} :
    debut s ω = ⊤ ↔ ∀ t, (t, ω) ∉ s := by
  constructor
  · intro h t ht
    have hle := debut_le_of_mem ht
    exact WithTop.not_top_le_coe t (h ▸ hle)
  · intro h
    exact top_unique (le_iInf fun t ↦ le_iInf fun ht ↦ (h t ht).elim)

/-- Enlarging a set can only bring its debut earlier. -/
theorem debut_anti {s r : Set (ℝ≥0 × Ω)} (hsr : s ⊆ r) (ω : Ω) :
    debut r ω ≤ debut s ω :=
  le_iInf fun _ ↦ le_iInf fun ht ↦ debut_le_of_mem (hsr ht)

/-- The debut of the empty set is infinity. -/
@[simp]
theorem debut_empty : debut (∅ : Set (ℝ≥0 × Ω)) = fun _ ↦ ⊤ := by
  funext ω
  simp

/-- The debut of a deterministic closed ray is its endpoint. -/
@[simp]
theorem debut_Ici_prod (a : ℝ≥0) :
    debut (Ici a ×ˢ (univ : Set Ω)) = fun _ ↦ (a : WithTop ℝ≥0) := by
  funext ω
  apply le_antisymm
  · exact debut_le_of_mem ⟨le_rfl, mem_univ _⟩
  · exact le_iInf fun t ↦ le_iInf fun ht ↦ WithTop.coe_le_coe.mpr ht.1

/-- The debut of the whole space is zero. -/
@[simp]
theorem debut_univ : debut (univ : Set (ℝ≥0 × Ω)) = fun _ ↦ 0 := by
  simpa using (debut_Ici_prod (Ω := Ω) 0)

end TauCeti

namespace MeasurableSet

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {s : Set (ℝ≥0 × Ω)}

/-- A progressive set's strict debut sublevel is null-measurable for the measure trimmed
to the current sigma algebra. No usual conditions are needed for this assertion. -/
theorem nullMeasurableSet_debut_lt (hs : MeasurableSet[ℱ.progressive] s) (t : ℝ≥0) :
    @NullMeasurableSet Ω (ℱ t) {ω | debut s ω < t} (P.trim (ℱ.le t)) := by
  have hs' := (ℱ.measurableSet_progressive_iff.mp hs) t
  let : MeasurableSpace Ω := ℱ t
  let : StandardBorelSpace (Iic t) := measurableSet_Iic.standardBorel
  let A : Set (Iic t × Ω) := {p | (p.1 : ℝ≥0) < t ∧ ((p.1 : ℝ≥0), p.2) ∈ s}
  have hA : MeasurableSet A :=
    (measurableSet_lt (measurable_subtype_coe.comp measurable_fst) measurable_const).inter hs'
  have he : {ω | debut s ω < t} = Prod.snd '' A := by
    ext ω
    constructor
    · intro hω
      obtain ⟨u, hut, hu⟩ := debut_lt_iff.mp hω
      exact ⟨(⟨u, hut.le⟩, ω), ⟨hut, hu⟩, rfl⟩
    · rintro ⟨⟨⟨u, _⟩, ω⟩, ⟨hut, hu⟩, rfl⟩
      exact debut_lt_iff.mpr ⟨u, hut, hu⟩
  rw [he]
  exact hA.nullMeasurableSet_image_snd

/-- On a complete finite measure space with all ambient null sets visible at time zero,
the strict debut sublevels of a progressive set are measurable at the current time. -/
theorem measurableSet_debut_lt (hs : MeasurableSet[ℱ.progressive] s) [P.IsComplete]
    (hcomplete : ∀ A, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) (t : ℝ≥0) :
    MeasurableSet[ℱ t] {ω | debut s ω < t} := by
  let : (P.trim (ℱ.le t)).IsComplete := ⟨fun A hA ↦ by
    have hPA : P A = 0 := measure_eq_zero_of_trim_eq_zero (ℱ.le t) hA
    exact ℱ.mono bot_le _ (hcomplete A (measurableSet_of_null hPA) hPA)⟩
  exact (hs.nullMeasurableSet_debut_lt (P := P) t).measurable_of_complete

/-- **The debut theorem.** On a complete finite measure space, a right-continuous filtration
containing all ambient null sets at time zero makes every progressive set's debut a stopping
time. No graph point or section is asserted. -/
theorem isStoppingTime_debut (hs : MeasurableSet[ℱ.progressive] s) [P.IsComplete]
    [ℱ.IsRightContinuous]
    (hcomplete : ∀ A, MeasurableSet A → P A = 0 → MeasurableSet[ℱ 0] A) :
    IsStoppingTime ℱ (debut s) :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    (hs.measurableSet_debut_lt hcomplete)

end MeasurableSet
