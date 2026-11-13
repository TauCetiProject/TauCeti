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

For an s-finite measure `P`, a progressive set's strict debut sublevels at time `t` are
null-measurable with respect to `P.trim (ℱ.le t)`. When these trimmed measures are complete
(in particular, when `ℱ.IsComplete P`), the sublevels are measurable in the current sigma
algebra. Right continuity of the filtration then makes the debut a stopping time. This proof
uses measurable projection alone and does not select a point of the set or use an
optional/predictable section theorem.

## References

* C. Dellacherie and P.-A. Meyer, *Probabilities and Potential*, Chapters I–IV,
  North-Holland, 1978, Chapter IV, Theorem 50 (the debut theorem).
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

/-- A lower bound for the debut is exactly a lower bound for every time in its fiber. -/
theorem le_debut_iff {s : Set (ℝ≥0 × Ω)} {ω : Ω} {a : WithTop ℝ≥0} :
    a ≤ debut s ω ↔ ∀ t : ℝ≥0, (t, ω) ∈ s → a ≤ t := by
  simp only [debut, le_iInf_iff]

/-- The debut of a union is the minimum of the two debuts. -/
@[simp]
theorem debut_union (s r : Set (ℝ≥0 × Ω)) : debut (s ∪ r) = debut s ⊓ debut r := by
  funext ω
  simp only [debut, mem_union, iInf_or]
  exact iInf_inf_eq

/-- The debut of a union is the infimum of the debuts. -/
@[simp]
theorem debut_iUnion {ι : Sort*} (s : ι → Set (ℝ≥0 × Ω)) :
    debut (⋃ i, s i) = ⨅ i, debut (s i) := by
  funext ω
  simp only [iInf_apply, debut, mem_iUnion, iInf_exists]
  rw [iInf_comm]

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

/-- Enlarging a time fiber can only bring its debut earlier. -/
theorem debut_le_debut {s r : Set (ℝ≥0 × Ω)} {ω : Ω}
    (h : ∀ t, (t, ω) ∈ s → (t, ω) ∈ r) : debut r ω ≤ debut s ω :=
  le_debut_iff.mpr fun _ ht ↦ debut_le_of_mem (h _ ht)

/-- Enlarging a set can only bring its debut earlier. -/
theorem debut_anti : Antitone (debut (Ω := Ω)) :=
  fun _ _ hsr _ ↦ debut_le_debut fun _ ht ↦ hsr ht

/-- The debut of the empty set is infinity. -/
@[simp]
theorem debut_empty : debut (∅ : Set (ℝ≥0 × Ω)) = fun _ ↦ ⊤ := by
  funext ω
  simp

/-- The debut of a deterministic closed ray is its endpoint. -/
@[simp]
theorem debut_Ici_prod_univ (a : ℝ≥0) :
    debut (Ici a ×ˢ (univ : Set Ω)) = fun _ ↦ (a : WithTop ℝ≥0) := by
  funext ω
  apply le_antisymm
  · exact debut_le_of_mem ⟨le_rfl, mem_univ _⟩
  · exact le_iInf fun t ↦ le_iInf fun ht ↦ WithTop.coe_le_coe.mpr ht.1

/-- The debut of the whole space is zero. -/
@[simp]
theorem debut_univ : debut (univ : Set (ℝ≥0 × Ω)) = fun _ ↦ 0 := by
  simpa using (debut_Ici_prod_univ (Ω := Ω) 0)

end TauCeti

namespace MeasurableSet

open TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [SFinite P] {s : Set (ℝ≥0 × Ω)}

/-- A progressive set's strict debut sublevel is null-measurable for the s-finite measure
`P` trimmed to the current sigma algebra. No usual conditions are needed. -/
theorem nullMeasurableSet_debut_lt (hs : MeasurableSet[ℱ.progressive] s) (t : ℝ≥0) :
    @NullMeasurableSet Ω (ℱ t) {ω | debut s ω < t} (P.trim (ℱ.le t)) := by
  have hs' := (ℱ.measurableSet_progressive_iff.mp hs) t
  have : @SFinite Ω (ℱ t) (P.trim (ℱ.le t)) := by
    rw [trim_eq_map]
    infer_instance
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

/-- A progressive set's strict debut sublevel is measurable at time `t` if the s-finite
measure `P` trimmed to `ℱ t` is complete, in particular under `ℱ.IsComplete P`. -/
theorem measurableSet_debut_lt (hs : MeasurableSet[ℱ.progressive] s) (P : Measure Ω)
    [SFinite P] (t : ℝ≥0) [(P.trim (ℱ.le t)).IsComplete] :
    MeasurableSet[ℱ t] {ω | debut s ω < t} :=
  (hs.nullMeasurableSet_debut_lt (P := P) t).measurable_of_complete

/-- **The debut theorem.** A right-continuous filtration with complete trims of an s-finite
measure `P` makes every progressive set's debut a stopping time. In particular,
`ℱ.IsComplete P` supplies the required trim completeness. No graph point or section is asserted. -/
theorem isStoppingTime_debut (hs : MeasurableSet[ℱ.progressive] s) (P : Measure Ω)
    [SFinite P] [ℱ.IsRightContinuous] [∀ t, (P.trim (ℱ.le t)).IsComplete] :
    IsStoppingTime ℱ (debut s) :=
  isStoppingTime_of_measurableSet_lt_of_isRightContinuous fun t ↦ hs.measurableSet_debut_lt P t

end MeasurableSet
