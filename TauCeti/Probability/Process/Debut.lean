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

The debut of a set in time × sample space is the infimum of its time fiber,
with infinity for an empty fiber. Time may be any conditionally complete linear order
with a bottom element, including nonnegative real time. The infimum need not belong to
the fiber. Its strict sublevel events are projections of the set restricted to an initial
time interval.

For standard Borel time with measurable open sets and a closed order, a progressive set's
strict debut sublevels at time `t` are null-measurable with respect to `P.trim (ℱ.le t)`
for any s-finite measure `P`. When these trimmed measures are complete
(in particular, when `ℱ.IsComplete P`), the sublevels are measurable in the current sigma
algebra. For standard Borel time with a first-countable order topology, right continuity
of the filtration then makes the debut a stopping time. This proof uses measurable
projection alone and does not select a point of the set or use an
optional/predictable section theorem.

## References

* C. Dellacherie and P.-A. Meyer, *Probabilities and Potential*, Chapters I–IV,
  North-Holland, 1978, Chapter IV, Theorem 50 (the debut theorem).
-/

public section

open Set MeasureTheory

namespace TauCeti

variable {ι Ω : Type*} [ConditionallyCompleteLinearOrderBot ι]

/-- The first possible time in a set's time fiber. Empty fibers have debut infinity;
the infimum need not be attained. -/
noncomputable def debut (s : Set (ι × Ω)) (ω : Ω) : WithTop ι :=
  ⨅ t : ι, ⨅ (_ : (t, ω) ∈ s), (t : WithTop ι)

/-- The debut is the infimum of the times in its fiber. -/
theorem debut_def (s : Set (ι × Ω)) (ω : Ω) :
    debut s ω = ⨅ t : ι, ⨅ (_ : (t, ω) ∈ s), (t : WithTop ι) := (rfl)

/-- Strict debut sublevels mean that the fiber has a point strictly before the threshold. -/
theorem debut_lt_iff {s : Set (ι × Ω)} {ω : Ω} {a : WithTop ι} :
    debut s ω < a ↔ ∃ u : ι, (u : WithTop ι) < a ∧ (u, ω) ∈ s := by
  simp only [debut, iInf_lt_iff]
  tauto

/-- At a finite threshold, strict debut sublevels are witnessed by an earlier time. -/
theorem debut_lt_coe_iff {s : Set (ι × Ω)} {ω : Ω} {t : ι} :
    debut s ω < t ↔ ∃ u < t, (u, ω) ∈ s := by
  simp [debut_lt_iff]

/-- The debut is no later than any point in its time fiber. -/
theorem debut_le_of_mem {s : Set (ι × Ω)} {ω : Ω} {t : ι}
    (ht : (t, ω) ∈ s) : debut s ω ≤ t :=
  iInf_le_of_le t (iInf_le _ ht)

/-- A lower bound for the debut is exactly a lower bound for every time in its fiber. -/
theorem le_debut_iff {s : Set (ι × Ω)} {ω : Ω} {a : WithTop ι} :
    a ≤ debut s ω ↔ ∀ t : ι, (t, ω) ∈ s → a ≤ t := by
  simp only [debut, le_iInf_iff]

/-- The debut of a union is the minimum of the two debuts. -/
@[simp]
theorem debut_union (s r : Set (ι × Ω)) : debut (s ∪ r) = debut s ⊓ debut r := by
  funext ω
  simp only [debut, mem_union, iInf_or]
  exact iInf_inf_eq

/-- The debut of a union is the infimum of the debuts. -/
@[simp]
theorem debut_iUnion {κ : Sort*} (s : κ → Set (ι × Ω)) :
    debut (⋃ i, s i) = ⨅ i, debut (s i) := by
  funext ω
  simp only [iInf_apply, debut, mem_iUnion, iInf_exists]
  rw [iInf_comm]

/-- A fiber has infinite debut exactly when it is empty. -/
@[simp]
theorem debut_eq_top_iff {s : Set (ι × Ω)} {ω : Ω} :
    debut s ω = ⊤ ↔ ∀ t, (t, ω) ∉ s := by
  rw [← top_le_iff, le_debut_iff]
  simp

/-- Enlarging a time fiber can only bring its debut earlier. -/
theorem debut_le_debut {s r : Set (ι × Ω)} {ω : Ω}
    (h : ∀ t, (t, ω) ∈ s → (t, ω) ∈ r) : debut r ω ≤ debut s ω :=
  le_debut_iff.mpr fun _ ht ↦ debut_le_of_mem (h _ ht)

/-- Enlarging a set can only bring its debut earlier. -/
theorem debut_anti : Antitone (debut (ι := ι) (Ω := Ω)) :=
  fun _ _ hsr _ ↦ debut_le_debut fun _ ht ↦ hsr ht

/-- The debut of the empty set is infinity. -/
@[simp]
theorem debut_empty : debut (∅ : Set (ι × Ω)) = fun _ ↦ ⊤ := by
  funext ω
  simp

/-- The debut of a deterministic closed ray is its endpoint. -/
@[simp]
theorem debut_Ici_prod_univ (a : ι) :
    debut (Ici a ×ˢ (univ : Set Ω)) = fun _ ↦ (a : WithTop ι) := by
  funext ω
  apply le_antisymm
  · exact debut_le_of_mem ⟨le_rfl, mem_univ _⟩
  · exact le_iInf fun t ↦ le_iInf fun ht ↦ WithTop.coe_le_coe.mpr ht.1

/-- The debut of the whole space is the bottom time. -/
@[simp]
theorem debut_univ : debut (univ : Set (ι × Ω)) = fun _ ↦ (⊥ : WithTop ι) := by
  simpa using (debut_Ici_prod_univ (Ω := Ω) (⊥ : ι))

-- At a maximal time or just before a successor, a closed sublevel has a fiber witness.
private theorem debut_le_iff_of_isTop_or_covBy {s : Set (ι × Ω)} {ω : Ω} {t : ι}
    (ht : IsTop t ∨ ∃ v, t ⋖ v) : debut s ω ≤ t ↔ ∃ u ≤ t, (u, ω) ∈ s := by
  constructor
  · intro h
    rcases ht with ht | ⟨v, htv⟩
    · obtain ⟨u, _, hu⟩ := debut_lt_iff.mp (h.trans_lt (WithTop.coe_lt_top t))
      exact ⟨u, ht u, hu⟩
    · obtain ⟨u, huv, hu⟩ :=
        debut_lt_coe_iff.mp (h.trans_lt (WithTop.coe_lt_coe.mpr htv.lt))
      exact ⟨u, htv.le_of_lt huv, hu⟩
  · rintro ⟨u, hut, hu⟩
    exact (debut_le_of_mem hu).trans (WithTop.coe_le_coe.mpr hut)

end TauCeti

namespace MeasurableSet

open TauCeti

variable {ι Ω : Type*} [ConditionallyCompleteLinearOrderBot ι] [TopologicalSpace ι]
  [MeasurableSpace ι] [OpensMeasurableSpace ι] [StandardBorelSpace ι]
  {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
  {P : Measure Ω} [SFinite P] {s : Set (ι × Ω)}

/-- For standard Borel time with measurable open sets and a closed order, a progressive
set's strict debut sublevel is null-measurable for the s-finite measure `P` trimmed to the
current sigma algebra. No usual conditions are needed. -/
theorem nullMeasurableSet_debut_lt [OrderClosedTopology ι]
    (hs : MeasurableSet[ℱ.progressive] s) (t : ι) :
    @NullMeasurableSet Ω (ℱ t) {ω | debut s ω < t} (P.trim (ℱ.le t)) := by
  have hs' := (ℱ.measurableSet_progressive_iff.mp hs) t
  have : @SFinite Ω (ℱ t) (P.trim (ℱ.le t)) := by
    rw [trim_eq_map]
    infer_instance
  let : MeasurableSpace Ω := ℱ t
  let : StandardBorelSpace (Iic t) := measurableSet_Iic.standardBorel
  let A : Set (Iic t × Ω) := {p | (p.1 : ι) < t ∧ ((p.1 : ι), p.2) ∈ s}
  have hA : MeasurableSet A :=
    (measurableSet_Iio.preimage (measurable_subtype_coe.comp measurable_fst)).inter hs'
  have he : {ω | debut s ω < t} = Prod.snd '' A := by
    ext ω
    constructor
    · intro hω
      obtain ⟨u, hut, hu⟩ := debut_lt_coe_iff.mp hω
      exact ⟨(⟨u, hut.le⟩, ω), ⟨hut, hu⟩, rfl⟩
    · rintro ⟨⟨⟨u, _⟩, ω⟩, ⟨hut, hu⟩, rfl⟩
      exact debut_lt_coe_iff.mpr ⟨u, hut, hu⟩
  rw [he]
  exact hA.nullMeasurableSet_image_snd

/-- For standard Borel time with measurable open sets and a closed order, a progressive
set's strict debut sublevel is measurable at time `t` if the s-finite measure `P` trimmed
to `ℱ t` is complete, in particular under `ℱ.IsComplete P`. -/
theorem measurableSet_debut_lt [OrderClosedTopology ι]
    (hs : MeasurableSet[ℱ.progressive] s) (P : Measure Ω)
    [SFinite P] (t : ι) [(P.trim (ℱ.le t)).IsComplete] :
    MeasurableSet[ℱ t] {ω | debut s ω < t} :=
  (hs.nullMeasurableSet_debut_lt (P := P) t).measurable_of_complete

/-- **The debut theorem.** For standard Borel time with measurable open sets and a
first-countable order topology, a right-continuous filtration with complete trims of an
s-finite measure `P` makes every progressive set's debut a stopping time. In particular,
`ℱ.IsComplete P` supplies the required trim completeness. No graph point or section is asserted. -/
theorem isStoppingTime_debut [OrderTopology ι] [FirstCountableTopology ι]
    (hs : MeasurableSet[ℱ.progressive] s) (P : Measure Ω)
    [SFinite P] [ℱ.IsRightContinuous] [∀ t, (P.trim (ℱ.le t)).IsComplete] :
    IsStoppingTime ℱ (debut s) := by
  refine isStoppingTime_of_measurableSet_lt_of_isRightContinuous'
    (fun t ↦ hs.measurableSet_debut_lt P t) fun t ht ↦ ?_
  have hs' := (ℱ.measurableSet_progressive_iff.mp hs) t
  have : @SFinite Ω (ℱ t) (P.trim (ℱ.le t)) := by
    rw [trim_eq_map]
    infer_instance
  let : MeasurableSpace Ω := ℱ t
  let : StandardBorelSpace (Iic t) := measurableSet_Iic.standardBorel
  have he : {ω | debut s ω ≤ t} =
      Prod.snd '' ((fun p : Iic t × Ω ↦ ((p.1 : ι), p.2)) ⁻¹' s) := by
    ext ω
    rw [mem_ofPred_eq, TauCeti.debut_le_iff_of_isTop_or_covBy (nhdsGT_eq_bot_iff.mp ht)]
    constructor
    · rintro ⟨u, hut, hu⟩
      exact ⟨(⟨u, hut⟩, ω), hu, rfl⟩
    · rintro ⟨⟨⟨u, hut⟩, ω⟩, hu, rfl⟩
      exact ⟨u, hut, hu⟩
  have hle : MeasurableSet[ℱ t] {ω | debut s ω ≤ t} :=
    he ▸ hs'.image_snd_of_complete (P.trim (ℱ.le t))
  convert hle.diff (hs.measurableSet_debut_lt P t) using 1
  ext ω
  simp only [mem_ofPred_eq, mem_sdiff, not_lt, le_antisymm_iff]

end MeasurableSet
