/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.Piecewise
public import TauCeti.Data.Set.Countable

/-!
# Measurability of stopped values at countable-range times

For a process `u` and a random time `τ : Ω → WithTop ι`, Mathlib's `stoppedValue u τ` is the value
`u (τ ω) ω`, with an arbitrary index used where `τ ω = ⊤`. Mathlib proves that it is measurable
for the σ-algebra of a stopping time when `u` is progressively measurable with values in a
pseudo-metrizable Borel space (`MeasureTheory.measurable_stoppedValue`).

When time is countable, neither progressive measurability nor a topology on the values is needed:
the stopped value is pieced together from the countably many events `{τ = i}`, as recorded by the
preimage decomposition `MeasureTheory.stoppedValue_preimage_eq`. This file proves that

* `stoppedValue u τ` is measurable whenever `τ` and every `u i` are
  (`MeasureTheory.measurable_stoppedValue_of_countable`), which applies to processes, such as the
  shifted paths of a chain, that are not adapted to the filtration of `τ`;
* `stoppedValue u τ` is measurable for the σ-algebra of the stopping time `τ` whenever `u` is
  adapted in the measurable sense (`MeasureTheory.Adapted.measurable_stoppedValue`).

These are the measurability facts needed to state the strong Markov property of a chain with values
in an arbitrary measurable space.

Even for uncountable time, a stopping time with countable range permits
strongly measurable gluing, without any topology on time or separability assumption on the
values. Capping such a time at each deterministic horizon shows that a strongly adapted
process remains strongly adapted after stopping, including on a raw filtration.
-/

public section

open Filter

namespace MeasureTheory

variable {Ω ι β : Type*} [Nonempty ι] {m : MeasurableSpace Ω} {u : ι → Ω → β}
  {τ : Ω → WithTop ι}

/-- On a finite-time slice, the stopped value is the value of the process at that time. -/
theorem stoppedValue_of_eq {i : ι} {ω : Ω} (h : τ ω = i) :
    stoppedValue u τ ω = u i ω := by
  simp [stoppedValue, h]

/-- The preimage of a set under a stopped value, decomposed along the values of the stopping
time. -/
theorem stoppedValue_preimage_eq (t : Set β) :
    stoppedValue u τ ⁻¹' t =
      (⋃ i : ι, {ω | τ ω = i} ∩ u i ⁻¹' t) ∪
        ({ω | τ ω = ⊤} ∩ u (⊤ : WithTop ι).untopA ⁻¹' t) := by
  ext ω
  simp only [stoppedValue, Set.mem_preimage, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
    Set.mem_ofPred_eq]
  cases h : τ ω with
  | top => simp
  | coe i => simp

variable [MeasurableSpace β]

/-- In countable time, a stopped value of a measurable process at a measurable random time is
measurable. -/
theorem measurable_stoppedValue_of_countable [Countable ι] [MeasurableSpace (WithTop ι)]
    [MeasurableSingletonClass (WithTop ι)] (hu : ∀ i, Measurable (u i)) (hτ : Measurable τ) :
    Measurable (stoppedValue u τ) := by
  intro t ht
  rw [stoppedValue_preimage_eq]
  refine .union (.iUnion fun i => ?_) ?_
  · exact (hτ (measurableSet_singleton _)).inter (hu i ht)
  · exact (hτ (measurableSet_singleton _)).inter (hu _ ht)

section CountableTime

variable [PartialOrder ι] [Countable ι] {f : Filtration ι m}

/-- In countable time, a stopped value of an adapted process is measurable for the σ-algebra of
the stopping time. -/
theorem Adapted.measurable_stoppedValue (hu : Adapted f u) (hτ : IsStoppingTime f τ) :
    Measurable[hτ.measurableSpace] (stoppedValue u τ) := by
  intro t ht
  have hu' : ∀ i, MeasurableSet[⨆ j, f j] (u i ⁻¹' t) := fun i =>
    le_iSup f i _ (hu i ht)
  have heq : ∀ i : ι, MeasurableSet[⨆ j, f j] {ω | τ ω = i} := fun i =>
    le_iSup f i _ (hτ.measurableSet_eq_of_countable i)
  have htop : MeasurableSet[⨆ j, f j] {ω | τ ω = ⊤} := by
    have : {ω | τ ω = ⊤} = (⋃ i : ι, {ω | τ ω = i})ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      simpa [eq_comm] using WithTop.eq_top_iff_forall_ne (x := τ ω)
    rw [this]
    exact (MeasurableSet.iUnion heq).compl
  refine ⟨?_, fun i => ?_⟩
  · rw [stoppedValue_preimage_eq]
    exact .union (.iUnion fun i => (heq i).inter (hu' i)) (htop.inter (hu' _))
  · -- Before time `i`, only the countably many values `j ≤ i` of the stopping time contribute.
    have : stoppedValue u τ ⁻¹' t ∩ {ω | τ ω ≤ i} =
        ⋃ j : ι, ⋃ (_ : j ≤ i), {ω | τ ω = j} ∩ u j ⁻¹' t := by
      ext ω
      simp only [stoppedValue, Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
        Set.mem_iUnion, exists_prop]
      cases h : τ ω with
      | top => simp
      | coe k => simp [and_comm]
    rw [this]
    exact .iUnion fun j => .iUnion fun hj =>
      (f.mono hj _ (hτ.measurableSet_eq_of_countable j)).inter (f.mono hj _ (hu j ht))

end CountableTime

/-- An adapted process evaluated at a countable-range stopping time is strongly measurable for the
stopping sigma algebra. Neither path regularity nor a topology on time is required, and the time
may take the value `⊤`, where the stopped value is the process at the junk index
`(⊤ : WithTop ι).untopA`. The countability assumption is on the range of the time, not on all
times. -/
theorem StronglyAdapted.stronglyMeasurable_stoppedValue_of_countable_range
    {E : Type*} [TopologicalSpace E] [Zero E] [LinearOrder ι]
    {ℱ : Filtration ι m} {X : ι → Ω → E} (hX : StronglyAdapted ℱ X)
    (hτ : IsStoppingTime ℱ τ) (hc : (Set.range τ).Countable) :
    StronglyMeasurable[hτ.measurableSpace] (stoppedValue X τ) := by
  classical
  have := hc.to_subtype
  let R : Set ι := {i | (i : WithTop ι) ∈ Set.range τ}
  have hR : R.Countable := hc.preimage WithTop.coe_injective
  let s : Set.range τ → Set Ω := fun v ↦ {ω | τ ω = v.val}
  have hs : IndexedPartition s := IndexedPartition.mk' s
    (fun v w hvw ↦ Set.disjoint_left.2 fun ω hv hw ↦
      hvw (Subtype.ext (hv.symm.trans hw)))
    (fun v ↦ by obtain ⟨ω, hω⟩ := v.property; exact ⟨ω, hω⟩)
    (fun ω ↦ ⟨⟨τ ω, ⟨ω, rfl⟩⟩, rfl⟩)
  have htop : MeasurableSet[hτ.measurableSpace] {ω | τ ω = ⊤} := by
    have : {ω | τ ω = ⊤} = (⋃ i ∈ R, {ω | τ ω = i})ᶜ := by
      ext ω
      cases h : τ ω with
      | top => simp [h]
      | coe i =>
        simpa [h, R] using (⟨ω, h⟩ : ∃ y, τ y = (i : WithTop ι))
    rw [this]
    exact (MeasurableSet.biUnion hR fun i _ ↦ hτ.measurableSet_eq_of_countable_range' hc i).compl
  have hind (v : Set.range τ) :
      StronglyMeasurable[hτ.measurableSpace] ((s v).indicator (X v.val.untopA)) := by
    obtain ⟨v, hv⟩ := v
    induction v using WithTop.recTopCoe with
    | top =>
      refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on
        (m := ⨆ i, ℱ i) (hτ.measurableSpace_le' _ htop) (fun t ht ↦ ⟨ht, fun i ↦ ?_⟩)
        (((hX _).mono (le_iSup ℱ _)).indicator (hτ.measurableSpace_le' _ htop))
        (fun ω hω ↦ Set.indicator_of_notMem hω _)
      have : {ω | τ ω = ⊤} ∩ t ∩ {ω | τ ω ≤ i} = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨h, -⟩, h'⟩
        simp [h] at h'
      rw [this]
      exact @MeasurableSet.empty _ (ℱ i)
    | coe i =>
      have hslice : MeasurableSet[ℱ i] (s ⟨i, hv⟩) := hτ.measurableSet_eq_of_countable_range hc i
      refine StronglyMeasurable.stronglyMeasurable_of_measurableSpace_le_on hslice
        (fun t ht ↦ ?_) ((hX i).indicator hslice) (fun ω hω ↦ Set.indicator_of_notMem hω _)
      rw [Set.inter_comm, hτ.measurableSet_inter_eq_iff, Set.inter_comm]
      exact ht
  have hm (v : Set.range τ) : MeasurableSet[hτ.measurableSpace] (s v) := by
    obtain ⟨v, hv⟩ := v
    induction v using WithTop.recTopCoe with
    | top => exact htop
    | coe i => exact hτ.measurableSet_eq_of_countable_range' hc i
  let : MeasurableSpace Ω := hτ.measurableSpace
  convert hs.stronglyMeasurable_piecewise hm hind using 1
  ext ω
  rw [IndexedPartition.piecewise_apply, Set.indicator_of_mem (hs.mem_index ω)]
  simp only [stoppedValue]
  rw [(hs.mem_index ω : τ ω = _)]

/-- Stopping a strongly adapted process at a countable-range stopping time preserves literal
strong adaptation on a raw filtration, with no path regularity or finiteness assumption on
the stopping time. Each deterministic horizon caps the time at a finite value. -/
theorem StronglyAdapted.stoppedProcess_of_countable_range
    {E : Type*} [TopologicalSpace E] [Zero E] [LinearOrder ι]
    {ℱ : Filtration ι m} {X : ι → Ω → E} (hX : StronglyAdapted ℱ X)
    (hτ : IsStoppingTime ℱ τ) (hc : (Set.range τ).Countable) :
    StronglyAdapted ℱ (MeasureTheory.stoppedProcess X τ) := by
  rw [stoppedProcess_eq_stoppedValue]
  intro t
  have hct := ((Set.countable_singleton (t : WithTop ι)).mono Set.range_const_subset).range_min hc
  exact (hX.stronglyMeasurable_stoppedValue_of_countable_range
    ((isStoppingTime_const ℱ t).min hτ) hct).mono
      (((isStoppingTime_const ℱ t).min hτ).measurableSpace_le_of_le_const
        (fun _ ↦ min_le_left _ _))

end MeasureTheory
