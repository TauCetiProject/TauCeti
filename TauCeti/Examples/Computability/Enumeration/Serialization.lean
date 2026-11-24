/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Encoded
import TauCeti.Computability.Enumeration.Unpaused

/-!
# Examples of serialization and pause removal

A batched relation keeps each pair intact. The two tags on a common element of a
disjoint sum have different entry stages. A one-element enumeration has a first
entry and no second entry, while a paused enumeration of the naturals can be
read at its cardinality clock to recover the ordinary initial segments.
-/

open TauCeti.Enumeration

-- The raw relation has two pairs at once, with the same first component.
example :
    stageLimit (serializedStageOf (fun _ => ({(1, 2), (1, 3)} : Finset (ℕ × ℕ)))) =
      {(1, 2), (1, 3)} := by
  rw [stageLimit_serializedStageOf]
  ext x
  simp

/-- Both tagged copies of zero appear in the serialization at different transitions. -/
public theorem TauCeti.Enumeration.Examples.distinct_tagged_entry_stages :
    ∃ s t, s ≠ t ∧
      Sum.inl 0 ∈ fresh (serializedStageOf (fun _ =>
        ({0} : Finset ℕ).disjSum ({0} : Finset ℕ))) s ∧
      Sum.inr 0 ∈ fresh (serializedStageOf (fun _ =>
        ({0} : Finset ℕ).disjSum ({0} : Finset ℕ))) t := by
  let A := fun _ : ℕ => ({0} : Finset ℕ).disjSum ({0} : Finset ℕ)
  let B := serializedStageOf A
  have hlim : stageLimit B = stageLimit A := stageLimit_serializedStageOf A
  have hl : Sum.inl 0 ∈ stageLimit B := hlim ▸ mem_stageLimit.mpr ⟨0, by simp [A]⟩
  have hr : Sum.inr 0 ∈ stageLimit B := hlim ▸ mem_stageLimit.mpr ⟨0, by simp [A]⟩
  obtain ⟨s, hs⟩ := exists_mem_fresh_of_mem_stageLimit hl (by simp [B])
  obtain ⟨t, ht⟩ := exists_mem_fresh_of_mem_stageLimit hr (by simp [B])
  refine ⟨s, t, ?_, hs, ht⟩
  rintro rfl
  have hle : (fresh B s).card ≤ 1 := card_fresh_serializedStageOf_le_one A s
  exact Sum.inl_ne_inr (Finset.card_le_one_iff.mp hle hs ht)

/-- A serialized singleton that first appears at the end of stage three. -/
private def singletonStages (s : ℕ) : Finset ℕ :=
  if s < 3 then ∅ else {42}

example : 42 ∈ entryAt singletonStages 0 ∧ ¬ (entryAt singletonStages 1).Dom := by
  have hm : Monotone singletonStages := by
    intro s t hst
    unfold singletonStages
    split_ifs with hs ht <;> simp_all
    omega
  have hstep (s : ℕ) : (fresh singletonStages s).card ≤ 1 := by
    have hsub : fresh singletonStages s ⊆ {42} := by
      have hs : singletonStages (s + 1) ⊆ {42} := by
        unfold singletonStages
        split_ifs <;> simp
      rw [fresh_eq_sdiff]
      exact (Finset.sdiff_subset (s := singletonStages (s + 1)) (t := singletonStages s)).trans hs
    exact (Finset.card_le_card hsub).trans (by simp)
  constructor
  · exact (mem_entryAt hm hstep).mpr ⟨2, by simp [singletonStages], by simp [singletonStages]⟩
  · rw [entryAt_dom hm (by simp [singletonStages]) hstep]
    rintro ⟨s, hs⟩
    unfold singletonStages at hs
    split_ifs at hs <;> simp_all

example : ¬ (stageAtCard (fun _ => (∅ : Finset ℕ)) 1).Dom := by
  simp

-- Removing the intervening pauses from [0, ⌊s / 2⌋) gives [0, n) at output stage n.
example (n : ℕ) :
    ∃ (hm : Monotone fun s : ℕ => Finset.range (s / 2))
      (hi : (stageLimit fun s : ℕ => Finset.range (s / 2)).Infinite),
      unpausedStage (fun s => Finset.range (s / 2)) hm hi n = Finset.range n := by
  have hm : Monotone fun s : ℕ => Finset.range (s / 2) :=
    fun _ _ h => Finset.range_subset_range.mpr (Nat.div_le_div_right h)
  have hi : (stageLimit fun s : ℕ => Finset.range (s / 2)).Infinite := by
    apply (stageLimit_infinite_iff hm).mpr
    intro k
    refine ⟨2 * k, ?_⟩
    simp
  refine ⟨hm, hi, ?_⟩
  have h := unpausedStage_card hm hi (2 * n)
  simpa using h
