/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Hall.Finite

import Mathlib.Data.Finset.Sum

/-!
# Deficiency form of Hall's theorem

For a finite family `t : ι → Finset α`, its Hall deficiency is the largest value of
`|S| - |⋃ i ∈ S, t i|`.  This file proves that the deficiency is exactly the number of indices
left unmatched by a largest partial system of distinct representatives.

The attaining result keeps the partial choice function defined only on its selected finite set
of indices.  This permits the empty partial choice even when `α` is empty.  It also supplies a
set `S` witnessing the cardinality identity

`|D| + |S| = |ι| + |⋃ i ∈ S, t i|`,

while the reverse inequality holds for every partial injective choice on `D` and every `S`.
The proof applies Mathlib's finite Hall theorem after adjoining a common set of dummy choices,
one for each unit of deficiency.

This is the finite-family form of the classical deficiency theorem; see R. Diestel,
*Graph Theory*, 5th ed., Graduate Texts in Mathematics 173, Springer, 2017, Section 2.1.
-/

public section

open Function

namespace Finset

universe u v

variable {ι : Type u} {α : Type v} [Fintype ι] [DecidableEq α]

/-- The largest excess of the number of indices in a finite subfamily over the cardinality of
the union of its available choices. -/
noncomputable def hallDeficiency (t : ι → Finset α) : ℕ :=
  univ.powerset.sup fun S ↦ #S - #(S.biUnion t)

/-- Every subfamily's excess is bounded by the Hall deficiency. -/
theorem card_sub_card_biUnion_le_hallDeficiency (t : ι → Finset α) (S : Finset ι) :
    #S - #(S.biUnion t) ≤ hallDeficiency t := by
  classical
  exact Finset.le_sup (f := fun T ↦ #T - #(T.biUnion t))
    (mem_powerset.mpr (subset_univ S))

/-- Some set of indices attains the Hall deficiency.  When the deficiency is zero, the empty
set is chosen. -/
theorem exists_card_sub_card_biUnion_eq_hallDeficiency (t : ι → Finset α) :
    ∃ S : Finset ι, #S - #(S.biUnion t) = hallDeficiency t := by
  classical
  by_cases h : hallDeficiency t = 0
  · exact ⟨∅, by simp [h]⟩
  · obtain ⟨S, hS, hmax⟩ := Finset.exists_mem_eq_sup univ.powerset
      (by simp : univ.powerset.Nonempty) (fun S ↦ #S - #(S.biUnion t))
    exact ⟨S, hmax.symm⟩

/-- The Hall deficiency as the maximum excess over all subfamilies. -/
theorem hallDeficiency_def (t : ι → Finset α) :
    hallDeficiency t = univ.powerset.sup fun S ↦ #S - #(S.biUnion t) := by
  classical
  rfl

/-- The Hall deficiency is at most `k` exactly when every subfamily has at most `k` more
indices than available choices. -/
theorem hallDeficiency_le_iff (t : ι → Finset α) (k : ℕ) :
    hallDeficiency t ≤ k ↔ ∀ S : Finset ι, #S ≤ #(S.biUnion t) + k := by
  classical
  simp [hallDeficiency_def, Finset.sup_le_iff, Nat.sub_le_iff_le_add, add_comm]

/-- The Hall deficiency is at most the number of indices. -/
theorem hallDeficiency_le_card (t : ι → Finset α) :
    hallDeficiency t ≤ Fintype.card ι := by
  classical
  apply Finset.sup_le
  intro S hS
  exact (Nat.sub_le _ _).trans (by simpa using card_le_card (mem_powerset.mp hS))

/-- The cardinality inequality for a partial system of distinct representatives: its selected
domain and any test set `S` have total size at most `|ι| + |⋃ i ∈ S, t i|`. -/
theorem card_add_card_le_card_add_card_biUnion_of_partialInjective
    (t : ι → Finset α) (D S : Finset ι) (f : D → α) (hf : Injective f)
    (hft : ∀ i : D, f i ∈ t i) :
    #D + #S ≤ Fintype.card ι + #(S.biUnion t) := by
  classical
  let A : Finset D := univ.filter fun i ↦ (i : ι) ∈ S
  let B : Finset D := univ.filter fun i ↦ (i : ι) ∉ S
  let e : D ↪ α := ⟨f, hf⟩
  have hA : A.map e ⊆ S.biUnion t := by
    intro a ha
    rw [mem_map] at ha
    obtain ⟨i, hiA, rfl⟩ := ha
    rw [mem_biUnion]
    exact ⟨i, (mem_filter.mp hiA).2, hft i⟩
  have hAcard : #A ≤ #(S.biUnion t) := by
    rw [← card_map]
    exact card_le_card hA
  let inclusion : D ↪ ι := ⟨Subtype.val, Subtype.val_injective⟩
  have hB : B.map inclusion ⊆ univ \ S := by
    intro i hi
    rw [mem_map] at hi
    obtain ⟨j, hjB, rfl⟩ := hi
    exact mem_sdiff.mpr ⟨mem_univ _, (mem_filter.mp hjB).2⟩
  have hBcard : #B ≤ #(univ \ S) := by
    rw [← card_map]
    exact card_le_card hB
  have hD : #A + #B = #D := by
    simpa [A, B] using
      (card_filter_add_card_filter_not (s := (univ : Finset D))
        (p := fun i ↦ (i : ι) ∈ S))
  have hι := card_sdiff_add_card_inter univ S
  simp only [inter_eq_right.mpr (subset_univ S), card_univ] at hι
  omega

/-- Adjoining `hallDeficiency t` common dummy choices to every set of a family gives a family
satisfying Hall's condition.  The definition of deficiency is exactly this condition. -/
private theorem card_le_card_biUnion_disjSum_univ_hallDeficiency (t : ι → Finset α)
    (S : Finset ι) :
    #S ≤ #(S.biUnion fun i ↦ (t i).disjSum (univ : Finset (Fin (hallDeficiency t)))) := by
  classical
  have hbiUnion :
      (S.biUnion fun i ↦ (t i).disjSum (univ : Finset (Fin (hallDeficiency t)))) =
        (S.biUnion t).disjSum (if S.Nonempty then univ else ∅) := by
    ext z
    rcases z with a | b
    · simp
    · simp only [mem_biUnion, inr_mem_disjSum, mem_univ, and_true]
      by_cases hS : S.Nonempty
      · exact ⟨fun _ ↦ by simp [hS], fun _ ↦ hS⟩
      · refine ⟨fun h ↦ (hS h).elim, fun h ↦ ?_⟩
        simp [hS] at h
  by_cases hS : S.Nonempty
  · simp only [hbiUnion, card_disjSum, hS, ↓reduceIte, card_univ, Fintype.card_fin]
    have hle := card_sub_card_biUnion_le_hallDeficiency t S
    omega
  · rw [not_nonempty_iff_eq_empty.mp hS]
    exact Nat.zero_le _

omit [DecidableEq α] in
/-- An injective map into `α ⊕ Fin d` sends at most `d` indices to the `Fin d` summand. -/
private theorem card_sdiff_filter_exists_inl_le {d : ℕ} (g : ι → α ⊕ Fin d)
    [DecidableEq ι] [DecidablePred fun i ↦ ∃ a, g i = Sum.inl a] (hg : Injective g) :
    #(univ \ univ.filter fun i ↦ ∃ a, g i = Sum.inl a) ≤ d := by
  set D : Finset ι := univ.filter fun i ↦ ∃ a, g i = Sum.inl a
  have hright (i : (univ \ D : Finset ι)) : ∃ b, g i = Sum.inr b := by
    have hiD : (i : ι) ∉ D := (mem_sdiff.mp i.2).2
    cases hgi : g i with
    | inl a => exact False.elim (hiD (mem_filter.mpr ⟨mem_univ _, ⟨a, hgi⟩⟩))
    | inr b => exact ⟨b, rfl⟩
  let r : (univ \ D : Finset ι) → Fin d := fun i ↦ Classical.choose (hright i)
  have hgr (i : (univ \ D : Finset ι)) : g i = Sum.inr (r i) := Classical.choose_spec (hright i)
  have hr : Injective r := by
    intro i j hij
    apply Subtype.ext
    exact hg (by simpa only [hgr i, hgr j, Sum.inr.injEq] using hij)
  simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective r hr

/-- A finite family has a partial injective choice and a set attaining equality in the
deficiency bound.  The choice function is defined only on the selected set `D`. -/
theorem exists_partialInjective_card_add_card_eq_card_add_card_biUnion
    (t : ι → Finset α) :
    ∃ (D S : Finset ι) (f : D → α), Injective f ∧ (∀ i : D, f i ∈ t i) ∧
      #D + #S = Fintype.card ι + #(S.biUnion t) ∧
      #D = Fintype.card ι - hallDeficiency t := by
  classical
  let d := hallDeficiency t
  -- Adjoin `d` common dummy choices; Hall's condition holds for the augmented family.
  let augmented : ι → Finset (α ⊕ Fin d) := fun i ↦ (t i).disjSum univ
  have hHall : ∀ S : Finset ι, #S ≤ #(S.biUnion augmented) :=
    card_le_card_biUnion_disjSum_univ_hallDeficiency t
  obtain ⟨g, hg, hgt⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective' augmented).mp hHall
  -- Keep precisely the indices at which the full augmented choice uses an original value.
  let D : Finset ι := univ.filter fun i ↦ ∃ a, g i = Sum.inl a
  have hg_left {i : ι} (hi : i ∈ D) : ∃ a, g i = Sum.inl a :=
    (mem_filter.mp hi).2
  let f : D → α := fun i ↦ Classical.choose (hg_left i.2)
  have hgf (i : D) : g i = Sum.inl (f i) := Classical.choose_spec (hg_left i.2)
  have hf : Injective f := by
    intro i j hij
    apply Subtype.ext
    exact hg (by simpa only [hgf i, hgf j, Sum.inl.injEq] using hij)
  have hft : ∀ i : D, f i ∈ t i := by
    intro i
    have hi := hgt i
    rw [hgf i] at hi
    simpa [augmented] using hi
  -- The omitted indices inject into the `d` dummy choices.
  have hcompl : #(univ \ D) ≤ d := card_sdiff_filter_exists_inl_le g hg
  have hsplit := card_sdiff_add_card_inter univ D
  have hDuniv : univ ∩ D = D := inter_eq_right.mpr (subset_univ D)
  rw [hDuniv, card_univ] at hsplit
  by_cases hd : d = 0
  · refine ⟨D, ∅, f, hf, hft, ?_, ?_⟩
    · simp only [card_empty, biUnion_empty]
      omega
    · have hcard : #D = Fintype.card ι - d := by omega
      simpa only [d] using hcard
  · obtain ⟨S, hS⟩ := exists_card_sub_card_biUnion_eq_hallDeficiency t
    -- For a positive deficiency, an attaining `S` turns weak duality into equality and forces
    -- exactly `d` indices to be omitted.
    have hweak := card_add_card_le_card_add_card_biUnion_of_partialInjective t D S f hf hft
    refine ⟨D, S, f, hf, hft, Nat.le_antisymm hweak ?_, ?_⟩
    · have hS' : #S - #(S.biUnion t) = d := by simpa only [d] using hS
      omega
    · have hcard : #D = Fintype.card ι - d := by omega
      simpa only [d] using hcard

/-- A partial injective choice can select at most `|ι| - hallDeficiency t` indices. -/
theorem card_le_card_sub_hallDeficiency_of_partialInjective
    (t : ι → Finset α) (D : Finset ι) (f : D → α) (hf : Injective f)
    (hft : ∀ i : D, f i ∈ t i) :
    #D ≤ Fintype.card ι - hallDeficiency t := by
  classical
  let d := hallDeficiency t
  by_cases hd : d = 0
  · have hcard : #D ≤ Fintype.card ι - d := by
      simpa [hd] using card_le_card (subset_univ D)
    simpa only [d] using hcard
  · obtain ⟨S, hS⟩ := exists_card_sub_card_biUnion_eq_hallDeficiency t
    have hweak := card_add_card_le_card_add_card_biUnion_of_partialInjective t D S f hf hft
    have hS' : #S - #(S.biUnion t) = d := by simpa only [d] using hS
    have hcard : #D ≤ Fintype.card ι - d := by omega
    simpa only [d] using hcard

/-- There is a largest partial system of distinct representatives, and its domain has cardinality
`|ι| - hallDeficiency t`. -/
theorem exists_partialInjective_card_eq_card_sub_hallDeficiency (t : ι → Finset α) :
    ∃ (D : Finset ι) (f : D → α), Injective f ∧ (∀ i : D, f i ∈ t i) ∧
      #D = Fintype.card ι - hallDeficiency t := by
  obtain ⟨D, S, f, hf, hft, _, hD⟩ :=
    exists_partialInjective_card_add_card_eq_card_add_card_biUnion t
  exact ⟨D, f, hf, hft, hD⟩

/-- The Hall deficiency vanishes exactly when the usual Hall cardinality inequalities hold. -/
theorem hallDeficiency_eq_zero_iff (t : ι → Finset α) :
    hallDeficiency t = 0 ↔ ∀ S : Finset ι, #S ≤ #(S.biUnion t) := by
  simpa using (hallDeficiency_le_iff t 0)

/-- Vanishing Hall deficiency is equivalent to the existence of a full system of distinct
representatives. -/
theorem hallDeficiency_eq_zero_iff_existsInjective (t : ι → Finset α) :
    hallDeficiency t = 0 ↔
      ∃ f : ι → α, Injective f ∧ ∀ i, f i ∈ t i := by
  rw [hallDeficiency_eq_zero_iff]
  exact Finset.all_card_le_biUnion_card_iff_existsInjective' t

end Finset
