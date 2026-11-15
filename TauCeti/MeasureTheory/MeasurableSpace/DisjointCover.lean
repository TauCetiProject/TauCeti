/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Order.Disjointed

/-!
# Countable disjoint measurable covers of open sets

In a second-countable space, an open set `W` each of whose points has a neighbourhood with some
property `p` that passes to subsets is the union of a sequence of pairwise disjoint measurable sets
with property `p` (`IsOpen.exists_pairwise_disjoint_iUnion_eq`). The pieces are the disjointed
sequence of the basic open sets inside `W` with property `p`.

This is how a local property, such as local injectivity of a map with invertible derivative,
becomes a countable measurable partition, along which integrals can be split and computed piece
by piece.
-/

public section

open Set Filter Topology Function

/-- **Countable disjoint covers by small measurable pieces.** Let `p` be a property of subsets
that passes to smaller subsets and holds for `∅`. If every point of an open set `W` of a
second-countable space has a neighbourhood with property `p`, then `W` is the union of a sequence
of pairwise disjoint measurable sets with property `p`. -/
theorem IsOpen.exists_pairwise_disjoint_iUnion_eq {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X] {W : Set X}
    (hW : IsOpen W) {p : Set X → Prop} (hp : ∀ ⦃s t⦄, s ⊆ t → p t → p s) (hp₀ : p ∅)
    (hloc : ∀ x ∈ W, ∃ U ∈ 𝓝 x, p U) :
    ∃ t : ℕ → Set X, (∀ n, MeasurableSet (t n)) ∧ Pairwise (Disjoint on t) ∧
      ⋃ n, t n = W ∧ ∀ n, p (t n) := by
  -- The basic open sets inside `W` with property `p`, together with `∅`, enumerated.
  set S : Set (Set X) :=
    insert ∅ {b ∈ TopologicalSpace.countableBasis X | b ⊆ W ∧ p b}
  have hS : S.Countable :=
    ((TopologicalSpace.countable_countableBasis X).mono (sep_subset _ _)).insert ∅
  obtain ⟨s, hs⟩ := hS.exists_eq_range (insert_nonempty _ _)
  have hsS (n : ℕ) : s n ∈ S := hs ▸ mem_range_self n
  have hsW (n : ℕ) : s n ⊆ W ∧ p (s n) := by
    rcases hsS n with h | h
    · rw [h]
      exact ⟨empty_subset _, hp₀⟩
    · exact h.2
  have hsm (n : ℕ) : MeasurableSet (s n) := by
    rcases hsS n with h | h
    · rw [h]
      exact MeasurableSet.empty
    · exact (TopologicalSpace.isOpen_of_mem_countableBasis h.1).measurableSet
  refine ⟨disjointed s, MeasurableSet.disjointed hsm, disjoint_disjointed s, ?_,
    fun n ↦ hp (disjointed_subset s n) (hsW n).2⟩
  rw [iUnion_disjointed]
  refine Subset.antisymm (iUnion_subset fun n ↦ (hsW n).1) fun x hx ↦ ?_
  -- A basic open set around `x` inside `W` and inside a neighbourhood with property `p`.
  obtain ⟨U, hU, hpU⟩ := hloc x hx
  obtain ⟨b, hb, hxb, hbU⟩ := (TopologicalSpace.isBasis_countableBasis X).mem_nhds_iff.1
    (inter_mem hU (hW.mem_nhds hx))
  have hbS : b ∈ S :=
    Or.inr ⟨hb, hbU.trans inter_subset_right, hp (hbU.trans inter_subset_left) hpU⟩
  obtain ⟨n, hn⟩ := hs ▸ hbS
  exact mem_iUnion.2 ⟨n, hn ▸ hxb⟩
