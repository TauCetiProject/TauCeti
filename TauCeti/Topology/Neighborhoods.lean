/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Neighborhoods

/-!
# Neighbourhoods of finite sets under subadditive set functions

Let `ν : Set α → ℕ∞` be monotone, zero on `∅` and subadditive, `ν (A ∪ B) ≤ ν A + ν B`, such as
an index in the sense of Lusternik and Schnirelmann. If every point of a set `K` has a
neighbourhood of index at most `1`, then `K` has an open neighbourhood whose index is at most the
number of points of `K` (`Set.exists_isOpen_superset_le_encard`): for finite `K`, take the union
of the interiors of those neighbourhoods; for infinite `K`, take `univ`.

## Main results

* `Set.exists_isOpen_superset_le_encard`: a set whose points have neighbourhoods of index at most
  `1` has an open neighbourhood of index at most its cardinality.
-/

public section

open Set Topology

variable {α : Type*} [TopologicalSpace α]

/-- Let `ν : Set α → ℕ∞` be monotone, zero on `∅` and subadditive. A set `K` whose points each
have a neighbourhood of index at most `1` has an open neighbourhood whose index is at most the
cardinality of `K`. -/
theorem Set.exists_isOpen_superset_le_encard (K : Set α)
    {ν : Set α → ℕ∞} (hmono : Monotone ν) (hempty : ν ∅ = 0)
    (hunion : ∀ A B, ν (A ∪ B) ≤ ν A + ν B) (hloc : ∀ x ∈ K, ∃ V ∈ 𝓝 x, ν V ≤ 1) :
    ∃ U, IsOpen U ∧ K ⊆ U ∧ ν U ≤ K.encard := by
  obtain hK | hK := K.finite_or_infinite
  · induction K, hK using Set.Finite.induction_on with
    | empty => exact ⟨∅, isOpen_empty, subset_rfl, by simp [hempty]⟩
    | @insert a s ha _ ih =>
      obtain ⟨U, hUo, hsU, hU⟩ := ih fun x hx ↦ hloc x (mem_insert_of_mem a hx)
      obtain ⟨V, hV, hνV⟩ := hloc a (mem_insert a s)
      refine ⟨interior V ∪ U, isOpen_interior.union hUo,
        insert_subset (Or.inl (mem_interior_iff_mem_nhds.2 hV)) (hsU.trans subset_union_right), ?_⟩
      calc ν (interior V ∪ U) ≤ ν (interior V) + ν U := hunion _ _
        _ ≤ 1 + s.encard := add_le_add ((hmono interior_subset).trans hνV) hU
        _ = (insert a s).encard := by rw [encard_insert_of_notMem ha, add_comm]
  · exact ⟨univ, isOpen_univ, subset_univ K, by simp [hK.encard_eq]⟩
