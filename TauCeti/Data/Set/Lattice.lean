/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.SetNotation
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Finset.Range

/-!
# Sets cut out by conditions on a tuple of values

A set defined by a condition `Φ` on the tuple of values of a family of functions is the union,
over the tuples satisfying `Φ`, of the fibres of the family over those tuples.

For a strictly monotone reindexing `σ` of pairwise disjoint sets `B`, the union `⋃ j, B (σ j)`
splits into the earlier sets, the `k`-th set and the later sets, and these pieces are disjoint.

## Main results

* `TauCeti.setOf_apply_eq_biUnion_iInter`:
  `{x | Φ (g · x)} = ⋃ ε ∈ {ε | Φ ε}, ⋂ i, {x | g i x = ε i}`.
* `TauCeti.iUnion_comp_eq_union_of_pairwise_disjoint`: the decomposition of `⋃ j, B (σ j)` and
  the disjointness of its three pieces.
-/

public section

open Function Set

namespace TauCeti

/-- The set of points where a family of functions `g i` satisfies a condition `Φ` on its tuple of
values is the union, over the tuples `ε` satisfying `Φ`, of the sets where `g i = ε i` for all
`i`. -/
theorem setOf_apply_eq_biUnion_iInter {α β ι : Type*} (g : ι → α → β) (Φ : (ι → β) → Prop) :
    {x | Φ fun i => g i x} = ⋃ ε ∈ {ε | Φ ε}, ⋂ i, {x | g i x = ε i} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
  exact ⟨fun h => ⟨_, h, fun _ => rfl⟩, fun ⟨ε, hε, h⟩ => (funext h).symm ▸ hε⟩

/-- For a strictly monotone `σ` and pairwise disjoint sets `B`, the union `⋃ j, B (σ j)` splits
into the earlier sets, the `k`-th set and the later sets, and these three pieces are disjoint. -/
theorem iUnion_comp_eq_union_of_pairwise_disjoint {α : Type*} {B : ℕ → Set α}
    (hB : Pairwise (Disjoint on B)) {σ : ℕ → ℕ} (hσ : StrictMono σ) (k : ℕ) :
    ⋃ j, B (σ j) = (⋃ i ∈ Finset.range k, B (σ i)) ∪ (B (σ k) ∪ ⋃ i, ⋃ (_ : k < i), B (σ i)) ∧
    Disjoint (⋃ i ∈ Finset.range k, B (σ i)) (B (σ k) ∪ ⋃ i, ⋃ (_ : k < i), B (σ i)) ∧
    Disjoint (B (σ k)) (⋃ i, ⋃ (_ : k < i), B (σ i)) := by
  have hdisj (i i' : ℕ) (hii' : i ≠ i') : Disjoint (B (σ i)) (B (σ i')) :=
    hB (hσ.injective.ne hii')
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [mem_union, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨i, hi⟩
      rcases lt_trichotomy i k with hik | rfl | hik
      · exact Or.inl ⟨i, hik, hi⟩
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr ⟨i, hik, hi⟩)
    · rintro (⟨i, -, hi⟩ | hi | ⟨i, -, hi⟩)
      exacts [⟨i, hi⟩, ⟨k, hi⟩, ⟨i, hi⟩]
  · simp only [disjoint_union_right, disjoint_iUnion_left, disjoint_iUnion_right,
      Finset.mem_range]
    exact ⟨fun i hi ↦ hdisj i k hi.ne, fun i hi i' hi' ↦ hdisj i' i (by omega)⟩
  · simp only [disjoint_iUnion_right]
    exact fun i hi ↦ hdisj k i hi.ne

end TauCeti
