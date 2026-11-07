/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.SetNotation

/-!
# Sets cut out by conditions on a tuple of values

A set defined by a condition `Φ` on the tuple of values of a family of functions is the union,
over the tuples satisfying `Φ`, of the fibres of the family over those tuples.

If a family of sets indexed by `ℕ` is eventually constant, then the intersection of its first
members is the intersection of all of them.

## Main results

* `TauCeti.setOf_apply_eq_biUnion_iInter`:
  `{x | Φ (g · x)} = ⋃ ε ∈ {ε | Φ ε}, ⋂ i, {x | g i x = ε i}`.
* `TauCeti.iInter_mem_range_succ_eq_iInter`: for an eventually constant family, the intersection of
  the first `j₀ + 1` members is the intersection of all members.
-/

public section

open Set

namespace TauCeti

/-- The set of points where a family of functions `g i` satisfies a condition `Φ` on its tuple of
values is the union, over the tuples `ε` satisfying `Φ`, of the sets where `g i = ε i` for all
`i`. -/
theorem setOf_apply_eq_biUnion_iInter {α β ι : Type*} (g : ι → α → β) (Φ : (ι → β) → Prop) :
    {x | Φ fun i => g i x} = ⋃ ε ∈ {ε | Φ ε}, ⋂ i, {x | g i x = ε i} := by
  ext x
  simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, exists_prop]
  exact ⟨fun h => ⟨_, h, fun _ => rfl⟩, fun ⟨ε, hε, h⟩ => (funext h).symm ▸ hε⟩

/-- If a family of sets is eventually constant from index `j₀`, then the intersection of its first
`j₀ + 1` members is the intersection of all members. -/
theorem iInter_mem_range_succ_eq_iInter {α : Type*} (S : ℕ → Set α) (j₀ : ℕ)
    (hS : ∀ j, j₀ ≤ j → S j = S j₀) : ⋂ j ∈ Finset.range (j₀ + 1), S j = ⋂ j, S j := by
  refine subset_antisymm (fun q hq ↦ mem_iInter.2 fun j ↦ ?_)
    fun q hq ↦ mem_iInter₂.2 fun j _ ↦ mem_iInter.1 hq j
  rcases le_total j j₀ with h | h
  · exact mem_iInter₂.1 hq j (Finset.mem_range.2 (by omega))
  · rw [hS j h]
    exact mem_iInter₂.1 hq j₀ (Finset.mem_range.2 (by omega))

end TauCeti
