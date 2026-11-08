/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Order.SetNotation

/-!
# Sets cut out by conditions on a tuple of values

A set defined by a condition `Φ` on the tuple of values of a family of functions is the union,
over the tuples satisfying `Φ`, of the fibres of the family over those tuples.

If a family in a complete lattice indexed by `ℕ` is eventually above its value at `j₀`, then the
infimum of its first members is the infimum of all of them.

## Main results

* `TauCeti.setOf_apply_eq_biUnion_iInter`:
  `{x | Φ (g · x)} = ⋃ ε ∈ {ε | Φ ε}, ⋂ i, {x | g i x = ε i}`.
* `TauCeti.iInf_mem_range_succ_eq_iInf`: for a family with `S j₀ ≤ S j` for all `j ≥ j₀`, the
  infimum of the first `j₀ + 1` members is the infimum of all members.
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

/-- If `S j₀ ≤ S j` for all `j ≥ j₀`, then the infimum of the first `j₀ + 1` members of the family
`S` is the infimum of all members. -/
theorem iInf_mem_range_succ_eq_iInf {α : Type*} [CompleteLattice α] (S : ℕ → α) (j₀ : ℕ)
    (hS : ∀ j, j₀ ≤ j → S j₀ ≤ S j) : ⨅ j ∈ Finset.range (j₀ + 1), S j = ⨅ j, S j := by
  refine le_antisymm (le_iInf fun j ↦ ?_) (le_iInf₂ fun j _ ↦ iInf_le S j)
  rcases le_total j j₀ with h | h
  · exact iInf₂_le j (Finset.mem_range.2 (by omega))
  · exact (iInf₂_le j₀ (Finset.mem_range.2 (by omega))).trans (hS j h)

end TauCeti
