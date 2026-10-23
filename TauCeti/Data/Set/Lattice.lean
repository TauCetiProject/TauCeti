/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.SetNotation

/-!
# Sets cut out by conditions on a tuple of values

A set defined by a condition `Φ` on the tuple of values of a family of functions is the union,
over the tuples satisfying `Φ`, of the fibres of the family over those tuples.

## Main results

* `TauCeti.setOf_apply_eq_biUnion_iInter`:
  `{x | Φ (g · x)} = ⋃ ε ∈ {ε | Φ ε}, ⋂ i, {x | g i x = ε i}`.
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

end TauCeti
