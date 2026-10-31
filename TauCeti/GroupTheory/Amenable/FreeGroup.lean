/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Subgroup
public import TauCeti.GroupTheory.Amenable.Tarski
public import TauCeti.GroupTheory.FreeGroup.Paradoxical

/-!
# Free groups are not amenable

A free group on at least two generators is paradoxical for its left regular action
(`FreeGroup.paradoxical_univ`), while an amenable discrete group is not
(`TauCeti.amenable_iff_not_paradoxical_univ`). Hence such a free group is not amenable as a
discrete group. Subgroups of amenable discrete groups are amenable, so no amenable discrete group
contains such a free group.

## Main results

* `TauCeti.not_amenable_freeGroup`: a free group on at least two generators is not amenable as a
  discrete group.
* `TauCeti.not_amenable_of_injective_freeGroup`: a discrete group containing a free group on at
  least two generators is not amenable.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 1.5 and Proposition 2.2.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- A free group on at least two generators is not amenable as a discrete group. -/
theorem not_amenable_freeGroup {α : Type*} [Nontrivial α] [TopologicalSpace (FreeGroup α)]
    [DiscreteTopology (FreeGroup α)] : ¬ Amenable (FreeGroup α) :=
  fun h => amenable_iff_not_paradoxical_univ.1 h FreeGroup.paradoxical_univ

/-- A discrete group containing a free group on at least two generators, as the image of an
injective homomorphism, is not amenable. -/
theorem not_amenable_of_injective_freeGroup {α : Type*} [Nontrivial α] (φ : FreeGroup α →* G)
    (hφ : Function.Injective φ) : ¬ Amenable G := fun _ => by
  let : TopologicalSpace (FreeGroup α) := ⊥
  have : DiscreteTopology (FreeGroup α) := ⟨rfl⟩
  exact not_amenable_freeGroup (Amenable.of_injective φ hφ)

end TauCeti
