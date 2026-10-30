/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Content
public import TauCeti.GroupTheory.Amenable.Subgroup
public import TauCeti.GroupTheory.FreeGroup.Paradoxical

/-!
# Amenable discrete groups are not paradoxical

An amenable discrete group carries a left-invariant finitely additive probability on all of its
subsets (`TauCeti.Amenable.exists_invariantContent`). Such a probability takes equal values on
equidecomposable sets, so it rules out a paradoxical decomposition of the group for its left regular
action. This is the easy half of Tarski's alternative.

Since a free group on at least two generators is paradoxical
(`TauCeti.paradoxical_univ_freeGroup`), it is not amenable as a discrete group. Subgroups of
amenable discrete groups are amenable, so no amenable discrete group contains such a free group.

## Main results

* `TauCeti.Amenable.not_paradoxical_univ`: an amenable discrete group is not paradoxical for its
  left regular action.
* `TauCeti.not_amenable_freeGroup`: a free group on at least two generators is not amenable as a
  discrete group.
* `TauCeti.not_amenable_of_injective_freeGroup`: a discrete group containing a free group on at
  least two generators is not amenable.

## References

* A. Garrido, *An introduction to amenable groups*, Corollary 1.3, Proposition 1.5 and
  Proposition 2.2.
-/

public section

open Set

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- An amenable discrete group is not paradoxical for its left regular action. -/
theorem Amenable.not_paradoxical_univ [Amenable G] : ¬ Paradoxical G (univ : Set G) := by
  obtain ⟨ν, hν₁, hν⟩ := Amenable.exists_invariantContent (G := G)
  exact not_paradoxical_univ_of_addContent hν hν₁

/-- A free group on at least two generators is not amenable as a discrete group. -/
theorem not_amenable_freeGroup {α : Type*} [Nontrivial α] [TopologicalSpace (FreeGroup α)]
    [DiscreteTopology (FreeGroup α)] : ¬ Amenable (FreeGroup α) :=
  fun _ => Amenable.not_paradoxical_univ (paradoxical_univ_freeGroup (α := α))

/-- A discrete group containing a free group on at least two generators, as the image of an
injective homomorphism, is not amenable. -/
theorem not_amenable_of_injective_freeGroup {α : Type*} [Nontrivial α] (φ : FreeGroup α →* G)
    (hφ : Function.Injective φ) : ¬ Amenable G := fun _ => by
  let : TopologicalSpace (FreeGroup α) := ⊥
  have : DiscreteTopology (FreeGroup α) := ⟨rfl⟩
  exact not_amenable_freeGroup (Amenable.of_injective φ hφ)

end TauCeti
