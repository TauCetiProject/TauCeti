/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Basic
import TauCeti.GroupTheory.SpecificGroups.KleinFour

/-!
# The Klein four reference permutation group in degree four

The reference subgroup of `4T2` is Mathlib's `alternatingGroup.kleinFour (Fin 4)`, the normal
subgroup of `A₄` made of the identity and the three double transpositions, viewed inside
`Equiv.Perm (Fin 4)`. We record that it is a Klein four-group, so that every permutation group
with label `4T2` is one. The converse for transitive subgroups of `S₄` is
`TauCeti.transitiveGroupLabel_four_one_iff_isKleinFour`, in
`TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Order`.

## Main declarations

* `TauCeti.isKleinFour_referenceSubgroup_four_one`: the reference subgroup of `4T2` is a Klein
  four-group.
* `TauCeti.TransitiveGroupLabel.isKleinFour_four_one`: a permutation group with label `4T2` is a
  Klein four-group.
-/

public section

open Equiv Equiv.Perm

namespace TauCeti

/-- The reference subgroup of `4T2` is a Klein four-group. -/
instance isKleinFour_referenceSubgroup_four_one :
    IsKleinFour (referenceSubgroup 4 ⟨1, by simp⟩) := by
  have := alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
  rw [referenceSubgroup_four_one]
  exact ((alternatingGroup.kleinFour (Fin 4)).equivMapOfInjective
    (alternatingGroup (Fin 4)).subtype (alternatingGroup (Fin 4)).subtype_injective).isKleinFour

/-- Every permutation group with label `4T2` is a Klein four-group. -/
theorem TransitiveGroupLabel.isKleinFour_four_one {G : Subgroup (Perm (Fin 4))}
    (h : TransitiveGroupLabel (⟨1, by simp⟩ : TransitiveGroupIndex 4) G) : IsKleinFour G := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv_referenceSubgroup
  exact e.symm.isKleinFour

end TauCeti
