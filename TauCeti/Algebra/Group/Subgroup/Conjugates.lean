/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Conjugate subgroups

This file packages the set of conjugates of a subgroup.  A conjugate of `H ≤ G` is the image
of `H` under the inner automorphism `MulAut.conj g` for some `g : G`.

## Main definitions

* `TauCeti.conjugateSubgroups`: the set of conjugates of a subgroup.
-/

public section

namespace TauCeti

/-- The set of conjugates of a subgroup by elements of its ambient group. -/
def conjugateSubgroups {G : Type*} [Group G] (H : Subgroup G) : Set (Subgroup G) :=
  Set.range fun g : G ↦ H.map (MulAut.conj g)

/-- Membership in `conjugateSubgroups H` means being obtained from `H` by conjugation. -/
theorem mem_conjugateSubgroups_iff {G : Type*} [Group G] {H H' : Subgroup G} :
    H' ∈ conjugateSubgroups H ↔ ∃ g : G, H.map (MulAut.conj g) = H' :=
  Iff.rfl

/-- A group isomorphism identifies the sets of conjugates of corresponding subgroups. -/
def conjugateSubgroupsEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) :
    conjugateSubgroups H ≃ conjugateSubgroups (H.map e.toMonoidHom) :=
  e.mapSubgroup.subtypeEquiv fun J ↦ by
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨e g, (Subgroup.map_map_conj H e.toMonoidHom g).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨e.symm g, ?_⟩
      apply e.mapSubgroup.injective
      change (H.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom =
        J.map e.toMonoidHom
      have hmap : (H.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom =
          (H.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
        simpa only [MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using
          Subgroup.map_map_conj H e.toMonoidHom (e.symm g)
      exact hmap.trans hg

end TauCeti
