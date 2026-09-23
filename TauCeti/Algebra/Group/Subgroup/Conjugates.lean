/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import TauCeti.Algebra.Group.Subgroup.Map

/-!
# Conjugate subgroups

This file packages the set of conjugates of a subgroup.  A conjugate of `H ≤ G` is the image
of `H` under the inner automorphism `MulAut.conj g` for some `g : G`.

## Main definitions

* `MulAction.orbit (ConjAct G) H`: the set of conjugates of a subgroup `H`.
-/

public section

namespace TauCeti

open scoped Pointwise

/-- Membership in the conjugacy orbit of `H` means being obtained from `H` by conjugation. -/
theorem mem_conjugateSubgroups_iff {G : Type*} [Group G] {H H' : Subgroup G} :
    H' ∈ MulAction.orbit (ConjAct G) H ↔ ∃ g : G, H.map (MulAut.conj g) = H' := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨ConjAct.toConjAct g, rfl⟩

/-- A group isomorphism identifies the sets of conjugates of corresponding subgroups. -/
def conjugateSubgroupsEquiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) :
    MulAction.orbit (ConjAct G) H ≃
      MulAction.orbit (ConjAct G') (H.map e.toMonoidHom) :=
  e.mapSubgroup.subtypeEquiv fun J ↦ by
    constructor
    · intro h
      obtain ⟨g, hg⟩ := mem_conjugateSubgroups_iff.mp h
      apply mem_conjugateSubgroups_iff.mpr
      refine ⟨e g, ?_⟩
      change H.map (MulAut.conj g).toMonoidHom = J at hg
      change (H.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom = J.map e.toMonoidHom
      have hmap : (H.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom =
          (H.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom := by
        simpa only [show e.toMonoidHom g = e g from rfl] using
          (Subgroup.map_map_conj H e.toMonoidHom g).symm
      exact hmap.trans (congrArg (·.map e.toMonoidHom) hg)
    · intro h
      obtain ⟨g, hg⟩ := mem_conjugateSubgroups_iff.mp h
      apply mem_conjugateSubgroups_iff.mpr
      refine ⟨e.symm g, ?_⟩
      apply e.mapSubgroup.injective
      change (H.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom =
        J.map e.toMonoidHom
      change (H.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = J.map e.toMonoidHom at hg
      have heg : e.toMonoidHom (e.symm g) = g := e.apply_symm_apply g
      have hmap : (H.map (MulAut.conj (e.symm g)).toMonoidHom).map e.toMonoidHom =
          (H.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
        simpa only [heg] using Subgroup.map_map_conj H e.toMonoidHom (e.symm g)
      exact hmap.trans hg

end TauCeti
