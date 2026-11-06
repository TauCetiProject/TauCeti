/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Atoms
public import Mathlib.Order.SupIndep

/-!
# Finite atom decompositions in a complemented modular lattice

In a bounded modular lattice that is complemented and satisfies the descending chain condition,
every element is the supremum of a finite independent family of atoms: split off an atom `a` of
the element `x`, meet a complement of `a` with `x`, which the modular law makes a complement of
`a` inside `x`, and recurse on that strictly smaller element.

Mathlib proves the corresponding statement for a *complete* lattice, where complementedness gives
atomisticity and the decomposition is an arbitrary supremum
(`exists_sSupIndep_of_sSup_atoms`, made finite by `WellFoundedGT.finite_of_sSupIndep`). The
descending chain condition makes the family finite from the start, which is what lattices without
arbitrary suprema — lattices of subobjects closed under finite meets and joins only — need.

## Main declarations

* `TauCeti.exists_finset_isAtom_sup_eq`: in a complemented modular lattice satisfying the
  descending chain condition, every element is the supremum of a finite independent family of
  atoms.
-/

public section

namespace TauCeti

variable {L : Type*} [Lattice L] [BoundedOrder L] [IsModularLattice L] [ComplementedLattice L]
  [WellFoundedLT L]

/-- **Finite atom decomposition.** In a bounded modular lattice which is complemented and
satisfies the descending chain condition, every element is the supremum of a finite independent
family of atoms. This is semisimplicity for a lattice of subobjects: `x` is the direct sum of
finitely many simple subobjects. -/
theorem exists_finset_isAtom_sup_eq (x : L) :
    ∃ s : Finset L, (∀ a ∈ s, IsAtom a) ∧ s.SupIndep id ∧ s.sup id = x := by
  classical
  induction x using WellFoundedLT.induction with
  | ind x ih =>
    obtain rfl | ⟨a, ha, hax⟩ := eq_bot_or_exists_atom_le x
    · exact ⟨∅, by simp⟩
    obtain ⟨b, hb⟩ := exists_isCompl a
    -- the meet of `x` with a complement of `a` is a complement of `a` inside `x`
    have hdisj : Disjoint a (b ⊓ x) := hb.disjoint.mono_right inf_le_left
    have hlt : b ⊓ x < x :=
      inf_le_right.lt_of_ne fun h ↦ ha.1 <| hdisj.eq_bot_of_le <| hax.trans h.ge
    obtain ⟨s, hatom, hindep, hssup⟩ := ih _ hlt
    refine ⟨insert a s, (Finset.forall_mem_insert _ _ _).2 ⟨ha, hatom⟩,
      hindep.insert (hssup ▸ hdisj), ?_⟩
    simp [hssup, ← sup_inf_assoc_of_le _ hax, hb.sup_eq_top]

end TauCeti
