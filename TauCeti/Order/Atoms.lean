/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Atoms
public import TauCeti.Order.SupIndep

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
satisfies the descending chain condition, every element is the supremum of a finite family of
atoms, pairwise independent. This is semisimplicity for a lattice of subobjects: `x` is the direct
sum of finitely many simple subobjects. -/
theorem exists_finset_isAtom_sup_eq (x : L) :
    ∃ s : Finset L, (∀ a ∈ s, IsAtom a) ∧ s.SupIndep id ∧ s.sup id = x := by
  classical
  induction x using WellFoundedLT.induction with
  | ind x ih =>
    rcases eq_or_ne x ⊥ with rfl | hx
    · exact ⟨∅, by simp, Finset.supIndep_empty _, by simp⟩
    obtain ⟨a, ha, hax⟩ := (eq_bot_or_exists_atom_le x).resolve_left hx
    obtain ⟨b, hb⟩ := exists_isCompl a
    -- the meet of `x` with a complement of `a` is a complement of `a` inside `x`
    have hinf : a ⊓ (b ⊓ x) = ⊥ :=
      le_bot_iff.1 <| calc
        a ⊓ (b ⊓ x) ≤ a ⊓ b := inf_le_inf_left _ inf_le_left
        _ = ⊥ := hb.disjoint.eq_bot
    have hsup : a ⊔ b ⊓ x = x := by
      rw [← sup_inf_assoc_of_le _ hax, hb.codisjoint.eq_top, top_inf_eq]
    have hlt : b ⊓ x < x := by
      refine inf_le_right.lt_of_ne fun h ↦ ha.1 ?_
      have hbot : a ⊓ x = ⊥ := h ▸ hinf
      rwa [inf_eq_left.2 hax] at hbot
    obtain ⟨s, hatom, hindep, hssup⟩ := ih _ hlt
    refine ⟨insert a s, ?_, hindep.insert ?_, ?_⟩
    · exact fun c hc ↦ (Finset.mem_insert.1 hc).elim (fun h ↦ h ▸ ha) (hatom c)
    · rw [hssup]
      exact disjoint_iff.2 hinf
    · rw [Finset.sup_insert, hssup, id_eq, hsup]

end TauCeti
