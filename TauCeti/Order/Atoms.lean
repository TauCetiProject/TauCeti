/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Atoms
public import Mathlib.Order.SupIndep
public import Mathlib.Order.ModularLattice
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Max

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
* `TauCeti.exists_isCompl_finset_sup_of_isAtom`: if a finite family of atoms has supremum `⊤`, every
  element has a complement that is the supremum of a subfamily.
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

section Complement

variable {α : Type*} [Lattice α] [BoundedOrder α] [IsModularLattice α]

/-- **Complements from a generating family of atoms.** In a bounded modular lattice, if a finite
family of atoms has supremum `⊤`, then every element has a complement that is the supremum of a
subfamily: a subfamily maximal among those whose supremum is disjoint from the element. -/
theorem exists_isCompl_finset_sup_of_isAtom {ι : Type*} [Fintype ι] {N : ι → α}
    (hN : ∀ i, IsAtom (N i)) (htop : Finset.univ.sup N = ⊤) (x : α) :
    ∃ s : Finset ι, IsCompl x (s.sup N) := by
  classical
  obtain ⟨s, hs, hmax⟩ :=
    (Finset.univ.powerset.filter fun t ↦ Disjoint x (t.sup N)).exists_max_image
      Finset.card ⟨∅, by simp⟩
  have hdis : Disjoint x (s.sup N) := (Finset.mem_filter.1 hs).2
  refine ⟨s, hdis, codisjoint_iff.2 (eq_top_iff.2 ?_)⟩
  rw [← htop]
  refine Finset.sup_le fun j _ ↦ ?_
  by_contra hj
  -- Otherwise `N j` could be added to the subfamily, contradicting maximality.
  have hdj : Disjoint (N j) (x ⊔ s.sup N) := (hN j).not_le_iff_disjoint.1 hj
  have hjs : j ∉ s := fun h ↦ hj (le_sup_of_le_right (Finset.le_sup h))
  have hins : Disjoint x ((insert j s).sup N) := by
    rw [Finset.sup_insert, sup_comm]
    exact hdis.disjoint_sup_right_of_disjoint_sup_left hdj.symm
  have := hmax (insert j s)
    (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), hins⟩)
  rw [Finset.card_insert_of_notMem hjs] at this
  lia

end Complement

end TauCeti
