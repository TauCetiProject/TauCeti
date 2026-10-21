/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.SupIndep

/-!
# Supremum-independent families

This file develops the API for supremum-independent families. The complement results turn an
independent spanning family into complementary summands, enabling projections or retractions onto
individual members.

## Main declarations

* `Finset.SupIndep.isCompl_sup_erase`: a member of an independent finite family spanning a
  bounded lattice is complemented by the supremum of the other members.
* `iSupIndep.isCompl_biSup_ne`: a member of an independent family spanning a complete lattice is
  complemented by the supremum of the other members.
* `iSupIndep.sum_elim`: in a modular lattice, two independent families with disjoint suprema
  combine into an independent family indexed by the sum type.
-/

public section

/-- In a bounded lattice, a member of an independent finite family whose supremum is `⊤` is
complemented by the supremum of the remaining members. -/
theorem Finset.SupIndep.isCompl_sup_erase {ι L : Type*} [Lattice L] [BoundedOrder L]
    [DecidableEq ι] {s : Finset ι} {f : ι → L} (hind : s.SupIndep f) (htop : s.sup f = ⊤)
    {i : ι} (hi : i ∈ s) : IsCompl (f i) ((s.erase i).sup f) where
  disjoint := Finset.supIndep_iff_disjoint_erase.1 hind i hi
  codisjoint := codisjoint_iff.2 <| by
    rw [← Finset.sup_insert, Finset.insert_erase hi, htop]

/-- In a complete lattice, a member of an independent family whose supremum is `⊤` is
complemented by the supremum of the remaining members. -/
theorem iSupIndep.isCompl_biSup_ne {ι L : Type*} [CompleteLattice L] {f : ι → L}
    (hind : iSupIndep f) (htop : ⨆ i, f i = ⊤) (i : ι) :
    IsCompl (f i) (⨆ j, ⨆ (_ : j ≠ i), f j) where
  disjoint := hind i
  codisjoint := codisjoint_iff.2 <| by
    rw [← iSup_split_single, htop]

/-- In a complete modular lattice, two independent families whose suprema are disjoint combine into
an independent family indexed by the sum of their index types. -/
theorem iSupIndep.sum_elim {ι κ L : Type*} [CompleteLattice L] [IsModularLattice L] {f : ι → L}
    {g : κ → L} (hf : iSupIndep f) (hg : iSupIndep g) (hfg : Disjoint (⨆ i, f i) (⨆ j, g j)) :
    iSupIndep (Sum.elim f g) := by
  rw [iSupIndep_def]
  rintro (i | j) <;> simp only [iSup_sum, Sum.elim_inl, Sum.elim_inr, ne_eq, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, not_false_eq_true, iSup_pos]
  · refine (hf i).disjoint_sup_right_of_disjoint_sup_left (hfg.mono_left ?_)
    exact sup_le (le_iSup f i) (iSup₂_le fun i' _ ↦ le_iSup f i')
  · rw [sup_comm]
    refine (hg j).disjoint_sup_right_of_disjoint_sup_left (hfg.symm.mono_left ?_)
    exact sup_le (le_iSup g j) (iSup₂_le fun j' _ ↦ le_iSup g j')
