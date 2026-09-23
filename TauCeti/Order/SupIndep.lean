/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.SupIndep

/-!
# Finite supremum-independent families

This file develops the API for finite supremum-independent families in bounded lattices.

## Main declarations

* `Finset.SupIndep.isCompl_sup_erase`: a member of an independent finite family spanning a
  bounded lattice is complemented by the supremum of the other members.
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
