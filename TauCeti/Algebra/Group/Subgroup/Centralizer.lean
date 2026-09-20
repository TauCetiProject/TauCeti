/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Subgroup.centralizer` occurs in the statement below.
public import Mathlib.GroupTheory.Subgroup.Centralizer
-- `Commute.units_val_iff` transports commutation between units and their values.
public import Mathlib.Algebra.Group.Commute.Units

/-!
# Centralizers and maximal commutative subgroups

Centralizers of a group of units are computed on the underlying monoid: a unit centralizes another
exactly when their values commute. Mathlib has both halves —
`Subgroup.mem_centralizer_singleton_iff` turns membership into an equation, and
`Commute.units_val_iff` transports that equation between `Mˣ` and `M` — but not their combination,
which is the form every concrete centralizer computation in a matrix group starts from.

## Main results

* `TauCeti.mem_centralizer_singleton_iff_commute_val`: a unit lies in the centralizer of a unit `g`
  exactly when the two commute as elements of the monoid.
* `Subgroup.mem_centralizer_singleton_iff_inv_mul_mul_eq`: in a group, centralizing an element is
  fixing it under conjugation.
* `Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative`: a self-centralizing subgroup is
  maximal among commutative subgroups.
-/

public section

namespace TauCeti

/-- Membership in the centralizer of a unit `g`, read on the underlying monoid. -/
theorem mem_centralizer_singleton_iff_commute_val {M : Type*} [Monoid M] {g h : Mˣ} :
    h ∈ Subgroup.centralizer {g} ↔ Commute (g : M) (h : M) :=
  ⟨fun hh => Commute.units_val_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hh).symm,
    fun hh => Subgroup.mem_centralizer_singleton_iff.mpr (Commute.units_val_iff.mp hh).symm⟩

end TauCeti

namespace Subgroup

/-- **Centralizing an element of a group is fixing it under conjugation.**  This is the
conjugation form of `Subgroup.mem_centralizer_singleton_iff`, which states the same membership as
a commutation. -/
theorem mem_centralizer_singleton_iff_inv_mul_mul_eq {G : Type*} [Group G] {a g : G} :
    g ∈ centralizer ({a} : Set G) ↔ g⁻¹ * a * g = a := by
  rw [mem_centralizer_singleton_iff, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]

/-- A self-centralizing subgroup is maximal among commutative subgroups. -/
theorem eq_of_centralizer_eq_self_of_le_of_isMulCommutative {G : Type*} [Group G]
    {S H : Subgroup G} (hS : Subgroup.centralizer (S : Set G) = S) [IsMulCommutative H]
    (hle : S ≤ H) :
    H = S :=
  le_antisymm
    (by
      rw [← hS]
      exact (Subgroup.le_centralizer (H := H)).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle)))
    hle

end Subgroup
