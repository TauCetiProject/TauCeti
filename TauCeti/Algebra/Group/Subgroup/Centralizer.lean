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
public import Mathlib.Order.Zorn
import TauCeti.Algebra.Group.Torsion

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
* `Subgroup.eq_of_centralizer_eq_self_of_le_of_isMulCommutative`: a self-centralizing subgroup is
  maximal among commutative subgroups.
* `Subgroup.exists_maximal_isMulCommutative`: every commutative subgroup lies in a maximal one.
* `Subgroup.centralizer_zpow_eq` and `Subgroup.centralizer_pow_eq`: nonzero powers have the same
  centralizer as their base in groups with unique roots.
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

/-- Every abelian subgroup is contained in a maximal abelian subgroup. -/
theorem exists_maximal_isMulCommutative {G : Type*} [Group G] (H : Subgroup G)
    (hH : IsMulCommutative H) :
    ∃ M : Subgroup G, H ≤ M ∧ Maximal (fun K : Subgroup G => IsMulCommutative K) M := by
  classical
  apply zorn_le_nonempty₀ {K : Subgroup G | IsMulCommutative K} ?_ H hH
  intro c hc hcc y hy
  have : ∀ K : c, IsMulCommutative (K : Subgroup G) := fun K => hc K.2
  have hcomm : IsMulCommutative (sSup c : Subgroup G) := by
    rw [sSup_eq_iSup']
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    exact Subgroup.isMulCommutative_iSup hcc.directedOn.directed_val
  exact ⟨sSup c, hcomm, fun K hK => le_sSup hK⟩

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

namespace Subgroup

variable {G : Type*} [Group G] [HasUniqueRoots G] (x : G)

/-- Taking a nonzero integer power does not change the centralizer of an element in a group
with unique roots. -/
@[simp]
theorem centralizer_zpow_eq {n : ℤ} (hn : n ≠ 0) :
    centralizer {x ^ n} = centralizer {x} := by
  ext y
  simp only [mem_centralizer_singleton_iff, ← commute_iff_eq, Commute.zpow_right_iff hn]

/-- Taking a nonzero natural power does not change the centralizer of an element in a group
with unique roots. -/
@[simp]
theorem centralizer_pow_eq {n : ℕ} (hn : n ≠ 0) :
    centralizer {x ^ n} = centralizer {x} := by
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  simpa only [zpow_natCast] using centralizer_zpow_eq x hn'

end Subgroup
