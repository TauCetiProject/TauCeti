/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Partition
public import TauCeti.GroupTheory.GroupAction.Orbit.Card

/-!
# Cycle lengths of a group element acting on a finite set

For a group acting on a finite set, the full cycle type of the permutation induced by an
element is the multiset of sizes of the orbits of its cyclic subgroup. The acting group itself
need not be finite. This connects permutation cycle lengths, including fixed points, to an
orbit calculation in the original group.

The comparison uses `Equiv.Perm.fullCycleType_eq_map_card_orbit` and
`TauCeti.map_card_orbit_eq_of_orbit_eq`: the permutation and the original group element have
the same integer powers acting on the carrier, hence the same orbits.
-/

public section

namespace MulAction

open scoped Classical in
/-- The cycle lengths of the permutation induced by a group element are the sizes of the
orbits of the cyclic subgroup it generates, including the singleton orbits. -/
theorem fullCycleType_toPerm_eq_map_card_orbit {G X : Type*} [Group G] [MulAction G X]
    [Fintype X] [DecidableEq X] (g : G) :
    (toPerm g : Equiv.Perm X).fullCycleType =
      (Finset.univ : Finset (orbitRel.Quotient (Subgroup.zpowers g) X)).val.map
        (fun ω => Nat.card ω.orbit) := by
  have hpow (n : ℤ) (x : X) : (toPerm g ^ n) x = g ^ n • x := by
    rw [← toPermHom_apply, ← map_zpow, toPermHom_apply, toPerm_apply]
  rw [Equiv.Perm.fullCycleType_eq_map_card_orbit]
  apply TauCeti.map_card_orbit_eq_of_orbit_eq
  intro x
  ext y
  simp only [mem_orbit_iff, Subgroup.smul_def]
  constructor
  · rintro ⟨h, hh⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
    exact ⟨⟨g ^ n, Subgroup.zpow_mem_zpowers g n⟩, by simpa [← hn, hpow] using hh⟩
  · rintro ⟨h, hh⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
    exact ⟨⟨(toPerm g : Equiv.Perm X) ^ n, Subgroup.zpow_mem_zpowers _ n⟩,
      by simpa [← hn, hpow] using hh⟩

end MulAction
