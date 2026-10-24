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

For the left-regular action of a finite group on itself every such orbit is a right coset of the
cyclic subgroup, so left multiplication by an element of order `d` in a group of order `m` is a
product of `m / d` disjoint `d`-cycles (`MulAction.fullCycleType_toPerm_self`). The raw cycle
type omits fixed points: for `g ≠ 1` it is the same multiset (`MulAction.cycleType_toPerm_self`),
while for `g = 1` the full cycle type is `1 ^ m` and the raw cycle type is empty.
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

/-- **The cycle type of the left-regular action.** In a finite group of order `m`, left
multiplication by an element `g` of order `d` is a product of `m / d` disjoint `d`-cycles: its full
cycle type, which counts fixed points as cycles of length one, is `d ^ (m / d)`. -/
@[simp]
theorem fullCycleType_toPerm_self {G : Type*} [Group G] [Fintype G] [DecidableEq G] (g : G) :
    (toPerm g : Equiv.Perm G).fullCycleType =
      Multiset.replicate (Fintype.card G / orderOf g) (orderOf g) := by
  -- Every orbit of `zpowers g` is a right coset of it, of size `orderOf g`; the sizes sum to `m`.
  have hmem : ∀ b ∈ (toPerm g : Equiv.Perm G).fullCycleType, b = orderOf g := by
    intro b hb
    rw [fullCycleType_toPerm_eq_map_card_orbit, Multiset.mem_map] at hb
    obtain ⟨ω, -, rfl⟩ := hb
    obtain ⟨x, rfl⟩ := Quotient.mk_surjective ω
    rw [orbitRel.Quotient.orbit_mk, orbit, Nat.card_range_of_injective, Nat.card_eq_fintype_card,
      Fintype.card_zpowers]
    exact fun a b h ↦ Subtype.ext (mul_right_cancel h)
  have hs := Multiset.eq_replicate_card.2 hmem
  have hsum := Equiv.Perm.sum_fullCycleType (toPerm g : Equiv.Perm G)
  rw [hs, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hs, ← hsum, Nat.mul_div_cancel _ (orderOf_pos g)]

/-- **The raw cycle type of the left-regular action.** In a finite group of order `m`, left
multiplication by an element `g ≠ 1` of order `d` has no fixed points, so its cycle type is
`d ^ (m / d)`. (Left multiplication by `1` is the identity, whose cycle type is empty.) -/
theorem cycleType_toPerm_self {G : Type*} [Group G] [Fintype G] [DecidableEq G] {g : G}
    (hg : g ≠ 1) :
    (toPerm g : Equiv.Perm G).cycleType =
      Multiset.replicate (Fintype.card G / orderOf g) (orderOf g) := by
  have h2 : 2 ≤ orderOf g := by
    have := orderOf_pos g
    have : orderOf g ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
    omega
  rw [← Equiv.Perm.filter_fullCycleType_eq_cycleType, fullCycleType_toPerm_self,
    Multiset.filter_eq_self.2 fun b hb ↦ (Multiset.eq_of_mem_replicate hb) ▸ h2]

end MulAction
