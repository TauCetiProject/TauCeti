/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Partition
public import TauCeti.GroupTheory.GroupAction.Orbit.Card
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Cycle lengths of a group element acting on a finite set

For a group acting on a finite set, the full cycle type of the permutation induced by an
element is the multiset of sizes of the orbits of its cyclic subgroup. The acting group itself
need not be finite. This connects permutation cycle lengths, including fixed points, to an
orbit calculation in the original group.

The comparison uses `Equiv.Perm.fullCycleType_eq_map_card_orbit` and
`TauCeti.map_card_orbit_eq_of_orbit_eq`: the permutation and the original group element have
the same integer powers acting on the carrier, hence the same orbits.

For a free action every such orbit is a copy of the cyclic subgroup, so all cycles of `g` have
length `orderOf g`. In particular, left multiplication by an element of order `d` in a finite group
of order `m` has `m / d` cycles, each of length `d`.
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

/-- **The cycle type of a free action.** If `G` acts freely on a finite set `X`, the permutation
induced by `g` has `Fintype.card X / orderOf g` cycles, all of length `orderOf g`. For the
left-regular action of a finite group on itself this says that left multiplication by an element
of order `d` in a group of order `m` is a product of `m / d` disjoint `d`-cycles. -/
theorem fullCycleType_toPerm_of_isCancelSMul {G X : Type*} [Group G] [MulAction G X]
    [IsCancelSMul G X] [Fintype X] [DecidableEq X] (g : G) :
    (toPerm g : Equiv.Perm X).fullCycleType =
      Multiset.replicate (Fintype.card X / orderOf g) (orderOf g) := by
  classical
  set s := (toPerm g : Equiv.Perm X).fullCycleType with hs
  -- Every cycle is an orbit of `zpowers g`, which the free action identifies with `zpowers g`.
  have hmem : ∀ d ∈ s, d = orderOf g := by
    intro d hd
    rw [hs, fullCycleType_toPerm_eq_map_card_orbit] at hd
    obtain ⟨ω, -, rfl⟩ := Multiset.mem_map.mp hd
    rw [ω.orbit_eq_orbit_out Quotient.out_eq', ← Nat.card_zpowers]
    exact (Nat.card_congr (Equiv.ofInjective (fun h : Subgroup.zpowers g ↦ h • ω.out)
      fun h₁ h₂ h ↦ Subtype.ext (IsCancelSMul.right_cancel _ _ _ h))).symm
  have hrep : s = Multiset.replicate (Multiset.card s) (orderOf g) :=
    Multiset.eq_replicate_card.mpr hmem
  -- The cycle lengths add up to the number of points.
  have hsum : Multiset.card s * orderOf g = Fintype.card X := by
    rw [← Equiv.Perm.sum_fullCycleType (toPerm g : Equiv.Perm X), ← hs, hrep,
      Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul]
  rcases (orderOf g).eq_zero_or_pos with h0 | hpos
  · have : s = 0 := Multiset.eq_zero_of_forall_notMem fun d hd ↦
      (Equiv.Perm.pos_of_mem_fullCycleType hd).ne' ((hmem d hd).trans h0)
    rw [this, h0, Nat.div_zero, Multiset.replicate_zero]
  · rw [hrep, ← hsum, Nat.mul_div_cancel _ hpos]

end MulAction
