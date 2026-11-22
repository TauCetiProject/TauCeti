/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.GroupTheory.Index.Basic

/-!
# Orbit sizes of a quotient group on normal-subgroup orbits

Let a group `G` act on a type `X`, and let `N` be a normal subgroup of `G`. The quotient group
`G ⧸ N` acts on the space of `N`-orbits `orbitRel.Quotient N X` by translating representatives
(`MulAction.orbitRel.Quotient.instMulActionQuotientGroup`). Taking indices in the stabilizer
formula `Subgroup.comap_stabilizer_quotientGroup_orbitRelQuotient_mk` via the relative-index
identity across `N ⊔ stabilizer G x` yields the orbit-size factorization

`Nat.card (orbit (G ⧸ N) ⟦x⟧) * Nat.card (orbit N x) = Nat.card (orbit G x)`

(`Subgroup.card_orbit_quotientGroup_mul_card_orbit_normal`), with no finiteness hypothesis on `G` or
`X`.

## Main results

* `Subgroup.card_orbit_quotientGroup_mul_card_orbit_normal`: the `(G ⧸ N)`-orbit size of the
  `N`-orbit of `x` times the `N`-orbit size of `x` equals the `G`-orbit size of `x`.
-/

public section

namespace Subgroup

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- **Orbit-size factorization across a normal subgroup.** For a normal subgroup `N` of `G`, the
size of the `(G ⧸ N)`-orbit of the `N`-orbit of `x`, times the size of the `N`-orbit of `x`, equals
the size of the `G`-orbit of `x`. No finiteness hypothesis is needed. -/
@[to_additive card_orbit_quotientAddGroup_mul_card_orbit_normal
  /-- **Orbit-size factorization across a normal additive subgroup.** For a normal additive subgroup
  `N` of `G`, the size of the `(G ⧸ N)`-orbit of the `N`-orbit of `x`, times the size of the
  `N`-orbit of `x`, equals the size of the `G`-orbit of `x`. No finiteness hypothesis is needed. -/]
theorem card_orbit_quotientGroup_mul_card_orbit_normal (N : Subgroup G) [N.Normal] (x : X) :
    Nat.card (orbit (G ⧸ N) (_root_.Quotient.mk'' x : orbitRel.Quotient N X)) *
        Nat.card (orbit N x) =
      Nat.card (orbit G x) := by
  calc
    Nat.card (orbit (G ⧸ N) (_root_.Quotient.mk'' x : orbitRel.Quotient N X)) *
        Nat.card (orbit N x)
      = (stabilizer (G ⧸ N) (_root_.Quotient.mk'' x : orbitRel.Quotient N X)).index *
          (stabilizer N x).index := by
        rw [Nat.card_congr (orbitEquivQuotientStabilizer _ _),
          Nat.card_congr (orbitEquivQuotientStabilizer _ _),
          Subgroup.index_eq_card, Subgroup.index_eq_card]
    _ = (N ⊔ stabilizer G x).index * (stabilizer G x).relIndex N := by
        rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N),
          comap_stabilizer_quotientGroup_orbitRelQuotient_mk, ← stabilizer_subgroupOf,
          Subgroup.relIndex]
    _ = (stabilizer G x).relIndex (stabilizer G x ⊔ N) * (stabilizer G x ⊔ N).index := by
        rw [Subgroup.relIndex_sup_of_le_normalizer Subgroup.le_normalizer_of_normal,
          sup_comm, mul_comm]
    _ = (stabilizer G x).index := Subgroup.relIndex_mul_index le_sup_left
    _ = Nat.card (orbit G x) := by
        rw [Nat.card_congr (orbitEquivQuotientStabilizer G x), Subgroup.index_eq_card]

end Subgroup
