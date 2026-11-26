/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Finite subgroups

For a finite subgroup `H` of a group, such as any subgroup of a finite group,
`Subgroup.fintypeOfFinite H` is a `Fintype` structure on the elements of `H`, so that finite sums
and products can be indexed over `H`. Examples are the sum over a subgroup in the relative norm,
and the sums over a subgroup and its cosets in the transfer.

A homomorphism `f : G →* H` from a finite group with `f.range = K` and `Nat.card G ≤ Nat.card K`
is an isomorphism onto `K`. This is how a finite presentation is recognised as a concrete
group: an order bound on the presented group, compared with the order of the image of the
presentation map, upgrades that map to `MonoidHom.mulEquivOfRangeEq`.

The intersection `H ⊓ K` of two subgroups can be read as a subgroup of `K` or of `H`, and the
two readings have the same order (`Subgroup.card_subgroupOf_comm`).

## Main definitions

* `Subgroup.fintypeOfFinite`: the `Fintype` structure `Fintype.ofFinite` on the elements of a
  finite subgroup.
* `MonoidHom.mulEquivOfRangeEq`: a homomorphism from a finite group onto a subgroup `K` with at
  least as many elements, as an isomorphism with `K`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

-- Not a global instance: Mathlib's `Subgroup.instFintypeSubtypeMemOfDecidablePred` asks for
-- decidable membership instead, and the two structures are not definitionally equal. Files about
-- finite subgroups, such as the subgroups of a finite group, install this one with
-- `attribute [local instance]`, so that their statements share one `Fintype` structure.
/-- The `Fintype` structure on a finite subgroup given by `Fintype.ofFinite`. -/
@[instance_reducible, expose]
noncomputable def fintypeOfFinite (H : Subgroup G) [Finite H] : Fintype H :=
  Fintype.ofFinite H

/-- The intersection `H ⊓ K`, read in `K` or in `H`, has the same order either way. -/
theorem card_subgroupOf_comm (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card (K.subgroupOf H) := by
  rw [← card_subtype K, ← card_subtype H, subgroupOf_map_subtype, subgroupOf_map_subtype, inf_comm]

end Subgroup

namespace MonoidHom

variable {G H : Type*} [Group G] [Group H]

/-- A homomorphism from a finite group whose range is `K`, where `K` has at least as many elements
as the source, is an isomorphism onto `K`. -/
noncomputable def mulEquivOfRangeEq [Finite G] (f : G →* H) {K : Subgroup H} (hK : f.range = K)
    (hcard : Nat.card G ≤ Nat.card K) : G ≃* K :=
  MulEquiv.ofBijective ((MulEquiv.subgroupCongr hK).toMonoidHom.comp f.rangeRestrict) <|
    Function.Surjective.bijective_of_nat_card_le
      ((MulEquiv.subgroupCongr hK).surjective.comp f.rangeRestrict_surjective) hcard

/-- The isomorphism `MonoidHom.mulEquivOfRangeEq` is `f`, read in `K`. -/
@[simp]
theorem coe_mulEquivOfRangeEq_apply [Finite G] (f : G →* H) {K : Subgroup H} (hK : f.range = K)
    (hcard : Nat.card G ≤ Nat.card K) (g : G) : (f.mulEquivOfRangeEq hK hcard g : H) = f g := by
  simp only [mulEquivOfRangeEq, MulEquiv.ofBijective_apply, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom, Function.comp_apply, MulEquiv.subgroupCongr_apply, coe_rangeRestrict]

end MonoidHom
