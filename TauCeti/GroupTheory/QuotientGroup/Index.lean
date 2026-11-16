/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.GroupTheory.QuotientGroup.ThirdIso

/-!
# Indices in quotient groups

This file records how the index of the image of a subgroup in a quotient group is computed in
the original group. It is the `Nat.card` shadow of the coset-space bijection
`QuotientGroup.quotientQuotientEquivQuotientSup`, and is read off it.

## Main results

* `Subgroup.index_map_mk'_eq_index_sup`: the index of the image of `H` in `G ⧸ N` is the
  index of `H ⊔ N` in `G`.
* `Subgroup.index_comap_subtype_eq_card_map`: the index of the preimage of `N` in `H` is the order
  of the image of `H` in `G ⧸ N`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- The index of the image of a subgroup in a quotient is the index of its join with the
quotienting subgroup: the two coset spaces are in bijection, by
`QuotientGroup.quotientQuotientEquivQuotientSup`. -/
@[to_additive (attr := simp), simp]
theorem index_map_mk'_eq_index_sup (H N : Subgroup G) [N.Normal] :
    (H.map (QuotientGroup.mk' N)).index = (H ⊔ N).index :=
  Nat.card_congr (QuotientGroup.quotientQuotientEquivQuotientSup H N)

/-- The index of the preimage of a normal subgroup `N` in a subgroup `H` is the order of the image
of `H` in the quotient by `N`. -/
@[to_additive]
theorem index_comap_subtype_eq_card_map (H N : Subgroup G) [N.Normal] :
    (N.comap H.subtype).index = Nat.card (H.map (QuotientGroup.mk' N)) := by
  rw [← Subgroup.relIndex_ker H (QuotientGroup.mk' N), QuotientGroup.ker_mk', Subgroup.relIndex,
    ← Subgroup.comap_subtype]

end Subgroup
