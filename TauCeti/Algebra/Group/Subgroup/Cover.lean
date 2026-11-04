/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Order.Atoms
import Mathlib.Order.LatticeIntervals

/-!
# Covering subgroups

The subgroups of `G` contained in a subgroup `K` are order-isomorphic to the subgroups of `K`
(`Subgroup.MapSubtype.orderIso`). Under that isomorphism, a subgroup `H ≤ K` is covered by `K` in
the subgroup lattice of `G` exactly when it becomes a maximal subgroup of `K`.

## Main results

* `Subgroup.covBy_iff_isCoatom_subgroupOf`: for `H ≤ K`, `H ⋖ K` if and only if
  `H.subgroupOf K` is a coatom in the subgroup lattice of `K`.
* `CovBy.isCoatom_subgroupOf`: if `H ⋖ K`, then `H.subgroupOf K` is a coatom in the subgroup
  lattice of `K`.

Both results also hold for additive subgroups.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] {H K : Subgroup G}

/-- For `H ≤ K`, `H` is covered by `K` in the subgroup lattice of `G` if and only if `H`,
regarded as a subgroup of `K`, is a maximal subgroup of `K`. -/
@[to_additive /-- For `H ≤ K`, `H` is covered by `K` in the additive subgroup lattice of `G` if
and only if `H`, regarded as an additive subgroup of `K`, is a maximal additive subgroup of `K`. -/]
theorem _root_.Subgroup.covBy_iff_isCoatom_subgroupOf (hHK : H ≤ K) :
    H ⋖ K ↔ IsCoatom (H.subgroupOf K) :=
  -- The codomain `{H' // H' ≤ K}` of `MapSubtype.orderIso K` is definitionally `Set.Iic K`;
  -- reading it as `Set.Iic K` supplies its `OrderTop` instance.
  (covBy_iff_coatom_Iic hHK).trans
    ((Subgroup.MapSubtype.orderIso K).symm.isCoatom_iff (α := Set.Iic K) _).symm

/-- If `H` is covered by `K` in the subgroup lattice of `G`, then `H`, regarded as a subgroup of
`K`, is a maximal subgroup of `K`. -/
@[to_additive /-- If `H` is covered by `K` in the additive subgroup lattice of `G`, then `H`,
regarded as an additive subgroup of `K`, is a maximal additive subgroup of `K`. -/]
theorem _root_.CovBy.isCoatom_subgroupOf (hHK : H ⋖ K) :
    IsCoatom (H.subgroupOf K) :=
  (Subgroup.covBy_iff_isCoatom_subgroupOf hHK.le).mp hHK

end TauCeti
