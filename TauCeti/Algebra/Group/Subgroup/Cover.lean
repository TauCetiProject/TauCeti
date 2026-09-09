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
(`Subgroup.MapSubtype.orderIso`). Under that isomorphism, a subgroup `H` covered by `K` in the
subgroup lattice of `G` becomes a maximal subgroup of `K`.

## Main result

* `CovBy.isCoatom_subgroupOf`: if `H ⋖ K`, then `H.subgroupOf K` is a coatom in the subgroup
  lattice of `K`.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] {H K : Subgroup G}

/-- If `H` is covered by `K` in the subgroup lattice of `G`, then `H`, regarded as a subgroup of
`K`, is a maximal subgroup of `K`. -/
theorem _root_.CovBy.isCoatom_subgroupOf (hHK : H ⋖ K) :
    IsCoatom (H.subgroupOf K) := by
  let _ : OrderTop { H' : Subgroup G // H' ≤ K } := Set.Iic.orderTop
  exact (OrderIso.isCoatom_iff (Subgroup.MapSubtype.orderIso K).symm _).mpr
    ((covBy_iff_coatom_Iic hHK.le).mp hHK)

end TauCeti
