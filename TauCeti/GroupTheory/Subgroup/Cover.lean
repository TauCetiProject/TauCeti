/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Order.Atoms

/-!
# Covering subgroups

This file relates consecutive subgroups of an ambient group to maximal subgroups of the larger
subgroup. If `H` is covered by `K`, then no subgroup lies strictly between them. Equivalently,
the copy `H.subgroupOf K` of `H` inside `K` is a maximal subgroup of `K`.

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
  refine ⟨?_, fun L hL => ?_⟩
  · intro htop
    apply hHK.ne
    have heq := congrArg (fun L : Subgroup K => L.map K.subtype) htop
    rw [Subgroup.map_subgroupOf_eq_of_le hHK.le, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at heq
    exact heq
  · have hlt : H < L.map K.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hHK.le]
      exact Subgroup.map_subtype_lt_map_subtype.mpr hL
    have heq : L.map K.subtype = K :=
      (hHK.eq_or_eq hlt.le (Subgroup.map_subtype_le L)).resolve_left hlt.ne'
    apply Subgroup.map_injective K.subtype_injective
    rw [heq]
    exact K.range_subtype.symm.trans K.subtype.range_eq_map

end TauCeti
