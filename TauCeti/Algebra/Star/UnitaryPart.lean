/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Star.Unitary
import TauCeti.Algebra.Star.Unitary

/-!
# The unitary part of a subgroup of units

For a subgroup `H` of the units `Mˣ` of a star monoid `M`, the unitary part `H.unitaryPart` is the
subgroup of `unitary M` consisting of the unitary elements whose unit lies in `H`. For a subgroup
`H` of `GL(n, 𝕜)` this is `K_H = H ∩ U(n)` viewed inside the unitary group, the compact factor of
the Cartan decomposition of `H`.

The same elements also form the subgroup `(unitarySubgroup Mˣ).subgroupOf H` of `H`;
`Subgroup.map_subtype_unitarySubgroup_subgroupOf` says that both have the same image in `Mˣ`.

## Main definitions and results

* `Subgroup.unitaryPart`: the unitary part of a subgroup of units, with `Subgroup.mem_unitaryPart`
  and `Subgroup.coe_unitaryPart`.
* `Subgroup.map_subtype_unitarySubgroup_subgroupOf`: the unitary part of `H` and the unitary
  elements of `H` have the same image in `Mˣ`.
-/

public section

namespace Subgroup

variable {M : Type*} [Monoid M] [StarMul M]

/-- The unitary part of a subgroup `H` of the units of a star monoid `M`: the unitary elements of
`M` whose unit lies in `H`. For a subgroup `H` of `GL n 𝕜` it is `K_H = H ∩ U(n)` as a subgroup of
the unitary group. -/
def unitaryPart (H : Subgroup Mˣ) : Subgroup (unitary M) :=
  H.comap Unitary.toUnits

variable {H : Subgroup Mˣ}

/-- A unitary element lies in the unitary part of `H` exactly when its unit lies in `H`. -/
@[simp]
theorem mem_unitaryPart {k : unitary M} : k ∈ H.unitaryPart ↔ Unitary.toUnits k ∈ H :=
  mem_comap

/-- As a set, the unitary part of `H` is the preimage of `H` under `Unitary.toUnits`. -/
@[simp]
theorem coe_unitaryPart : (H.unitaryPart : Set (unitary M)) = Unitary.toUnits ⁻¹' H :=
  coe_comap _ _

variable (H) in
/-- The unitary part of `H`, a subgroup of `unitary M`, and the unitary elements of `H`, a subgroup
of `H`, have the same image in `Mˣ`. -/
theorem map_subtype_unitarySubgroup_subgroupOf :
    ((unitarySubgroup Mˣ).subgroupOf H).map H.subtype = H.unitaryPart.map Unitary.toUnits := by
  rw [subgroupOf_map_subtype]
  ext g
  simp only [mem_inf, mem_map, mem_unitaryPart]
  constructor
  · rintro ⟨hg, hgH⟩
    have hk := TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply (unitarySubgroupUnitsEquiv ⟨g, hg⟩)
    rw [MulEquiv.symm_apply_apply] at hk
    exact ⟨_, hk ▸ hgH, hk.symm⟩
  · rintro ⟨k, hk, rfl⟩
    rw [← TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply]
    exact ⟨SetLike.coe_mem _, (TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply k).symm ▸ hk⟩

end Subgroup
