/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Star.Prod
public import Mathlib.Algebra.Star.Unitary

/-!
# Unitary elements

The unitary elements of a product of star monoids are the pairs of unitary elements. This file
packages that identification as a multiplicative equivalence. It also records that a unit is
unitary exactly when its adjoint is its inverse. A star-preserving multiplicative map that
sends `1` to `1`, such as a unit-preserving non-unital `⋆`-homomorphism, maps unitaries to
unitaries, and the ring inverse of a unitary element is its adjoint.

For a subgroup `H` of the units `Mˣ` of a star monoid `M`, the unitary part `H.unitaryPart` is the
subgroup of `unitary M` consisting of the unitary elements whose unit lies in `H`. For a subgroup
`H` of `GL(n, 𝕜)` this is `K_H = H ∩ U(n)` viewed inside the unitary group, the compact factor of
the Cartan decomposition of `H`. The same elements also form the subgroup
`(unitarySubgroup Mˣ).subgroupOf H` of `H`, and both have the same image in `Mˣ`.

## Main definitions and results

* `TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply`: the inverse unitary equivalence
  agrees with `Unitary.toUnits` after coercion to units.

* `Unitary.prodEquiv`: `unitary (A × B)` is multiplicatively equivalent to
  `unitary A × unitary B`.
* `Unitary.map_mem_of_map_one`: a star-preserving multiplicative map with `f 1 = 1` maps
  unitaries to unitaries.
* `Unitary.ringInverse_coe`: the ring inverse of a unitary element is its adjoint.
* `Units.mem_unitary_iff_star_eq_inv`: a unit `u` is unitary if and only if `star u = u⁻¹`
  in `R`.
* `Subgroup.unitaryPart`: the unitary part of a subgroup of units, with `Subgroup.mem_unitaryPart`
  and `Subgroup.coe_unitaryPart`.
* `Subgroup.map_subtype_unitarySubgroup_subgroupOf`: the unitary part of `H` and the unitary
  elements of `H` have the same image in `Mˣ`.
-/

public section

namespace Unitary

variable (A B : Type*) [Monoid A] [Monoid B] [StarMul A] [StarMul B]

/-- Unitary elements in a product are pairs of unitary elements. -/
def prodEquiv :
    unitary (A × B) ≃* unitary A × unitary B :=
  (MulEquiv.submonoidCongr (Prod.unitary_eq A B)).trans
    (Submonoid.prodEquiv (unitary A) (unitary B))

/-- The product underlying the forward unitary-product equivalence is unchanged. -/
@[simp]
theorem coe_prodEquiv_apply (u : unitary (A × B)) :
    (((prodEquiv A B u).1 : A), ((prodEquiv A B u).2 : B)) = (u : A × B) :=
  (rfl)

/-- The product underlying the inverse unitary-product equivalence is the pair of underlying
unitary elements. -/
@[simp]
theorem coe_prodEquiv_symm_apply (u : unitary A × unitary B) :
    ((prodEquiv A B).symm u : A × B) = ((u.1 : A), (u.2 : B)) :=
  (rfl)

/-- A star-preserving multiplicative map sending `1` to `1` maps unitaries to unitaries. This
applies to non-unital `⋆`-homomorphisms that happen to preserve the unit; compare
`Unitary.map_mem` for monoid homomorphism classes. -/
theorem map_mem_of_map_one {R S F : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S]
    [FunLike F R S] [MulHomClass F R S] [StarHomClass F R S] (f : F) (hf : f 1 = 1) {r : R}
    (hr : r ∈ unitary R) : f r ∈ unitary S :=
  Unitary.mem_iff.mpr
    ⟨by rw [← map_star, ← map_mul, Unitary.star_mul_self_of_mem hr, hf],
      by rw [← map_star, ← map_mul, Unitary.mul_star_self_of_mem hr, hf]⟩

/-- The ring inverse of a unitary element is its adjoint. -/
@[simp]
theorem ringInverse_coe {R : Type*} [MonoidWithZero R] [StarMul R] (u : unitary R) :
    Ring.inverse (u : R) = star (u : R) :=
  Ring.inverse_unit (Unitary.toUnits u)

end Unitary

namespace Units

section Monoid

variable {R : Type*} [Monoid R] [StarMul R] {u : Rˣ}

/-- A unit is unitary exactly when its adjoint is its inverse. -/
theorem mem_unitary_iff_star_eq_inv : (u : R) ∈ unitary R ↔ star (u : R) = ↑u⁻¹ :=
  ⟨fun h ↦ (u.inv_eq_of_mul_eq_one_left (Unitary.star_mul_self_of_mem h)).symm,
    fun h ↦ u.isUnit.mem_unitary_of_star_mul_self (h ▸ u.inv_mul)⟩

/-- The adjoint of the inverse of a unit whose underlying element is unitary is the unit. -/
theorem star_inv_eq_of_mem_unitary (h : (u : R) ∈ unitary R) : star (↑u⁻¹ : R) = u := by
  rw [← mem_unitary_iff_star_eq_inv.1 h, star_star]

end Monoid

/-- For a unit `u` whose underlying element is unitary, `u - u⁻¹` is skew-adjoint. -/
theorem star_sub_inv_of_mem_unitary {R : Type*} [Ring R] [StarRing R] {u : Rˣ}
    (h : (u : R) ∈ unitary R) : star ((u : R) - ↑u⁻¹) = ↑u⁻¹ - u := by
  rw [star_sub, mem_unitary_iff_star_eq_inv.1 h, star_inv_eq_of_mem_unitary h]

end Units

namespace TauCeti

/-- The inverse unitary equivalence, viewed in the units, is the canonical unitary inclusion. -/
@[simp]
theorem coe_unitarySubgroupUnitsEquiv_symm_apply {M : Type*} [Monoid M] [StarMul M]
    (u : unitary M) : (unitarySubgroupUnitsEquiv.symm u : Mˣ) = Unitary.toUnits u := by
  apply Units.ext
  exact (val_unitarySubgroupUnitsEquiv_symm_apply_coe u).trans
    (Unitary.val_toUnits_apply u).symm

end TauCeti

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

end
