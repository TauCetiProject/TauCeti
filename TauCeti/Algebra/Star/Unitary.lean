/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Prod
public import Mathlib.Algebra.Star.Unitary

/-!
# Unitary elements

The unitary elements of a product of star monoids are the pairs of unitary elements. This file
packages that identification as a multiplicative equivalence. It also records that a unit is
unitary exactly when its adjoint is its inverse. A star-preserving multiplicative map that
sends `1` to `1`, such as a unit-preserving non-unital `⋆`-homomorphism, maps unitaries to
unitaries, and the ring inverse of a unitary element is its adjoint. Finally, the unitary
elements of a subgroup of the units are identified with the unitary elements whose unit lies in
that subgroup.

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
* `Subgroup.unitaryInfEquiv`: the unitary elements of a subgroup `H` of `Mˣ` are the unitary
  elements of `M` whose unit lies in `H`.
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

variable {M : Type*} [Monoid M] [StarMul M] (H : Subgroup Mˣ)

/-- The unitary elements `H ⊓ unitarySubgroup Mˣ` of a subgroup `H` of the units of a star monoid,
viewed as the unitary elements of the monoid whose unit lies in `H`. -/
def unitaryInfEquiv :
    (H ⊓ unitarySubgroup Mˣ : Subgroup Mˣ) ≃ {u : unitary M // Unitary.toUnits u ∈ H} where
  toFun k := ⟨unitarySubgroupUnitsEquiv ⟨k, (mem_inf.1 k.property).2⟩, by
    rw [← TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply, MulEquiv.symm_apply_apply]
    exact (mem_inf.1 k.property).1⟩
  invFun u := ⟨Unitary.toUnits u.val, mem_inf.2 ⟨u.property, by
    rw [← TauCeti.coe_unitarySubgroupUnitsEquiv_symm_apply]
    exact (unitarySubgroupUnitsEquiv.symm u.val).property⟩⟩
  left_inv _ := Subtype.ext <| Units.ext rfl
  right_inv _ := rfl

/-- The unitary element underlying `unitaryInfEquiv` is the underlying element of the unit. -/
@[simp]
theorem coe_unitaryInfEquiv_apply (k : (H ⊓ unitarySubgroup Mˣ : Subgroup Mˣ)) :
    ((H.unitaryInfEquiv k : unitary M) : M) = ((k : Mˣ) : M) :=
  (rfl)

/-- The inverse of `unitaryInfEquiv` is the canonical unitary inclusion. -/
@[simp]
theorem coe_unitaryInfEquiv_symm_apply (u : {u : unitary M // Unitary.toUnits u ∈ H}) :
    (H.unitaryInfEquiv.symm u : Mˣ) = Unitary.toUnits u.val :=
  (rfl)

end Subgroup

end
