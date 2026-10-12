/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# The group of equivariant characters

Equivariant characters into a commutative group form a subgroup of ordinary monoid
homomorphisms under pointwise multiplication. This supplies the domain of character
transgression, whose kernel describes which characters extend to a group extension.

We use a subgroup because Mathlib's `One` on equivariant endomorphisms is the
identity map, rather than the constant character required by pointwise multiplication.
-/

public section

namespace TauCeti

variable (G M A : Type*) [Monoid G] [Monoid M] [CommGroup A]
  [MulDistribMulAction G M] [MulDistribMulAction G A]

/-- The pointwise group of equivariant characters into `A`. -/
def equivariantCharacterSubgroup : Subgroup (M →* A) where
  carrier := {χ | ∀ (g : G) (m : M), χ (g • m) = g • χ m}
  one_mem' := by simp
  mul_mem' hχ hψ g m := by simp only [MonoidHom.mul_apply, hχ g m, hψ g m, smul_mul']
  inv_mem' hχ g m := by simp only [MonoidHom.inv_apply, hχ g m, smul_inv']

@[simp]
theorem mem_equivariantCharacterSubgroup (χ : M →* A) :
    χ ∈ equivariantCharacterSubgroup G M A ↔
      ∀ (g : G) (m : M), χ (g • m) = g • χ m :=
  Iff.rfl

/-- Equivariant characters as subgroup elements or bundled equivariant homomorphisms. -/
def equivariantCharacterEquiv : equivariantCharacterSubgroup G M A ≃ (M →*[G] A) where
  toFun χ := { χ.val with map_smul' := χ.property }
  invFun χ := ⟨χ.toMonoidHom, χ.map_smul⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem equivariantCharacterEquiv_apply (χ : equivariantCharacterSubgroup G M A) (m : M) :
    equivariantCharacterEquiv G M A χ m = χ.val m :=
  (rfl)

@[simp]
theorem equivariantCharacterEquiv_symm_coe (χ : M →*[G] A) :
    ((equivariantCharacterEquiv G M A).symm χ).val = χ.toMonoidHom :=
  (rfl)

end TauCeti
