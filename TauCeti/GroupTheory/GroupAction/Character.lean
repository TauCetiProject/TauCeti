/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

public import TauCeti.Algebra.GroupAction.Trivial
import TauCeti.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.FiniteAbelian.Duality

/-!
# The group of equivariant characters

Equivariant characters into a commutative group form a subgroup of ordinary monoid
homomorphisms under pointwise multiplication. This supplies the domain of character
transgression, whose kernel describes which characters extend to a group extension.
The subgroup needs only a `MulOneClass` source with scalar multiplication. Identifying it
with the bundled equivariant homomorphisms `M →*[G] A` needs a monoid source with a
distributive action.

We use a subgroup because Mathlib's `One` on equivariant endomorphisms is the
identity map, rather than the constant character required by pointwise multiplication.

Finally, `TauCeti.natCard_additive_equivariantCharacterSubgroup_rootsOfUnity` counts the
equivariant characters of a product of groups of roots of unity under the trivial action, over a
commutative monoid with enough roots of unity.
-/

public section

namespace TauCeti

variable (G M A : Type*) [Monoid G] [CommGroup A] [MulDistribMulAction G A]

section SMul

variable [MulOneClass M] [SMul G M]

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

end SMul

variable [Monoid M] [MulDistribMulAction G M]

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

section RootsOfUnity

attribute [local instance] trivialMulDistribMulAction

variable (k G : Type) [CommMonoid k] [Monoid G]

/-- When each `n i` is nonzero and `k` has enough `∏ i, n i`-th roots of unity, the group
of equivariant `kˣ`-valued characters of `∏ i, μ_{n i}` has `∏ i, n i` elements. -/
theorem natCard_additive_equivariantCharacterSubgroup_rootsOfUnity {ι : Type} [Fintype ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] [HasEnoughRootsOfUnity k (∏ i, n i)] :
    Nat.card (Additive (equivariantCharacterSubgroup G (∀ i, rootsOfUnity (n i) k) kˣ)) =
      ∏ i, n i := by
  classical
  have : NeZero (∏ i, n i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ ↦ (NeZero.ne (n i))⟩
  have (i : ι) : HasEnoughRootsOfUnity k (n i) :=
    .of_dvd k (Finset.dvd_prod_of_mem n (Finset.mem_univ i))
  let M := ∀ i, rootsOfUnity (n i) k
  have : HasEnoughRootsOfUnity k (Monoid.exponent M) :=
    .of_dvd k (exponent_pi_rootsOfUnity_dvd_prod n)
  let : MulDistribMulAction G M := trivialMulDistribMulAction G M
  have hcardM : Nat.card M = ∏ i, n i := by
    rw [Nat.card_pi]
    simp only [HasEnoughRootsOfUnity.natCard_rootsOfUnity]
  let forget : equivariantCharacterSubgroup G M kˣ ≃ (M →* kˣ) :=
    Equiv.subtypeUnivEquiv fun f ↦
      (mem_equivariantCharacterSubgroup G M kˣ f).mpr fun _ _ ↦ rfl
  rw [Nat.card_congr Additive.toMul, Nat.card_congr forget,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, hcardM]

end RootsOfUnity

end TauCeti
