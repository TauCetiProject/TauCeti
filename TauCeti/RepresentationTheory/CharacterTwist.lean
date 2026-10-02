/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.LinearCharacter

/-!
# Twisting a representation by a linear character

Tensoring a representation `ρ` with a one-dimensional representation does not change its carrier:
the line can be absorbed by `TensorProduct.lid`, leaving the same module with the action rescaled
by the character.  This file records that rescaled action directly as
`Representation.charTwist χ ρ`, `g ↦ χ g • ρ g` for a linear character `χ : G →* kˣ`, and proves
that it is the tensor product with `Representation.ofLinearCharacter χ`
(`Representation.charTwistTprodEquiv`).

Working with the twist rather than with the tensor product is what makes its basic theory
transparent.  Because every value of `χ` is a *unit*, a submodule is stable under `χ g • ρ g`
exactly when it is stable under `ρ g`, so the twist has literally the same subrepresentations
(`Representation.subrepresentationCharTwistOrderIso`) and is irreducible exactly when `ρ` is
(`Representation.isIrreducible_charTwist_iff`).  Neither statement is visible through the tensor
product without transporting along `TensorProduct.lid` first.

The twists form an action of the character group: twisting by `1` changes nothing and twisting
twice multiplies the characters.  The main consumer is the determinant twist of the general linear
group, where `χ = det ^ m` turns a polynomial representation into a rational one.

This is a module of its own rather than a section of
`TauCeti/RepresentationTheory/LinearCharacter.lean`, which it extends: the twist needs the tensor
product and the subrepresentation lattice, and that file is imported for the bare one-dimensional
representation by consumers that need neither.

## Main definitions

* `Representation.charTwist`: the representation `g ↦ χ g • ρ g`.
* `Representation.subrepresentationCharTwistOrderIso`: the twist has the same lattice of
  subrepresentations as `ρ`, by the identity on carriers.
* `Representation.charTwistTprodEquiv`: the twist **is** the tensor product
  `(ofLinearCharacter χ) ⊗ ρ`, along `TensorProduct.lid`.

## Main results

* `Representation.charTwist_one` and `Representation.charTwist_charTwist`: twisting is an action of
  the character group `G →* kˣ`.
* `Representation.charTwist_trivial`: twisting the trivial representation of the line gives the
  one-dimensional representation of the character.
* `Representation.isIrreducible_charTwist_iff`: **the twist of an irreducible representation is
  irreducible**, and conversely.
* `Representation.char_charTwist`: the trace character of the twist is `χ` times the character
  of `ρ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  rational representations of `GL n` are the determinant twists of the polynomial ones.
* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3, whose determinant twists `det ^ λₙ ⊗ V_μ` this supplies the general mechanism for.
-/

public section

namespace Representation

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}

section CommSemiring

variable [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- **The twist of a representation by a linear character**: the same carrier, with `ρ g` rescaled
by the unit `χ g`.  It is the tensor product with the one-dimensional representation of `χ`
(`Representation.charTwistTprodEquiv`), with the line absorbed. -/
def charTwist (χ : G →* kˣ) (ρ : Representation k G V) : Representation k G V where
  toFun g := (χ g : k) • ρ g
  map_one' := by simp
  map_mul' g h := by
    ext v
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul,
      smul_smul, mul_comm]

@[simp]
theorem charTwist_apply (χ : G →* kˣ) (ρ : Representation k G V) (g : G) :
    charTwist χ ρ g = (χ g : k) • ρ g :=
  (rfl)

theorem charTwist_apply_apply (χ : G →* kˣ) (ρ : Representation k G V) (g : G) (v : V) :
    charTwist χ ρ g v = (χ g : k) • ρ g v :=
  (rfl)

/-- Twisting by the trivial character changes nothing. -/
@[simp]
theorem charTwist_one (ρ : Representation k G V) : charTwist (1 : G →* kˣ) ρ = ρ :=
  MonoidHom.ext fun _ => by simp

/-- Twisting twice multiplies the characters: the twists are an action of `G →* kˣ`. -/
theorem charTwist_charTwist (χ ψ : G →* kˣ) (ρ : Representation k G V) :
    charTwist χ (charTwist ψ ρ) = charTwist (χ * ψ) ρ :=
  MonoidHom.ext fun g => LinearMap.ext fun v => by
    simp [mul_smul]

/-- Twisting the trivial representation of the coefficient line by `χ` gives the one-dimensional
representation of `χ`.  So the one-dimensional representations are the twists of the trivial one,
and `Representation.charTwist` extends `Representation.ofLinearCharacter`. -/
theorem charTwist_trivial (χ : G →* kˣ) :
    charTwist χ (trivial k G k) = ofLinearCharacter χ :=
  MonoidHom.ext fun _ => LinearMap.ext fun x => by
    simp [ofLinearCharacter_apply, smul_eq_mul]

/-- A submodule stable under `ρ` is stable under any twist of `ρ`. -/
theorem charTwist_apply_mem {χ : G →* kˣ} {ρ : Representation k G V} {p : Submodule k V}
    (hp : ∀ (g : G) ⦃v : V⦄, v ∈ p → ρ g v ∈ p) (g : G) ⦃v : V⦄ (hv : v ∈ p) :
    charTwist χ ρ g v ∈ p :=
  p.smul_mem _ (hp g hv)

/-- Conversely a submodule stable under a twist of `ρ` is stable under `ρ`, the character values
being units. -/
theorem apply_mem_of_charTwist_apply_mem {χ : G →* kˣ} {ρ : Representation k G V}
    {p : Submodule k V} (hp : ∀ (g : G) ⦃v : V⦄, v ∈ p → charTwist χ ρ g v ∈ p) (g : G) ⦃v : V⦄
    (hv : v ∈ p) : ρ g v ∈ p := by
  have h := p.smul_mem ((χ g)⁻¹ : kˣ) (hp g hv)
  rwa [charTwist_apply_apply, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_smul] at h

variable (χ : G →* kˣ) (ρ : Representation k G V)

/-- **A twist has the same subrepresentations as the representation it twists**, by the identity on
carriers: the character values are units, so they scale a stable submodule into itself and back. -/
def subrepresentationCharTwistOrderIso : Subrepresentation (charTwist χ ρ) ≃o Subrepresentation ρ
    where
  toFun p := ⟨p.toSubmodule, apply_mem_of_charTwist_apply_mem p.apply_mem_toSubmodule⟩
  invFun p := ⟨p.toSubmodule, charTwist_apply_mem p.apply_mem_toSubmodule⟩
  left_inv _ := Subrepresentation.toSubmodule_injective rfl
  right_inv _ := Subrepresentation.toSubmodule_injective rfl
  map_rel_iff' := Iff.rfl

@[simp]
theorem toSubmodule_subrepresentationCharTwistOrderIso (p : Subrepresentation (charTwist χ ρ)) :
    (subrepresentationCharTwistOrderIso χ ρ p).toSubmodule = p.toSubmodule :=
  (rfl)

@[simp]
theorem toSubmodule_subrepresentationCharTwistOrderIso_symm (p : Subrepresentation ρ) :
    ((subrepresentationCharTwistOrderIso χ ρ).symm p).toSubmodule = p.toSubmodule :=
  (rfl)

/-- **The twist is the tensor product with the one-dimensional representation of the character**,
along `TensorProduct.lid`.  This is the identification that lets the twist be read as the
roadmap's `χ ⊗ ρ` and conversely lets a tensor product with a line be computed on the original
carrier. -/
noncomputable def charTwistTprodEquiv :
    ((ofLinearCharacter χ).tprod ρ).Equiv (charTwist χ ρ) :=
  .mk (_root_.TensorProduct.lid k V) fun g => by
    ext
    simp [ofLinearCharacter_apply]

@[simp]
theorem toLinearMap_charTwistTprodEquiv :
    (charTwistTprodEquiv χ ρ).toLinearMap = (_root_.TensorProduct.lid k V).toLinearMap :=
  (rfl)

@[simp]
theorem charTwistTprodEquiv_tmul (x : k) (v : V) :
    charTwistTprodEquiv χ ρ (x ⊗ₜ[k] v) = x • v :=
  (rfl)

end CommSemiring

section Field

variable [Field k] [Monoid G] [AddCommGroup V] [Module k V] (χ : G →* kˣ)
  (ρ : Representation k G V)

/-- **A twist of an irreducible representation is irreducible**, and only a twist of an irreducible
one is: twisting by a character does not change the lattice of subrepresentations. -/
@[simp]
theorem isIrreducible_charTwist_iff : (charTwist χ ρ).IsIrreducible ↔ ρ.IsIrreducible :=
  OrderIso.isSimpleOrder_iff (subrepresentationCharTwistOrderIso χ ρ)

/-- **The character of a twist is the pointwise product** of the twisting character with the
character of the representation. -/
@[simp]
theorem char_charTwist (g : G) :
    (charTwist χ ρ).character g = (χ g : k) * ρ.character g := by
  rw [character, character, charTwist_apply, map_smul, smul_eq_mul]

end Field

end Representation
