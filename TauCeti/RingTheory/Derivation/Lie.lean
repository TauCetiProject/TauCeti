/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Lie

/-!
# Derivations as a Lie subalgebra of linear endomorphisms

The bracket of two `R`-derivations of a commutative `R`-algebra `A` is the commutator of their
underlying endomorphisms (`Derivation.commutator_coe_linear_map`). This file packages the
inclusion `Derivation R A A → Module.End R A` as an injective morphism of Lie algebras, where
`Module.End R A` is bracketed by its ring commutator. It is the analogue for derivations of
Mathlib's `LieDerivation.toLinearMapLieHom`, and it moves identities between brackets of
derivations and powers in the associative algebra `Module.End R A`.

## Main declarations

* `Derivation.toLinearMapLieHom`: the inclusion of derivations into linear endomorphisms, as a
  morphism of Lie algebras.
* `Derivation.toLinearMapLieHom_injective`: this morphism is injective.
-/

public section

namespace Derivation

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

/-- The inclusion of derivations into `R`-linear endomorphisms, as a morphism of Lie algebras for
the commutator bracket of `Module.End R A`. -/
def toLinearMapLieHom : Derivation R A A →ₗ⁅R⁆ Module.End R A where
  toFun D := D
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := commutator_coe_linear_map

variable {R A}

/-- `toLinearMapLieHom` sends a derivation to its underlying endomorphism. -/
@[simp]
theorem toLinearMapLieHom_apply (D : Derivation R A A) :
    toLinearMapLieHom R A D = (D : Module.End R A) :=
  (rfl)

/-- A derivation is determined by its underlying endomorphism. -/
theorem toLinearMapLieHom_injective : Function.Injective (toLinearMapLieHom R A) :=
  fun _ _ h ↦ ext fun a ↦ by simpa using LinearMap.congr_fun h a

end Derivation
