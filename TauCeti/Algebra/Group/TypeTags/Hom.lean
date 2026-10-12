/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Additive homomorphisms as characters valued in a unit group

Mathlib's `AddMonoidHom.toMultiplicative` reads an additive homomorphism `M →+ N` as a monoid
homomorphism `Multiplicative M →* Multiplicative N`. When `N` is an additive group, the target
`Multiplicative N` is a group, so it is its own group of units through `toUnits`, and the
homomorphism becomes a character `Multiplicative M →* (Multiplicative N)ˣ`. This is the shape in
which Mathlib's duality theory for finite abelian groups states its results, with the characters of
`G` valued in `Mˣ` for a monoid `M` with enough roots of unity.

## Main definitions

* `AddMonoidHom.toMultiplicativeUnits`: the equivalence
  `(M →+ N) ≃ (Multiplicative M →* (Multiplicative N)ˣ)`, with the evaluation lemmas
  `AddMonoidHom.toMultiplicativeUnits_apply_apply` and
  `AddMonoidHom.toMultiplicativeUnits_symm_apply_apply`.
-/

public section

namespace AddMonoidHom

variable {M N : Type*} [AddZeroClass M] [AddGroup N]

/-- **Additive homomorphisms into an additive group are characters valued in its unit group**:
`M →+ N` read multiplicatively, through `AddMonoidHom.toMultiplicative`, lands in the group
`Multiplicative N`, which is its own group of units through `toUnits`. -/
def toMultiplicativeUnits : (M →+ N) ≃ (Multiplicative M →* (Multiplicative N)ˣ) :=
  AddMonoidHom.toMultiplicative.trans (MulEquiv.monoidHomCongrRightEquiv toUnits)

/-- The character attached to `f : M →+ N` sends `x` to the unit `ofAdd (f (toAdd x))`. -/
@[simp]
theorem toMultiplicativeUnits_apply_apply (f : M →+ N) (x : Multiplicative M) :
    toMultiplicativeUnits f x = toUnits (Multiplicative.ofAdd (f (Multiplicative.toAdd x))) :=
  (rfl)

/-- The additive homomorphism attached to a character `φ` sends `x` to the additive reading of the
underlying element of the unit `φ (ofAdd x)`. -/
@[simp]
theorem toMultiplicativeUnits_symm_apply_apply (φ : Multiplicative M →* (Multiplicative N)ˣ)
    (x : M) :
    toMultiplicativeUnits.symm φ x =
      Multiplicative.toAdd (φ (Multiplicative.ofAdd x) : Multiplicative N) :=
  (rfl)

end AddMonoidHom
