/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Additive units of finitely supported functions

Coercion to functions is an injective additive monoid homomorphism `(ι →₀ M) →+ (ι → M)`, so
finitely supported functions have trivial additive units whenever their values do. For a
commutative `M` this says that zero-sum-freeness passes to `ι →₀ M`; it is the coefficientwise
form of zero-sum-freeness for monoid algebras and polynomials.
-/

public section

namespace TauCeti

/-- Finitely supported functions have trivial additive units when their values do. -/
instance instSubsingletonAddUnitsFinsupp {ι M : Type*} [AddMonoid M]
    [Subsingleton (AddUnits M)] : Subsingleton (AddUnits (ι →₀ M)) :=
  (AddUnits.map_injective (f := Finsupp.coeFnAddHom) DFunLike.coe_injective).subsingleton

end TauCeti
