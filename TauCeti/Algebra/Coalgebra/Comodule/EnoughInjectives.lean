/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Abelian
public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Enough injectives for comodules over a flat coalgebra

Over a commutative ring, the category of comodules over a flat coalgebra has enough
injectives. The exact faithful forgetful functor has the cofree functor as right adjoint.
Consequently a cofree comodule on an injective module is injective, and an injective
presentation of the underlying module lifts to one of the comodule. No flatness or
finiteness condition is imposed on the coefficient module.

This is the construction in Jantzen, *Representations of Algebraic Groups*, Part I,
§3.9. The categorical transfer uses Mathlib's `EnoughInjectives.of_adjunction`.
-/

public section

open CategoryTheory

namespace TauCeti.ComoduleCat

universe u v w

variable (R : Type u) (C : Type v) [CommRing R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C] [Module.Flat R C]

/-- A cofree comodule on an injective module is injective when the coalgebra is flat. -/
instance (M : ModuleCat.{max v w} R) [Injective M] :
    Injective (cofree R C M) :=
  Injective.injective_of_adjoint (cofreeAdjunction R C) M

/-- Comodules over a flat coalgebra have enough injectives, with no restriction on their
coefficient modules. The carrier universe contains those of the ring and coalgebra. -/
instance : EnoughInjectives (ComoduleCat.{u, v, max u v w} R C) :=
  EnoughInjectives.of_adjunction (cofreeAdjunction.{u, v, max u w} R C)

end TauCeti.ComoduleCat
