/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Internal.Module

/-!
# Commutative monoid objects in `ModuleCat R`

Mathlib's `ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing` makes the carrier of a monoid
object in `ModuleCat R` a ring, whose multiplication is `x * y = μ (x ⊗ₜ y)`. This file records
that the ring is commutative when the monoid object is commutative.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u

variable {R : Type u} [CommRing R]

open ModuleCat.MonModuleEquivalenceAlgebra in
/-- The commutative ring structure on a commutative monoid object in `ModuleCat R`: the ring
structure `ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing`, whose multiplication is
commutative by commutativity of the monoid object.

Like `MonObj.toRing`, this is not an instance, since it does not round trip from a commutative
ring to a monoid object and back. -/
@[expose, instance_reducible]
noncomputable def _root_.ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toCommRing
    (A : ModuleCat.{u} R) [MonObj A] [IsCommMonObj A] : CommRing A :=
  { MonObj.toRing A with
    mul_comm x y := congr($(ModuleCat.hom_ext_iff.mp (IsCommMonObj.mul_comm A)) (y ⊗ₜ x)) }

end TauCeti
