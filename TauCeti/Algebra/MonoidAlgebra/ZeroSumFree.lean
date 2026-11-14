/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Zero-sum-freeness of monoid algebras

Zero-sum-freeness of an additive monoid is expressed by `Subsingleton (AddUnits M)`. Finitely
supported functions inherit it pointwise, and the coefficient equivalence transfers it to monoid
and additive-monoid algebras. In particular, multivariate polynomials are zero-sum-free when
their coefficients are.
-/

public section

/-- Finitely supported functions into a zero-sum-free additive monoid are zero-sum-free. -/
instance Finsupp.instSubsingletonAddUnits {ι M : Type*} [AddMonoid M]
    [Subsingleton (AddUnits M)] : Subsingleton (AddUnits (ι →₀ M)) :=
  AddUnits.map_injective (f := Finsupp.coeFnAddHom (ι := ι) (M := M))
    DFunLike.coe_injective |>.subsingleton

/-- Monoid algebras over zero-sum-free coefficients are zero-sum-free. -/
@[to_additive /-- Additive-monoid algebras over zero-sum-free coefficients are zero-sum-free. -/]
instance MonoidAlgebra.instSubsingletonAddUnits {R M : Type*} [Semiring R]
    [Subsingleton (AddUnits R)] : Subsingleton (AddUnits (MonoidAlgebra R M)) :=
  AddUnits.map_injective (f := MonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
    MonoidAlgebra.coeff_injective |>.subsingleton


