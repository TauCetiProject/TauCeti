/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import TauCeti.Algebra.Group.Finsupp

/-!
# Additive units of monoid algebras

A monoid algebra is additively its coefficient function, by the additive equivalence
`MonoidAlgebra.coeffAddEquiv`. It therefore has trivial additive units whenever its coefficient
semiring does; for commutative coefficient semirings this says that a sum in the monoid algebra
vanishes only when every summand does. The same holds for additive monoid algebras, and so for
multivariate polynomials `MvPolynomial σ R = AddMonoidAlgebra R (σ →₀ ℕ)`.
-/

public section

namespace TauCeti

/-- Monoid algebras over coefficients with trivial additive units have trivial additive units. -/
@[to_additive instSubsingletonAddUnitsAddMonoidAlgebra
  /-- Additive monoid algebras over coefficients with trivial additive units have
trivial additive units. -/]
instance instSubsingletonAddUnitsMonoidAlgebra {R M : Type*} [Semiring R]
    [Subsingleton (AddUnits R)] : Subsingleton (AddUnits (MonoidAlgebra R M)) :=
  (AddUnits.map_injective (f := MonoidAlgebra.coeffAddEquiv.toAddMonoidHom)
    MonoidAlgebra.coeff_injective).subsingleton

end TauCeti
