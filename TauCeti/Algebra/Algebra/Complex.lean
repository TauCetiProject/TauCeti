/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.AlgebraTower

/-!
# The inverse of two in a complex algebra

The algebra map transports the inverse of two from the complex scalars. Open
`scoped TauCeti.ComplexAlgebra` for the resulting `Invertible (2 : A)` instance.
The identity for `⅟(2 : A)` applies to any choice of that instance.
-/

public section

namespace TauCeti.ComplexAlgebra

/-- The inverse of two in a complex algebra, transported from the scalar inverse. -/
noncomputable scoped instance invertibleTwoOfAlgebraComplex
    (A : Type*) [Semiring A] [Algebra ℂ A] : Invertible (2 : A) :=
  IsScalarTower.invertibleAlgebraCoeNat ℂ A 2

/-- The inverse of two in a complex algebra is induced by the scalar inverse. -/
theorem invOf_two_eq {A : Type*} [Semiring A] [Algebra ℂ A] [Invertible (2 : A)] :
    ⅟(2 : A) = algebraMap ℂ A (2⁻¹ : ℂ) :=
  invOf_eq_right_inv <| by
    rw [← map_ofNat (algebraMap ℂ A) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

end TauCeti.ComplexAlgebra
