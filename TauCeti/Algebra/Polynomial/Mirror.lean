/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Mirror

/-!
# Irreducibility of the mirror of a polynomial

Over a ring without zero divisors, `Polynomial.mirror` is multiplicative
(`Polynomial.mirror_mul_of_domain`) and involutive (`Polynomial.mirror_mirror`), so it is a
multiplicative automorphism of `R[X]`. Consequently a polynomial is irreducible exactly when its
mirror is. This is the irreducibility input for reciprocal polynomials: the minimal polynomial of
the inverse of a nonzero algebraic number is, up to a unit, the mirror of the minimal polynomial.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {p : R[X]}

/-- A polynomial over a ring without zero divisors is irreducible exactly when its mirror is. -/
@[simp]
theorem irreducible_mirror_iff : Irreducible p.mirror ↔ Irreducible p :=
  MulEquiv.irreducible_iff
    ({ toFun := mirror
       invFun := mirror
       left_inv := mirror_involutive.leftInverse
       right_inv := mirror_involutive.rightInverse
       map_mul' := fun p q ↦ mirror_mul_of_domain p q } : R[X] ≃* R[X])

end Polynomial
