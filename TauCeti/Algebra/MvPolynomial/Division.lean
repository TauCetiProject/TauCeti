/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Division

/-!
# A variable is a nonzerodivisor

Over an arbitrary commutative semiring of coefficients, multiplication by a variable of a
multivariable polynomial semiring is injective: dividing by the monomial of that variable undoes
it. Mathlib's `MvPolynomial.X_prime` gives the same conclusion, but only over a coefficient ring
with no zero divisors.

## Main results

* `MvPolynomial.X_mul_right_injective`: multiplication by a variable is injective.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- Multiplication by a variable is injective, over any commutative semiring of coefficients:
dividing by the monomial of that variable is a left inverse. -/
theorem X_mul_right_injective (i : σ) :
    Function.Injective fun p : MvPolynomial σ R => X i * p := fun p q h => by
  simpa using congrArg (fun r : MvPolynomial σ R => r.divMonomial (Finsupp.single i 1)) h

end MvPolynomial
