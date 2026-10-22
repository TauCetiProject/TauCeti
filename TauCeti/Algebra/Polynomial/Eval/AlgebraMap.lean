/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Evaluation at a central scalar

For an `R`-algebra `S`, possibly noncommutative, the element `algebraMap R S t` is central, so
evaluating polynomials with coefficients in `S` at it is a ring homomorphism `S[X] →+* S`. Over a
noncommutative ring evaluation at an arbitrary point is not multiplicative, so Mathlib's
`Polynomial.evalRingHom` is only available over commutative rings.
-/

public section

noncomputable section

namespace Polynomial

variable {R : Type*} (S : Type*) [CommSemiring R] [Semiring S] [Algebra R S]

/-- Evaluation at the central element `algebraMap R S t`, as a ring homomorphism. -/
def evalAlgebraMapRingHom (t : R) : S[X] →+* S :=
  eval₂RingHom' (RingHom.id S) (algebraMap R S t) fun a ↦ Algebra.commute_algebraMap_right t a

@[simp]
theorem evalAlgebraMapRingHom_apply (t : R) (p : S[X]) :
    evalAlgebraMapRingHom S t p = p.eval (algebraMap R S t) :=
  eval₂_id

end Polynomial
