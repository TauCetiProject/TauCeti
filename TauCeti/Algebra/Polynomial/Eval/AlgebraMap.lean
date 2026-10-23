/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Evaluation at a central scalar

For an `R`-algebra `S`, possibly noncommutative, the element `algebraMap R S t` is central, so
evaluating polynomials with coefficients in `S` at it is a ring homomorphism `S[X] →+* S`. Over a
noncommutative ring evaluation at an arbitrary point is not multiplicative, so Mathlib's
`Polynomial.evalRingHom` is only available over commutative rings.

The value at `algebraMap R S t` expands as a sum of the coefficients of `p` weighted by the powers
of `t`.
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

/-- Evaluating a polynomial at the image of a scalar `t` combines its coefficients with the powers
of `t`. -/
theorem eval_algebraMap_eq_sum_range (p : S[X]) (t : R) :
    p.eval (algebraMap R S t) = ∑ i ∈ Finset.range (p.natDegree + 1), t ^ i • p.coeff i := by
  rw [eval_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← map_pow, Algebra.smul_def, Algebra.commutes]

end Polynomial
