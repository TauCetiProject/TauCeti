/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Polynomial.Roots

/-!
# Evaluation of polynomials on a set

Evaluating a polynomial at every point of a set `s` gives a linear map from polynomials to
functions on `s`. Over a domain it is injective when `s` is infinite, since a nonzero polynomial
has only finitely many roots. This identifies a space of polynomials with the space of functions
it defines on `s`.

## Main definitions

* `Polynomial.evalOn s`: evaluation at the points of `s`, as a linear map `R[X] →ₗ[R] (s → R)`.

## Main results

* `Polynomial.evalOn_injective`: over a domain, evaluation on an infinite set is injective.
-/

public section

namespace Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- Evaluation of polynomials at the points of a set `s`, as a linear map to functions on `s`. -/
noncomputable def evalOn (s : Set R) : R[X] →ₗ[R] (s → R) :=
  LinearMap.pi fun z : s => leval (z : R)

@[simp]
theorem evalOn_apply (s : Set R) (p : R[X]) (z : s) : evalOn s p z = p.eval (z : R) := by
  simp [evalOn]

end Semiring

/-- Over a domain, evaluation of polynomials on an infinite set is injective. -/
theorem evalOn_injective [CommRing R] [IsDomain R] {s : Set R} (hs : s.Infinite) :
    Function.Injective (evalOn s) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  exact eq_zero_of_infinite_isRoot p (hs.mono fun z hz => by simpa using congrFun hp ⟨z, hz⟩)

end Polynomial
