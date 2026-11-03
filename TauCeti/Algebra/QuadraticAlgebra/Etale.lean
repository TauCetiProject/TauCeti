/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import Mathlib.RingTheory.QuadraticAlgebra
public import TauCeti.RingTheory.Etale.Discriminant

/-!
# Quadratic étale algebras

A quadratic algebra `QuadraticAlgebra R a b` over a commutative ring is étale if and only if its
discriminant `b ^ 2 + 4 * a` is a unit, including in characteristic two. This is the
finite-free discriminant criterion for the basis `1, ω`. Over a field the condition is that the
discriminant is nonzero.

## References

* [Stacks Project, Lemma 49.3.1](https://stacks.math.columbia.edu/tag/0BJF).
-/

public section

namespace QuadraticAlgebra

/-- A quadratic algebra over a commutative ring is étale if and only if its discriminant is a
unit. -/
theorem etale_iff_isUnit_discr {R : Type*} [CommRing R] {a b : R} :
    Algebra.Etale R (QuadraticAlgebra R a b) ↔ IsUnit (discr a b) := by
  rw [TauCeti.Algebra.etale_iff_isUnit_discr R _ (basis a b), Algebra.discr_quadraticAlgebra]

/-- A quadratic algebra over a field with nonzero discriminant is étale. -/
theorem etale_of_discr_ne_zero {K : Type*} [Field K] {a b : K} (hd : discr a b ≠ 0) :
    Algebra.Etale K (QuadraticAlgebra K a b) :=
  etale_iff_isUnit_discr.mpr (isUnit_iff_ne_zero.mpr hd)

end QuadraticAlgebra
