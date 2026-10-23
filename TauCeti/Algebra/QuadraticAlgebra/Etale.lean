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

A quadratic algebra over a field is étale when its discriminant is nonzero, including in
characteristic two. This follows from the finite-free discriminant criterion.

## References

* [Stacks Project, Lemma 49.3.1](https://stacks.math.columbia.edu/tag/0BJF).
-/

public section

namespace QuadraticAlgebra

/-- A quadratic algebra over a field with nonzero discriminant is étale. -/
theorem etale_of_discr_ne_zero {K : Type*} [Field K] {a b : K} (hd : discr a b ≠ 0) :
    Algebra.Etale K (QuadraticAlgebra K a b) := by
  apply TauCeti.Algebra.etale_of_isUnit_discr (basis a b)
  simpa only [Algebra.discr_quadraticAlgebra] using (isUnit_iff_ne_zero.mpr hd)

end QuadraticAlgebra
