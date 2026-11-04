/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

/-!
# Nonnegative norms in quadratic algebras

Over an ordered ring, a nonpositive discriminant makes the norm nonnegative
(`QuadraticAlgebra.norm_nonneg_of_discr_nonpos`), as for `ℚ(√d)` with `d < 0`.
-/

public section

namespace QuadraticAlgebra

/-- **The norm is nonnegative when the discriminant is nonpositive.** Over an ordered ring, if
`b² + 4a ≤ 0` then every element of `QuadraticAlgebra R a b` has nonnegative norm. -/
theorem norm_nonneg_of_discr_nonpos {R : Type*} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] {a b : R} (h : discr a b ≤ 0) (z : QuadraticAlgebra R a b) :
    0 ≤ norm z := by
  have := im_sq_mul_discr z
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg z.im) h, sq_nonneg (trace z)]

end QuadraticAlgebra
