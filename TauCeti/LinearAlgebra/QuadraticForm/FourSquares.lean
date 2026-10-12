/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.Module

/-!
# Euler's four-square identity for quadratic maps

Mathlib's `euler_four_squares` says that the product of two sums of four squares in a commutative
ring is again a sum of four squares, the four new terms being the coordinates of a product of
quaternions. The same identity holds with the squares of the second factor replaced by the values
of an arbitrary quadratic map `Q : M → N`: multiplying a quadruple `(x, y, z, w)` of vectors by
the quaternion `a + bi + cj + dk` multiplies `Q x + Q y + Q z + Q w` by `a² + b² + c² + d²`.

The reason is that the matrix of left multiplication by a quaternion has orthogonal columns of
squared length `a² + b² + c² + d²`. So when `Q` of each new coordinate is expanded through the
polar form, the coefficients of `Q x, …, Q w` add up to that norm, and the coefficients of the
cross terms `polar Q x y, …` cancel. No inverse of `2` is needed. This is the identity used to
show that the fourth power of the Gauss sum of a finite quadratic module is real.

## Main declarations

* `QuadraticMap.euler_four_squares`: Euler's four-square identity for a quadratic map.
-/

public section

namespace QuadraticMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N]

/-- **Euler's four-square identity for a quadratic map.** Multiplying `(x, y, z, w)` by the
quaternion `a + bi + cj + dk` multiplies `Q x + Q y + Q z + Q w` by `a² + b² + c² + d²`. For
`Q = x ↦ x²` on a commutative ring this is `euler_four_squares`. -/
theorem euler_four_squares (Q : QuadraticMap R M N) (a b c d : R) (x y z w : M) :
    Q (a • x - b • y - c • z - d • w) + Q (a • y + b • x + c • w - d • z) +
      Q (a • z - b • w + c • x + d • y) + Q (a • w + b • z - c • y + d • x) =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) • (Q x + Q y + Q z + Q w) := by
  have hadd (u v : M) : Q (u + v) = Q u + Q v + polar Q u v := by rw [polar]; abel
  have hsub (u v : M) : Q (u - v) = Q u + Q v - polar Q u v := by
    rw [sub_eq_add_neg, hadd, polar_neg_right, QuadraticMap.map_neg]; abel
  simp only [hadd, hsub, polar_add_left, polar_sub_left, polar_smul_left, polar_smul_right,
    QuadraticMap.map_smul]
  -- Put every cross term in the form `polar Q u v` with `u` before `v` in `x, y, z, w`.
  rw [polar_comm Q y x, polar_comm Q z x, polar_comm Q w x, polar_comm Q z y, polar_comm Q w y,
    polar_comm Q w z]
  module

end QuadraticMap
