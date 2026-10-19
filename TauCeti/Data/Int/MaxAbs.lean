/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Cast

/-!
# The sup norm of a nonzero integer point

A point `(x, y)` of `ℤ²` other than the origin has `max(|x|, |y|) ≥ 1`, in any ordered ring the
integers are cast to. This is the normalisation behind lower bounds of the form
`c max(|x|, |y|) ^ e` at integer points, as in Liouville- and Roth-type inequalities for binary
forms.
-/

public section

namespace Int

/-- A point `(x, y)` of `ℤ²` other than the origin has `max(|x|, |y|) ≥ 1` in every ordered ring
`R`. -/
theorem one_le_max_abs_cast {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    {x y : ℤ} (h : x ≠ 0 ∨ y ≠ 0) : 1 ≤ max |(x : R)| |(y : R)| := by
  rcases h with hx | hy
  · exact le_max_of_le_left (by exact_mod_cast Int.one_le_abs hx)
  · exact le_max_of_le_right (by exact_mod_cast Int.one_le_abs hy)

end Int
