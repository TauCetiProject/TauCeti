/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Combinatorics.Quiver.Path

/-!
# Alternating vertex functions

A function from the vertices of a quiver to a monoid with distributive negation *alternates*
when it is negated by every arrow,
`c j = -c i` for all `a : i ⟶ j`. This file records what such a function does along a path: it is
multiplied by `(-1)ⁿ` over a path of length `n`, so it is unchanged along a path of even length and
negated along one of odd length.

In particular, a closed walk of odd length forces an alternating function to satisfy
`c a = -c a`. When the values lie in a ring, this gives `2 * c a = 0`.

## Main results

* `TauCeti.eq_neg_one_pow_mul_of_path`: an alternating vertex function changes by `(-1)ⁿ` along a
  path of length `n`.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u} [Quiver.{v} V] (k : Type*) [Monoid k] [HasDistribNeg k]

/-- **A sign-changing vertex function changes by `(-1)ⁿ` along a path.** If `c` negates along
every arrow of a quiver, then it is multiplied by `(-1)ⁿ` along every path of length `n`. -/
theorem eq_neg_one_pow_mul_of_path {c : V → k} (hc : ∀ ⦃i j : V⦄, (i ⟶ j) → c j = -c i)
    {a b : V} (p : Quiver.Path a b) : c b = (-1) ^ p.length * c a := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp [hc e, ih, pow_succ]

end TauCeti
