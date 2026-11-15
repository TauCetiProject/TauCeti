/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Logic.Function.Iterate

/-!
# Alternating vertex functions

A function `c` from the vertices of a quiver to a type with negation *alternates* when it is
negated by every arrow, `c j = -c i` for all `a : i ⟶ j`. This file records what such a function
does along a path: over a path of length `n` it is negated `n` times. When negation is involutive,
`Function.Involutive.iterate_even` and `Function.Involutive.iterate_odd` then show that `c` is
unchanged along a path of even length and negated along one of odd length.

In particular, a closed walk of odd length forces an alternating function to satisfy
`c a = -c a`. When the values lie in a ring, this gives `2 * c a = 0`.

## Main results

* `TauCeti.eq_iterate_neg_of_path`: an alternating vertex function is negated `n` times along a
  path of length `n`.
-/

public section

namespace TauCeti

universe u v

variable {V : Type u} [Quiver.{v} V] {k : Type*} [Neg k]

/-- **A sign-changing vertex function is negated once per arrow of a path.** If `c` negates along
every arrow of a quiver, then along every path of length `n` it is negated `n` times. -/
theorem eq_iterate_neg_of_path {c : V → k} (hc : ∀ ⦃i j : V⦄, (i ⟶ j) → c j = -c i)
    {a b : V} (p : Quiver.Path a b) : c b = Neg.neg^[p.length] (c a) := by
  induction p with
  | nil => rfl
  | cons p e ih => rw [hc e, ih, Quiver.Path.length_cons, Function.iterate_succ_apply']

end TauCeti
