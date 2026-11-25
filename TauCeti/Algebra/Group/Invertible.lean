/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Invertible.Defs

/-!
# Inverses of elements equal to one

Mathlib's `invOf_one` computes `⅟1` for an element that is syntactically `1`. This file records
the same value for an element that is only provably equal to `1`, whatever its `Invertible`
witness, so that it can be used when the element is a compound term that cannot be substituted.

## Main results

* `TauCeti.invOf_eq_one_of_eq_one`: if `a = 1`, then `⅟a = 1`.
-/

public section

namespace TauCeti

/-- An element equal to `1` has inverse `1`, whatever its `Invertible` witness. -/
theorem invOf_eq_one_of_eq_one {M : Type*} [Monoid M] {a : M} [Invertible a] (h : a = 1) :
    ⅟a = 1 :=
  invOf_eq_right_inv (by rw [h, mul_one])

end TauCeti
