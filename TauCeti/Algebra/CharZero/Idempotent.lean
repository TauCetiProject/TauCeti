/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Idempotent integers in a ring of characteristic zero

In a ring of characteristic zero the integers embed injectively, so an integer is idempotent in
the ring exactly when it is idempotent in `ℤ`, that is, when it is `0` or `1`. Consequently an
idempotent other than `0` and `1` is not an integer.

## Main results

* `TauCeti.isIdempotentElem_intCast_iff`: the cast of `n : ℤ` is idempotent exactly when `n`
  is `0` or `1`.
-/

public section

namespace TauCeti

/-- In a ring of characteristic zero, the cast of an integer `n` is idempotent exactly when `n` is
`0` or `1`. -/
@[simp]
theorem isIdempotentElem_intCast_iff {R : Type*} [NonAssocRing R] [CharZero R] {n : ℤ} :
    IsIdempotentElem (n : R) ↔ n = 0 ∨ n = 1 := by
  rw [← IsIdempotentElem.iff_eq_zero_or_one, IsIdempotentElem, IsIdempotentElem, ← Int.cast_mul,
    Int.cast_inj]

end TauCeti
