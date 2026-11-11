/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic

/-!
# Roots of nonzero integers in a ring of characteristic zero

In a ring of characteristic zero the integers embed injectively, so the image of a nonzero integer
is nonzero. Consequently an `n`-th root (`n ≠ 0`) of a nonzero integer is itself nonzero; for
example, a square root of a nonzero integer in a number field.

## Main results

* `TauCeti.ne_zero_of_pow_eq_intCast`: in characteristic zero, an `n`-th root (`n ≠ 0`) of a
  nonzero integer is nonzero.
-/

public section

namespace TauCeti

/-- In characteristic zero, an `n`-th root of a nonzero integer, for `n ≠ 0`, is nonzero. -/
theorem ne_zero_of_pow_eq_intCast {K : Type*} [Ring K] [CharZero K] {x : K} {n : ℕ} {c : ℤ}
    (hn : n ≠ 0) (hx : x ^ n = algebraMap ℤ K c) (hc : c ≠ 0) : x ≠ 0 :=
  ne_zero_pow hn <| by rwa [hx, eq_intCast, Int.cast_ne_zero]

end TauCeti
