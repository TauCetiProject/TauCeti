/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Int.Cast.Field

/-!
# Square roots of integers sharing a factor

If `x` and `y` are square roots, in a field, of integers `a` and `b` that are both divisible by
`c`, then `x * y / c` is a square root of the integer `(a / c) * (b / c)`, the product of the
cofactors. For `c` a prime dividing two radicands, this is the square root of the product of their
`c`-free parts, which is prime to `c` when neither radicand is divisible by `c²`.

The file also records that, in characteristic zero, such a square root is nonzero as soon as its
radicand is.

## Main results

* `TauCeti.mul_div_intCast_sq_eq`: `(x * y / c) ^ 2 = (a / c) * (b / c)`.
* `TauCeti.ne_zero_of_sq_eq_intCast`: in characteristic zero, a square root of a nonzero integer
  is nonzero.
-/

public section

namespace TauCeti

/-- If `x` and `y` are square roots of integers `a` and `b` that are both divisible by `c`, and
`c` does not vanish in the field, then `x * y / c` is a square root of the integer
`(a / c) * (b / c)`. -/
theorem mul_div_intCast_sq_eq {K : Type*} [Field K] {x y : K} {a b c : ℤ}
    (hx : x ^ 2 = algebraMap ℤ K a) (hy : y ^ 2 = algebraMap ℤ K b) (ha : c ∣ a) (hb : c ∣ b)
    (hc : (c : K) ≠ 0) :
    (x * y / c) ^ 2 = algebraMap ℤ K (a / c * (b / c)) := by
  simp only [div_pow, mul_pow, hx, hy, eq_intCast, Int.cast_mul, Int.cast_div ha hc,
    Int.cast_div hb hc]
  rw [div_mul_div_comm, sq]

/-- In characteristic zero, a square root of a nonzero integer is nonzero. -/
theorem ne_zero_of_sq_eq_intCast {K : Type*} [Field K] [CharZero K] {x : K} {c : ℤ}
    (hx : x ^ 2 = algebraMap ℤ K c) (hc : c ≠ 0) : x ≠ 0 := by
  rintro rfl
  apply hc
  simpa [eq_comm] using hx

end TauCeti
