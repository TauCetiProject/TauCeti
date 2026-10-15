/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The geometric series in `a X`

Mathlib's `PowerSeries.mk_one_mul_one_sub_eq_one` says that `∑ Xⁿ` inverts `1 - X`.  Rescaling
`X` by an element `a` of the coefficient ring turns it into the statement that the geometric
series `∑ aⁿ Xⁿ` inverts `1 - a X`, with no invertibility assumption on `a`.  This is the
one-variable factor of the generating functions of the complete homogeneous symmetric
polynomials, `∏ᵢ (1 - xᵢ X)⁻¹ = ∑ₙ hₙ Xⁿ`.

## Main results

* `TauCeti.powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one`:
  `(∑ aⁿ Xⁿ) * (1 - a X) = 1`.
-/

public section

namespace TauCeti

/-- **The geometric series in `a X`**: `∑ aⁿ Xⁿ` is a multiplicative inverse of `1 - a X`, for
every element `a` of the coefficient ring. -/
theorem powerSeries_mk_pow_mul_one_sub_C_mul_X_eq_one {R : Type*} [Ring R] (a : R) :
    PowerSeries.mk (fun n => a ^ n) *
        (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  rw [mul_sub, mul_one, ← mul_assoc, PowerSeries.ext_iff]
  intro n
  cases n with
  | zero => simp
  | succ n => simp [pow_succ]

end TauCeti
