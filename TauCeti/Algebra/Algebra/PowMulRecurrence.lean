/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs

/-!
# Powers of an element against a scalar-twisted recurrence

Let `A` be an `R`-algebra, not necessarily commutative, and let `C` commute with `u`. Suppose a
sequence `Wₖ` in `A` satisfies `C W₀ = c₀ • 1` and `C Wₖ₊₁ = cₖ₊₁ • 1 + u Wₖ` for scalars `cₖ`.
If `cⱼ = 0` for `j < h`, then `C ^ (h + 1) W_h = c_h • C ^ h`.

For `C = 1 - a u` and `Wₖ` the values at `a` of the Hasse derivatives of the Fredholm resolvent
of `u`, this is the identity from which the Riesz projector at a zero of order `h` of the Fredholm
determinant is built.

## Main statements

* `Commute.pow_succ_mul_eq_smul_pow_of_mul_eq`: `C ^ (h + 1) W_h = c_h • C ^ h`.
-/

public section

namespace Commute

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- Let `C` commute with `u`, and let `Wₖ` satisfy `C W₀ = c₀ • 1` and
`C Wₖ₊₁ = cₖ₊₁ • 1 + u Wₖ`. If `cⱼ = 0` for `j < h`, then `C ^ (h + 1) W_h = c_h • C ^ h`. -/
theorem pow_succ_mul_eq_smul_pow_of_mul_eq {C u : A} {W : ℕ → A} {c : ℕ → R}
    (hu : Commute u C) (h0 : C * W 0 = c 0 • 1)
    (hsucc : ∀ k, C * W (k + 1) = c (k + 1) • 1 + u * W k) {h : ℕ} (hc : ∀ j < h, c j = 0) :
    C ^ (h + 1) * W h = c h • C ^ h := by
  induction h with
  | zero => simpa using h0
  | succ h ih =>
    -- `C ^ (h + 1) W_h = 0` by induction, and `u` commutes past `C ^ (h + 1)`
    have hz : C ^ (h + 1) * W h = 0 := by
      rw [ih fun j hj ↦ hc j (by omega), hc h (by omega), zero_smul]
    rw [pow_succ, mul_assoc, hsucc, mul_add, ← mul_assoc, ← (hu.pow_right (h + 1)).eq, mul_assoc,
      hz, mul_zero, add_zero, Algebra.mul_smul_comm, mul_one]

end Commute
