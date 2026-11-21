/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Ring.Defs

/-!
# Powers of an element against an inhomogeneous recurrence

Let `A` be a semiring, not necessarily commutative, and let `C` commute with `u`. Suppose a
sequence `Wₖ` in `A` satisfies `C W₀ = d₀` and `C Wₖ₊₁ = dₖ₊₁ + u Wₖ`. If `dⱼ = 0` for `j < h`,
then `C ^ (h + 1) W_h = C ^ h d_h`.

For `C = 1 - a u`, `Wₖ` the values at `a` of the Hasse derivatives of the Fredholm resolvent
of `u` and `dₖ` the corresponding scalar multiples of `1`, this is the identity from which the
Riesz projector at a zero of order `h` of the Fredholm determinant is built.

## Main statements

* `Commute.pow_succ_mul_eq_pow_mul_of_mul_eq`: `C ^ (h + 1) W_h = C ^ h d_h`.
-/

public section

namespace Commute

variable {A : Type*} [Semiring A]

/-- Let `C` commute with `u`, and let `Wₖ` satisfy `C W₀ = d₀` and `C Wₖ₊₁ = dₖ₊₁ + u Wₖ`.
If `dⱼ = 0` for `j < h`, then `C ^ (h + 1) W_h = C ^ h d_h`. -/
theorem pow_succ_mul_eq_pow_mul_of_mul_eq {C u : A} {W d : ℕ → A}
    (hu : Commute u C) (h0 : C * W 0 = d 0)
    (hsucc : ∀ k, C * W (k + 1) = d (k + 1) + u * W k) {h : ℕ} (hd : ∀ j < h, d j = 0) :
    C ^ (h + 1) * W h = C ^ h * d h := by
  induction h with
  | zero => simpa using h0
  | succ h ih =>
    -- `C ^ (h + 1) W_h = 0` by induction, and `u` commutes past `C ^ (h + 1)`
    have hz : C ^ (h + 1) * W h = 0 := by
      rw [ih fun j hj ↦ hd j (by omega), hd h (by omega), mul_zero]
    calc C ^ (h + 1 + 1) * W (h + 1) = C ^ (h + 1) * (d (h + 1) + u * W h) := by
          rw [pow_succ, mul_assoc, hsucc]
      _ = C ^ (h + 1) * d (h + 1) + u * (C ^ (h + 1) * W h) := by
          rw [mul_add, (hu.pow_right (h + 1)).symm.left_comm]
      _ = C ^ (h + 1) * d (h + 1) := by rw [hz, mul_zero, add_zero]

end Commute
