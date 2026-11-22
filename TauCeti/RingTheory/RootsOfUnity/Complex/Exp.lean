/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Compatibility of the complex roots of unity `exp(2πi / m)`

Mathlib's `Complex.isPrimitiveRoot_exp` says that `exp(2πi / m)` is a primitive `m`-th root of
unity. This file records that these roots are compatible along the power maps: for `n ∣ m` with
`m ≠ 0`, `exp(2πi / m) ^ (m / n) = exp(2πi / n)`.

## Main results

* `TauCeti.exp_two_pi_I_div_pow_div`: `exp(2πi / m) ^ (m / n) = exp(2πi / n)` for `n ∣ m`,
  `m ≠ 0`.
* `TauCeti.one_add_exp_two_pi_mul_I_div_ne_zero`: `1 + exp(2πi / l) ≠ 0` for `3 ≤ l`.
-/

public section

open Complex Real

namespace TauCeti

/-- The complex numbers `exp(2πi / m)` are compatible along the power maps: for `n ∣ m` with
`m ≠ 0`, `exp(2πi / m) ^ (m / n) = exp(2πi / n)`. -/
theorem exp_two_pi_I_div_pow_div {m n : ℕ} (hm : m ≠ 0) (h : n ∣ m) :
    exp (2 * π * I / m) ^ (m / n) = exp (2 * π * I / n) := by
  obtain ⟨k, rfl⟩ := h
  have hn : n ≠ 0 := left_ne_zero_of_mul hm
  have hk : k ≠ 0 := right_ne_zero_of_mul hm
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn), ← Complex.exp_natCast_mul]
  congr 1
  push_cast
  field_simp

/-- `1 + exp (2 * π * I / l) ≠ 0` for `3 ≤ l`: if `exp (2 * π * I / l) = -1`, then its square
would be `1`, contradicting that it is a primitive `l`-th root of unity. -/
theorem one_add_exp_two_pi_mul_I_div_ne_zero {l : ℕ} (hl : 3 ≤ l) :
    1 + exp (2 * π * I / l) ≠ 0 := by
  intro h0
  have hζ : exp (2 * π * I / l) = -1 := eq_neg_of_add_eq_zero_right h0
  have hsq : exp (2 * π * I / l) ^ 2 = 1 := by rw [hζ, neg_one_sq]
  exact (Complex.isPrimitiveRoot_exp l (by omega)).pow_ne_one_of_pos_of_lt two_ne_zero
    (by omega) hsq

end TauCeti
