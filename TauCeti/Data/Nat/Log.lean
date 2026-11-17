/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Log

/-!
# Integer logarithms of base-`b` digit extensions and exact powers

Appending a base-`b` digit `e < b` to a positive natural number `n` raises its integer logarithm
by one: `Nat.log b (b * n + e) = Nat.log b n + 1`. This complements Mathlib's `Nat.log_mul_base`,
which is the case `e = 0` with the factors in the other order.

For any nonzero base `b`, raising `b` to `Nat.log b k` recovers `k` precisely when `k` is a power
of `b`.

## Main results

* `TauCeti.Nat.log_mul_add`: `Nat.log b (b * n + e) = Nat.log b n + 1` for `n ≠ 0` and `e < b`.
* `Nat.pow_log_eq_self_iff_exists_pow`: for `b ≠ 0`, `b ^ b.log k = k ↔ ∃ m, b ^ m = k`.
-/

public section

namespace TauCeti.Nat

/-- Appending a base-`b` digit to a positive number raises its integer logarithm by one. -/
theorem log_mul_add {b n e : ℕ} (hb : 1 < b) (hn : n ≠ 0) (he : e < b) :
    Nat.log b (b * n + e) = Nat.log b n + 1 := by
  have hle : b ≤ b * n + e :=
    (Nat.le_mul_of_pos_right b (Nat.pos_of_ne_zero hn)).trans (Nat.le_add_right _ _)
  rw [Nat.log_of_one_lt_of_le hb hle, Nat.mul_add_div (by omega), Nat.div_eq_of_lt he]
  simp

end TauCeti.Nat

namespace Nat

/-- For a nonzero base `b`, `b ^ b.log k = k` if and only if `k` is a power of `b`. -/
theorem pow_log_eq_self_iff_exists_pow {b : ℕ} (hb : b ≠ 0) (k : ℕ) :
    b ^ b.log k = k ↔ ∃ m : ℕ, b ^ m = k := by
  refine ⟨fun h ↦ ⟨b.log k, h⟩, fun ⟨m, hm⟩ ↦ hm ▸ ?_⟩
  rcases eq_or_lt_of_le (one_le_iff_ne_zero.mpr hb) with rfl | hb1
  · simp
  · rw [log_pow hb1]

end Nat
