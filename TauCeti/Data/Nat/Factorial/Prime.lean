/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Multiplicity

/-!
# Prime squares dividing factorials

## Main results

* `Nat.Prime.sq_dvd_factorial_iff`: the square of a prime `p` divides `n!` if and only if
  `2 * p ≤ n`.

This is the square analogue of Mathlib's `Nat.Prime.dvd_factorial`. In particular `p ^ 2` does
not divide `p!`, the order of the permutation group on `p` points, so it does not divide the
order of any of its subgroups.
-/

public section

namespace Nat.Prime

/-- The square of a prime `p` divides `n!` if and only if `2 * p ≤ n`. -/
theorem sq_dvd_factorial_iff {p n : ℕ} (hp : p.Prime) : p ^ 2 ∣ n ! ↔ 2 * p ≤ n := by
  have h2p : 2 * p ≤ p ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hp.two_le
  rcases lt_or_ge n (p ^ 2) with hn | hn
  · rw [hp.pow_dvd_factorial_iff (Nat.log_lt_of_lt_pow' two_ne_zero hn)]
    simp [Nat.le_div_iff_mul_le hp.pos]
  · exact iff_of_true (Nat.dvd_factorial (pow_pos hp.pos 2) hn) (h2p.trans hn)

end Nat.Prime
