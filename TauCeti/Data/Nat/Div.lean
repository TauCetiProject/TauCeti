/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Notation

/-!
# Inequalities for natural-number division

When two divisors `p` and `q` are each at least `2`, the quotients `n / p` and `n / q` sum to at
most `n`, and more generally `n / (d * p) + n / (d * q) ≤ n / d` for any common factor `d`. This
ensures that two-step inclusion–exclusion refinements of divisibility counts `n / d` do not
underflow in `ℕ`.

## Main results

* `Nat.div_add_div_le_self`: `n / p + n / q ≤ n` for `2 ≤ p` and `2 ≤ q`.
* `Nat.div_mul_add_div_mul_le_div`: `n / (d * p) + n / (d * q) ≤ n / d` for `2 ≤ p` and `2 ≤ q`.
-/

public section

namespace Nat

/-- Dividing a natural number by two divisors that are each at least `2` gives quotients whose sum
is at most the original number. -/
theorem div_add_div_le_self (n : ℕ) {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    n / p + n / q ≤ n := by
  have hp2 : n / p ≤ n / 2 := Nat.div_le_div_left hp Nat.zero_lt_two
  have hq2 : n / q ≤ n / 2 := Nat.div_le_div_left hq Nat.zero_lt_two
  omega

/-- Scaling a divisor `d` by two factors that are each at least `2` gives quotients whose sum is at
most `n / d`. -/
theorem div_mul_add_div_mul_le_div (n d : ℕ) {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    n / (d * p) + n / (d * q) ≤ n / d := by
  simpa only [Nat.div_div_eq_div_mul] using div_add_div_le_self (n / d) hp hq

end Nat
