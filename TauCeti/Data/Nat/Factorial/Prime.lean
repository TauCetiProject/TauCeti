/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Factorial

/-!
# Prime divisibility of factorials

## Main results

* `Nat.Prime.not_sq_dvd_factorial`: a prime occurs only once in its own factorial.
-/

public section

namespace TauCeti

/-- A prime occurs only once in its own factorial. -/
theorem Nat.Prime.not_sq_dvd_factorial {p : ℕ} (hp : p.Prime) : ¬ p ^ 2 ∣ p.factorial := by
  intro h
  rw [← Nat.mul_factorial_pred hp.ne_zero, pow_two] at h
  have := hp.dvd_factorial.1 (Nat.dvd_of_mul_dvd_mul_left hp.pos h)
  exact (Nat.not_le_of_gt (Nat.sub_lt hp.pos (by omega))) this

end TauCeti
