/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.GCD.Basic

/-!
# Coprimality and nonzero least common multiples

For `q ≠ 0` and `N ≠ 0`, the natural numbers `q` and `q ^ N - 1` are coprime, because any common
divisor of `q` and `q ^ N - 1` also divides `q ^ N - (q ^ N - 1) = 1`. This is the coprimality
needed to view `q` as a unit of `ZMod (q ^ N - 1)`.

The least common multiple of two nonzero naturals is nonzero, also as a `NeZero` instance.

## Main results

* `Nat.coprime_pow_sub_one`: `q` is coprime to `q ^ N - 1`.
* `Nat.neZero_lcm`: `NeZero (lcm m n)` for nonzero `m` and `n`.
-/

public section

namespace Nat

/-- The least common multiple of two nonzero natural numbers is nonzero. -/
instance neZero_lcm (m n : ℕ) [NeZero m] [NeZero n] : NeZero (lcm m n) :=
  ⟨lcm_ne_zero (NeZero.ne m) (NeZero.ne n)⟩

/-- If `q ≠ 0` and `N ≠ 0`, then `q` is coprime to `q ^ N - 1`. -/
theorem coprime_pow_sub_one {q N : ℕ} (hq : q ≠ 0) (hN : N ≠ 0) : q.Coprime (q ^ N - 1) :=
  .of_dvd_left (dvd_pow_self q hN) <|
    (coprime_self_sub_right (one_le_pow N q (Nat.pos_of_ne_zero hq))).2 (coprime_one_right _)

end Nat
