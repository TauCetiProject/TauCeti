/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient

/-!
# Prime powers with totient one

Mathlib's `Nat.totient_eq_one_iff` says that `φ(n) = 1` exactly for `n = 1` and `n = 2`. This file
specialises it to prime powers: `φ(p ^ k) = 1` exactly when `k = 0`, or `p = 2` and `k = 1`.

## Main results

* `TauCeti.Nat.totient_prime_pow_eq_one_iff`: for a prime `p`, `φ(p ^ k) = 1` iff `k = 0`, or
  `p = 2` and `k = 1`.
-/

public section

namespace TauCeti.Nat

/-- For a prime `p`, the totient of `p ^ k` is one exactly when `k = 0`, or `p = 2` and `k = 1`. -/
theorem totient_prime_pow_eq_one_iff {p k : ℕ} (hp : p.Prime) :
    (p ^ k).totient = 1 ↔ k = 0 ∨ p = 2 ∧ k = 1 := by
  rw [Nat.totient_eq_one_iff, Nat.pow_eq_one, Nat.Prime.pow_eq_iff Nat.prime_two]
  simp [hp.ne_one]

end TauCeti.Nat
