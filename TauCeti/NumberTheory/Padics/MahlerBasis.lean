/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.MahlerBasis

/-!
# The Mahler basis on the p-adic integers

This file records algebraic identities for Mathlib's Mahler basis functions on `ℤ_p`.

## Main results

* `TauCeti.id_mul_mahler`: multiplication by the coordinate function satisfies
  `x * mahler n = (n + 1) • mahler (n + 1) + n • mahler n`.
-/

public section

variable {p : ℕ} [Fact p.Prime]

namespace TauCeti

/-- The Mahler recurrence `x * (x choose n) = (n + 1) * (x choose (n + 1)) + n * (x choose n)`. -/
theorem id_mul_mahler (n : ℕ) :
    ContinuousMap.id ℤ_[p] * mahler n = (n + 1) • mahler (n + 1) + n • mahler n := by
  refine ContinuousMap.ext fun x => ?_
  have hchoose :
      (n + 1) • Ring.choose x (n + 1) = Ring.choose x n * (x - n) := by
    simpa only [Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Ring.choose_one_right] using
      Ring.choose_smul_choose x (Nat.le_add_right n 1)
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.id_apply, mahler_apply]
  rw [hchoose, nsmul_eq_mul]
  ring

end TauCeti
