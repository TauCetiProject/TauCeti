/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Tactic.Common

/-!
# Rounding a natural number up to a multiple

* `Nat.exists_dvd_between_of_pos`: rounding `M` up to a multiple of a positive `q` overshoots by
  less than `q`.
-/

public section

namespace Nat

/-- Rounding `M` up to a multiple of `q` overshoots by less than `q`. -/
theorem exists_dvd_between_of_pos {q : ℕ} (hq : 0 < q) (M : ℕ) :
    ∃ m, q ∣ m ∧ M ≤ m ∧ m < M + q := by
  refine ⟨q * ((M + q - 1) / q), ⟨_, rfl⟩, ?_, ?_⟩
  · have hrem := Nat.mod_lt (M + q - 1) hq
    have hdiv := Nat.mod_add_div (M + q - 1) q
    omega
  · have := Nat.mul_div_le (M + q - 1) q
    omega

end Nat
