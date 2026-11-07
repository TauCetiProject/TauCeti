/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Parity
import Mathlib.Tactic.IntervalCases

/-!
# Squares modulo `5`

The squares in `ZMod 5` are `0`, `1` and `4`, so a natural number is a square modulo `5` exactly
when its remainder modulo `5` is one of these.

## Main results

* `ZMod.isSquare_natCast_iff_mod_five`: `(r : ZMod 5)` is a square if and only if
  `r % 5 = 0 ∨ r % 5 = 1 ∨ r % 5 = 4`.
-/

public section

namespace ZMod

/-- The squares in `ZMod 5` are `0`, `1` and `4`: a natural number `r` is a square modulo `5`
exactly when `r % 5` is `0`, `1` or `4`. -/
@[simp]
theorem isSquare_natCast_iff_mod_five (r : ℕ) :
    IsSquare (r : ZMod 5) ↔ r % 5 = 0 ∨ r % 5 = 1 ∨ r % 5 = 4 := by
  rw [← natCast_mod]
  have := Nat.mod_lt r (by decide : 0 < 5)
  interval_cases r % 5 <;> decide

end ZMod
