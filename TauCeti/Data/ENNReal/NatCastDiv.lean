/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Real
import Mathlib.Basic.ENNReal.Inv

/-!
# Quotients of natural numbers in `ℝ≥0∞`

* `ENNReal.natCast_div_natCast_lt_ofReal_iff`: for a positive natural number `n`, the quotient
  `m / n` in `ℝ≥0∞` is below `ENNReal.ofReal ε` exactly when `m < ε * n` in `ℝ`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- For a positive natural number `n`, the quotient `m / n` in `ℝ≥0∞` is below `ENNReal.ofReal ε`
exactly when `m < ε * n` in `ℝ`. -/
theorem natCast_div_natCast_lt_ofReal_iff {m n : ℕ} (hn : 0 < n) {ε : ℝ} :
    (m : ℝ≥0∞) / n < ENNReal.ofReal ε ↔ (m : ℝ) < ε * n := by
  -- Clear the denominator in `ℝ≥0∞`, then compare a natural number with a real.
  rw [ENNReal.div_lt_iff (by simp [hn.ne']) (by simp), ← ENNReal.ofReal_natCast n,
    ← ENNReal.ofReal_mul' (Nat.cast_nonneg n)]
  exact ENNReal.natCast_lt_ofReal

end ENNReal
