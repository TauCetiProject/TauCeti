/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.ENatENNReal

/-!
# Extended natural numbers as extended nonnegative reals

The `WithTop.recTopCoe` expression used for extended hitting-time means agrees with the
canonical coercion from `ℕ∞` to `ℝ≥0∞`.
-/

public section

open scoped ENNReal

namespace WithTop

/-- Sending infinity to infinity and natural numbers to their casts is `ENat.toENNReal`.
Use explicitly: as a global simp rule, this can leave a cast of `WithTop` infinity that
simp lemmas for `ENat` infinity do not match. -/
theorem recTopCoe_top_natCast_eq_toENNReal (t : WithTop ℕ) :
    t.recTopCoe (⊤ : ℝ≥0∞) (fun n => (n : ℝ≥0∞)) = ENat.toENNReal t := by
  induction t using WithTop.recTopCoe with
  | top => exact ENat.toENNReal_top.symm
  | coe n => exact (ENat.toENNReal_coe n).symm

end WithTop
