/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Data.Rat.Cast.Defs

import Mathlib.Algebra.Group.Int.Units

/-!
# Integral rationals with product one

If two rationals that are integers have product `1`, they are both `1` or both `-1`.

## Main result

* `Rat.eq_one_or_neg_one_pair_of_mul_eq_one`
-/

public section

namespace Rat

/-- Two rationals that are integers with product one are both `1` or both `-1`. -/
theorem eq_one_or_neg_one_pair_of_mul_eq_one {a b : ℚ} (ha : ∃ n : ℤ, (n : ℚ) = a)
    (hb : ∃ m : ℤ, (m : ℚ) = b) (hab : a * b = 1) :
    (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) := by
  obtain ⟨n, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := hb
  have hnm : n * m = 1 := by exact_mod_cast hab
  exact_mod_cast Int.eq_one_or_neg_one_of_mul_eq_one' hnm

end Rat
