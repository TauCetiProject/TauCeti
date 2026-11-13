/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range

/-!
# Filtering natural ranges

Filtering `range h` by `c * s ≤ m` truncates the range at `m / c + 1` when `c > 0`.
-/

public section

namespace Finset

/-- For `c > 0`, filtering `range h` by `c * s ≤ m` yields
`range (min h (m / c + 1))`. -/
theorem filter_range_mul_le {h c m : ℕ} (hc : 0 < c) :
    (range h).filter (fun s ↦ c * s ≤ m) = range (min h (m / c + 1)) := by
  ext s
  simp only [mem_filter, mem_range, lt_min_iff, Nat.lt_succ_iff,
    Nat.le_div_iff_mul_le hc, Nat.mul_comm c]

/-- If `m / c < h` and `c > 0`, filtering `range h` by `c * s ≤ m` yields
`range (m / c + 1)`. -/
theorem filter_range_mul_le_of_div_lt {h c m : ℕ} (hc : 0 < c) (hm : m / c < h) :
    (range h).filter (fun s ↦ c * s ≤ m) = range (m / c + 1) := by
  rw [filter_range_mul_le hc, min_eq_right hm]

end Finset
