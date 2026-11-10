/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Interval
import Mathlib.Tactic.Linarith

/-!
# Filtered natural intervals

Filtering a bounded range by an inequality `c * s ≤ h * r` gives the range ending at
the natural quotient `h * r / c`, provided that quotient is below the original bound.
-/

public section

namespace Finset

/-- The lattice points `(r, s)` with `0 ≤ s < h` lying below the line `c s = h r`. -/
theorem filter_range_mul_le {h c r : ℕ} (hh : 0 < h) (hc : 0 < c) (hr : r < c) :
    (range h).filter (fun s ↦ c * s ≤ h * r) = range (h * r / c + 1) := by
  ext s
  simp only [mem_filter, mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le hc]
  constructor
  · rintro ⟨-, hs⟩
    linarith
  · intro hs
    refine ⟨?_, by linarith⟩
    by_contra! hsh
    nlinarith

end Finset
