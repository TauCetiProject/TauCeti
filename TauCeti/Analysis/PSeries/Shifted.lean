/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Summable

/-!
# The shifted `p`-series over `ℤ`

The weights `(1 + |n|) ^ r` are summable over `n : ℤ` for `r < -1`. This is the form in which the
`p`-series enters weighted sequence spaces. It follows from Mathlib's `Real.summable_abs_int_rpow`
(the unshifted series `∑ |n| ^ (-b)` for `1 < b`) by the general comparison
`Summable.const_add_rpow`: shifting a base that is positive outside a finite set by a constant
keeps a summable family of nonpositive powers summable.

## Main results

* `TauCeti.summable_one_add_abs_int_rpow` — `∑ n : ℤ, (1 + |n|) ^ r` converges for `r < -1`.
-/

public section

namespace TauCeti

/-- The weights `(1 + |n|) ^ r` are summable over `ℤ` for `r < -1`. -/
theorem summable_one_add_abs_int_rpow {r : ℝ} (hr : r < -1) :
    Summable fun n : ℤ ↦ (1 + |(n : ℝ)|) ^ r := by
  have h := Real.summable_abs_int_rpow (b := -r) (by linarith)
  rw [neg_neg] at h
  exact h.const_add_rpow (by linarith) ((Filter.eventually_cofinite_ne 0).mono fun n hn ↦
    abs_pos.2 (Int.cast_ne_zero.2 hn)) 1

end TauCeti
