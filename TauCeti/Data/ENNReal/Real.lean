/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Claude
-/
module

public import Mathlib.Basic.ENNReal.Real

/-!
# `ENNReal.ofReal` of a difference

For `0 ≤ q ≤ p`, the embedding `ENNReal.ofReal` splits `p` into `p - q` and `q`:
`ENNReal.ofReal (p - q) + ENNReal.ofReal q = ENNReal.ofReal p`. With `p = 1` and `q = θ`, this
says that the interpolation weights `1 - θ` and `θ` sum to one in `ℝ≥0∞`.

## Main results

* `ENNReal.ofReal_sub_add_ofReal`: `ENNReal.ofReal (p - q) + ENNReal.ofReal q = ENNReal.ofReal p`
  for `0 ≤ q ≤ p`.
-/

public section

namespace ENNReal

/-- For `0 ≤ q ≤ p`, `ENNReal.ofReal` adds `p - q` and `q` back up to `p`. -/
@[simp]
theorem ofReal_sub_add_ofReal {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) :
    ENNReal.ofReal (p - q) + ENNReal.ofReal q = ENNReal.ofReal p := by
  rw [← ofReal_add (sub_nonneg.2 hqp) hq, sub_add_cancel]

end ENNReal

end
