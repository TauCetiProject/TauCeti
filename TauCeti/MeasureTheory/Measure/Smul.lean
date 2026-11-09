/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CompleteLattice

/-!
# Order and positivity of scalar multiples of measures

If `a μ ≤ b μ` for a nonzero measure `μ` and a positive scalar `a`, then `b` is positive.

## Main results

* `MeasureTheory.Measure.pos_of_smul_le_smul`: if `a μ ≤ b μ` for a nonzero measure `μ`, with
  `a > 0`, then `b > 0`.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

namespace Measure

/-- If `a μ ≤ b μ` for a nonzero measure `μ`, with `a > 0`, then `b > 0`. -/
theorem pos_of_smul_le_smul {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : ℝ≥0∞}
    (ha : 0 < a) (h : a • μ ≤ b • μ) (hμ : μ ≠ 0) : 0 < b := by
  refine pos_iff_ne_zero.2 fun h0 => hμ ?_
  rw [h0, zero_smul, Measure.nonpos_iff_eq_zero'] at h
  rw [← Measure.measure_univ_eq_zero]
  have := congr($h univ)
  simpa [ha.ne'] using this

end Measure

end MeasureTheory
