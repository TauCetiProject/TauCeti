/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The deviation of an `Lᵖ` function from a constant

On a finite measure space the `Lᵖ` seminorm of `fun x => f x - a`, for a constant `a`, is the
`Lᵖ` distance from `f` to the constant class `MeasureTheory.Lp.const`.  The identity is the
bridge between the seminorm form of an estimate on the deviation from a constant and its norm
form, in which both sides are continuous functions of the `Lᵖ` class and so pass to limits.

## Main declaration

* `TauCeti.eLpNorm_sub_const_eq_enorm`: the deviation from a constant as a distance in `Lᵖ`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}
  [IsFiniteMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The deviation from a constant, as a distance in `Lᵖ`.**  The `Lᵖ` seminorm of
`fun x => f x - a` is the distance from `f` to the constant class `a`. -/
theorem eLpNorm_sub_const_eq_enorm (f : Lp F p μ) (a : F) :
    eLpNorm (fun x => f x - a) p μ = ‖f - Lp.const p μ a‖ₑ := by
  rw [Lp.enorm_def]
  refine (eLpNorm_congr_ae ?_).symm
  filter_upwards [Lp.coeFn_sub f (Lp.const p μ a), Lp.coeFn_const p μ a] with x h1 h2
  rw [h1, Pi.sub_apply, h2]
  rfl

end TauCeti
