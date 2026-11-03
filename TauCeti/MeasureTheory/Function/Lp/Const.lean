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
`Lᵖ` distance from `f` to the constant class `MeasureTheory.Lp.const`.  The identity holds for
every exponent `p`.  It is the bridge between the seminorm form of an estimate on the deviation
from a constant and its norm form; for `1 ≤ p`, where `Lᵖ` is a normed group, both sides of the
norm form are continuous functions of the `Lᵖ` class and so pass to limits.

## Main declaration

* `TauCeti.eLpNorm_sub_const_eq_enorm`: the deviation from a constant as a distance in `Lᵖ`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}
  [IsFiniteMeasure μ] {p : ℝ≥0∞}

/-- **The deviation from a constant, as a distance in `Lᵖ`.**  The `Lᵖ` seminorm of
`fun x => f x - a` is the distance from `f` to the constant class `a`. -/
theorem eLpNorm_sub_const_eq_enorm (a : F) (f : Lp F p μ) :
    eLpNorm (fun x => f x - a) p μ = ‖f - Lp.const p μ a‖ₑ := by
  rw [Lp.enorm_def]
  exact eLpNorm_congr_ae ((Lp.coeFn_sub _ _).trans (.sub .rfl (Lp.coeFn_const p μ a))).symm

end TauCeti
