/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.IntegerValued.Basic
public import TauCeti.MeasureTheory.Measure.Stieltjes

/-!
# Integer-valued Stieltjes measures

A `StieltjesFunction` on the nonnegative half-line whose increments from zero are natural numbers
determines an integer-valued measure (`StieltjesFunction.isIntegerValued_measure`). For
reconstructing measures directly from counting paths (and transferring measurability and laws), see
`TauCeti.Probability.countPathMeasure`.
-/

public section

open MeasureTheory
open scoped NNReal

namespace StieltjesFunction

/-- A Stieltjes function on the half-line with natural-valued increments from zero defines an
integer-valued measure. Its initial value is arbitrary: the measure records increments and has
no atom at zero. -/
theorem isIntegerValued_measure (f : StieltjesFunction ℝ≥0)
    (hf : ∀ t, ∃ n : ℕ, f t - f 0 = n) : f.measure.IsIntegerValued :=
  Measure.isIntegerValued_of_Iic fun t => by
    obtain ⟨n, hn⟩ := hf t
    exact ⟨n, by simp [hn]⟩

end StieltjesFunction
