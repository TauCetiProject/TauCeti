/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of the real sign function

The real sign function is measurable, so it can be composed with measurable real-valued
parameters even at their zeros.
-/

public section

namespace TauCeti

/-- The real sign function is measurable. -/
@[fun_prop]
theorem measurable_real_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (by measurability) measurable_const
    (Measurable.ite (by measurability) measurable_const measurable_const)

end TauCeti
