/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import TauCeti.Basic.Real.Sign

/-!
# Measurability of the real sign function

The real sign function is measurable, so it can be composed with measurable real-valued
parameters even at their zeros (`TauCeti.measurable_real_sign` and `TauCeti.measurable_coe_sign`).
-/

public section

namespace TauCeti

/-- The real sign function is measurable. -/
@[fun_prop]
theorem measurable_real_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (by measurability) measurable_const
    (Measurable.ite (by measurability) measurable_const measurable_const)

/-- Coercing `SignType.sign` to `ℝ` is measurable. -/
@[fun_prop]
theorem measurable_coe_sign : Measurable fun r : ℝ => (SignType.sign r : ℝ) := by
  simpa only [Real.coe_sign_eq_sign] using measurable_real_sign

end TauCeti
