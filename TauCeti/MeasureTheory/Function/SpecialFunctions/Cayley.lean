/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.RCLike
public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# Measurability of the inverse Cayley map

The real-valued inverse Cayley map `Complex.invCayley`, `w ↦ i (1 + w) / (1 - w)` read as a real
number, is measurable (`Complex.measurable_invCayley`). It transports measures on the unit circle
to the real line, both for Nevanlinna measures and for the spectral measure of an unbounded
self-adjoint operator.
-/

public section

namespace Complex

/-- The inverse Cayley map is measurable. -/
@[fun_prop]
theorem measurable_invCayley : Measurable invCayley := by
  rw [show invCayley = fun w => (I * (1 + w) / (1 - w)).re from funext invCayley_apply]
  fun_prop

end Complex
