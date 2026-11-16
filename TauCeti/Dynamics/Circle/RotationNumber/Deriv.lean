/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Derivatives of lifts of circle maps

A lift `f : ℝ → ℝ` of a degree one circle map satisfies `f (x + 1) = f x + 1`
(`CircleDeg1Lift.map_add_one`), so `f` differs from the identity by a `1`-periodic function.
Differentiating, its derivative is `1`-periodic. This is the form in which the derivative of a
boundary map of the closed annulus enters compactness arguments: a continuous derivative of a lift
attains its bounds on `[0, 1]`.

## Main results

* `CircleDeg1Lift.periodic_deriv`: the derivative of a lift is `1`-periodic.
-/

public section

namespace CircleDeg1Lift

/-- The derivative of a lift of a degree one circle map is `1`-periodic. This holds without any
differentiability hypothesis, since `deriv` takes its junk value `0` at the same points of each
period. -/
theorem periodic_deriv (f : CircleDeg1Lift) : Function.Periodic (deriv f) 1 := fun x ↦ by
  rw [← deriv_comp_add_const]
  simp only [map_add_one]
  exact deriv_add_const 1

end CircleDeg1Lift
