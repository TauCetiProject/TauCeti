/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle

/-!
# The unit circle is the unit sphere of `ℂ`

Mathlib's unit circle `Circle` is a type synonym for the unit sphere `sphere (0 : ℂ) 1`, carrying
its group structure.  This file records the identification as a homeomorphism, so that results
stated for unit spheres of real normed spaces (such as their CW structures) apply to `Circle`
without unfolding the synonym.

## Main declarations

* `Circle.homeomorphSphere`: `Circle ≃ₜ sphere (0 : ℂ) 1`, the identity on underlying complex
  numbers.
-/

public section

noncomputable section

open Metric

namespace Circle

/-- The unit circle `Circle` is homeomorphic to the unit sphere `sphere (0 : ℂ) 1`, by the identity
on underlying complex numbers. -/
def homeomorphSphere : Circle ≃ₜ sphere (0 : ℂ) 1 :=
  Homeomorph.refl _

@[simp]
theorem coe_homeomorphSphere (z : Circle) : (homeomorphSphere z : ℂ) = z :=
  (rfl)

@[simp]
theorem coe_homeomorphSphere_symm (z : sphere (0 : ℂ) 1) : (homeomorphSphere.symm z : ℂ) = z :=
  (rfl)

end Circle
