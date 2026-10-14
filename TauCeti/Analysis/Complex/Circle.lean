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
without unfolding the synonym. It also records that `Circle.toUnits` is injective, so that the
point `-1 = Circle.exp π` of the circle makes the units of `ℂ` nontrivial.

## Main declarations

* `Circle.homeomorphSphere`: `Circle ≃ₜ sphere (0 : ℂ) 1`, the identity on underlying complex
  numbers.
* `Circle.toUnits_injective`: the inclusion of the circle into the units of `ℂ` is injective.
* `Complex.instNontrivialUnits`: the units of `ℂ` form a nontrivial group.
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
theorem coe_homeomorphSphere_apply (z : Circle) : (homeomorphSphere z : ℂ) = z :=
  (rfl)

@[simp]
theorem coe_homeomorphSphere_symm_apply (z : sphere (0 : ℂ) 1) :
    (homeomorphSphere.symm z : ℂ) = z :=
  (rfl)

/-- The inclusion of the unit circle into the units of `ℂ` is injective. -/
theorem toUnits_injective : Function.Injective toUnits :=
  unitSphereToUnits_injective

end Circle

/-- The units of `ℂ` form a nontrivial group: `-1 = Circle.exp π` is a unit different from `1`. -/
instance Complex.instNontrivialUnits : Nontrivial ℂˣ :=
  nontrivial_of_ne _ _ (Circle.toUnits_injective.ne Circle.exp_pi_ne_one)
