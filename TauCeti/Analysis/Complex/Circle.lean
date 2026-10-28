/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.ContinuousMap.Star

/-!
# The unit circle: the unit sphere of `ℂ`, the exponential and the coordinate function

Mathlib's unit circle `Circle` is a type synonym for the unit sphere `sphere (0 : ℂ) 1`, carrying
its group structure.  This file records the identification as a homeomorphism, so that results
stated for unit spheres of real normed spaces (such as their CW structures) apply to `Circle`
without unfolding the synonym.

It also packages the exponential `t ↦ exp (i t)` as a continuous homomorphism from the real line,
and records that the coordinate function `z ↦ z` is a unitary element of `C(S¹, ℂ)`.

## Main declarations

* `Circle.homeomorphSphere`: `Circle ≃ₜ sphere (0 : ℂ) 1`, the identity on underlying complex
  numbers.
* `Circle.expContinuousMonoidHom`: `t ↦ exp (i t)` as a continuous homomorphism
  `Multiplicative ℝ →ₜ* Circle`.
* `Circle.coordinate`: the coordinate function `z ↦ z` in `C(S¹, ℂ)`, and
  `Circle.coordinate_mem_unitary`.
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

/-- The map `t ↦ exp (i t)` from the real line to the circle, as a continuous homomorphism
from `Multiplicative ℝ`. -/
def expContinuousMonoidHom : ContinuousMonoidHom (Multiplicative ℝ) Circle where
  toFun t := Circle.exp t.toAdd
  map_one' := Circle.exp_zero
  map_mul' _ _ := Circle.exp_add _ _
  continuous_toFun := Circle.exp.continuous.comp continuous_toAdd

@[simp]
theorem expContinuousMonoidHom_apply (t : Multiplicative ℝ) :
    expContinuousMonoidHom t = Circle.exp t.toAdd :=
  (rfl)

/-- The coordinate function `z ↦ z` on the circle. -/
def coordinate : C(Circle, ℂ) :=
  ⟨(↑), by fun_prop⟩

@[simp]
theorem coordinate_apply (z : Circle) : coordinate z = z :=
  (rfl)

@[simp]
theorem star_coordinate_mul : star coordinate * coordinate = 1 := by
  ext z
  simp [Complex.conj_mul']

@[simp]
theorem coordinate_mul_star : coordinate * star coordinate = 1 := by
  rw [mul_comm, star_coordinate_mul]

/-- The coordinate function is a unitary element of `C(S¹, ℂ)`. -/
theorem coordinate_mem_unitary : coordinate ∈ unitary C(Circle, ℂ) :=
  ⟨star_coordinate_mul, coordinate_mul_star⟩

end Circle
