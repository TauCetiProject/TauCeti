/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Analysis.Complex.Circle.Basic
public import TauCeti.Analysis.Normed.Module.Normalize.Complex

import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Radial normalization of nowhere-zero continuous complex maps into `Circle`

For any topological space `X`, radial projection `TauCeti.normalizeToSphere` sends a nowhere-zero
continuous complex function `f : C(X, ℂ)` to a continuous map
`f.normalizeToCircle hf : C(X, Circle)` whose value at `x` has complex coordinate `f x / ‖f x‖`.
Because `Circle` is a topological group under complex multiplication, radial normalization is
multiplicative and sends `1` to `1`.

`Circle.phase` is the sphere direction transported to the circle,
with an assigned value at zero.

## Main definitions

* `ContinuousMap.normalizeToCircle`: radial projection of `f : C(X, ℂ)` with `∀ x, f x ≠ 0` into
  `C(X, Circle)`.

## Main results

* `Circle.coe_phase_of_ne_zero`: the phase is division by the norm
  away from zero.
* `Circle.norm_mul_phase`: multiplying the phase by the norm recovers the original number.
* `Circle.continuousAt_phase`: the phase is continuous at each nonzero point.
* `ContinuousMap.normalizeToCircle_apply`: evaluation of bundled normalization as a circle phase.
* `ContinuousMap.coe_normalizeToCircle_apply`: `(f.normalizeToCircle hf x : ℂ) = f x / ‖f x‖`.
* `ContinuousMap.norm_mul_normalizeToCircle_apply`:
  `(‖f x‖ : ℂ) * (f.normalizeToCircle hf x : ℂ) = f x`.
* `ContinuousMap.normalizeToCircle_mul`, `ContinuousMap.normalizeToCircle_one`: radial
  normalization preserves products and `1` in `C(X, Circle)`.
* `Circle.phase_one_eq_exp_arg`: the phase with fallback `1` equals
  `Circle.exp (Complex.arg z)` pointwise, including at zero.
* `Circle.phase_mul_of_ne_zero`: the phases of nonzero factors multiply.
* `Circle.ne_zero_of_coe_eq_div_norm`: a point of the circle equal to `w / ‖w‖` forces `w ≠ 0`.
-/

public section

noncomputable section

open TauCeti

namespace Circle

/-- The circle phase of a complex number, with specified value `e` at zero. -/
def phase (z : ℂ) (e : Circle) : Circle :=
  homeomorphSphere.symm (sphereDirection (homeomorphSphere e) z)

/-- The circle phase at zero is the specified value. -/
@[simp] theorem phase_zero (e : Circle) :
    phase 0 e = e := by
  simp [phase]

/-- The underlying complex value of the circle phase away from zero is `z / ‖z‖`. -/
@[simp] theorem coe_phase_of_ne_zero (e : Circle) {z : ℂ} (hz : z ≠ 0) :
    (phase z e : ℂ) = z / ‖z‖ := by
  rw [phase, coe_homeomorphSphere_symm_apply,
    coe_sphereDirection_eq_div_norm _ hz]

/-- Multiplying the circle phase by the norm recovers the complex number, including at zero. -/
theorem norm_mul_phase (e : Circle) (z : ℂ) : (‖z‖ : ℂ) * (phase z e : ℂ) = z := by
  rw [phase, coe_homeomorphSphere_symm_apply, ← Complex.real_smul, norm_smul_sphereDirection]

/-- The circle phase with a fixed value at zero is continuous at each nonzero point. -/
theorem continuousAt_phase (e : Circle) {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun w ↦ phase w e) z :=
  homeomorphSphere.symm.continuous.continuousAt.comp
    (continuousAt_sphereDirection (homeomorphSphere e) hz)

/-- The direction of the product of two nonzero complex numbers is the product of their
directions in the circle. -/
@[simp] theorem phase_mul_of_ne_zero (e : Circle) {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0) :
    phase (z * w) e = phase z e * phase w e := by
  apply Circle.ext
  simp only [coe_mul, coe_phase_of_ne_zero _ (mul_ne_zero hz hw),
    coe_phase_of_ne_zero _ hz,
    coe_phase_of_ne_zero _ hw, ← Complex.normalize_eq_div_norm,
    Complex.normalize_mul]

/-- With fallback `1`, the circle phase is the exponential of the principal argument at each
complex number, including at zero. -/
theorem phase_one_eq_exp_arg (z : ℂ) : phase z 1 = Circle.exp z.arg := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · apply Circle.ext
    rw [coe_phase_of_ne_zero _ hz, coe_exp, Complex.exp_arg_mul_I hz]

end Circle

/-- The circle phase is continuous on a set where the input is continuous and nonzero. -/
theorem ContinuousOn.circlePhase {X : Type*} [TopologicalSpace X]
    {f : X → ℂ} {s : Set X} (hf : ContinuousOn f s) (e : Circle)
    (hne : ∀ x ∈ s, f x ≠ 0) : ContinuousOn (fun x ↦ Circle.phase (f x) e) s :=
  fun x hx ↦ (Circle.continuousAt_phase e (hne x hx)).comp_continuousWithinAt (hf x hx)

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- Radial normalization of a nowhere-zero continuous complex function `f : C(X, ℂ)` as a
continuous map into `Circle`, sending `x` to `f x / ‖f x‖`. -/
def normalizeToCircle (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) : C(X, Circle) where
  toFun x := Circle.phase (f x) 1
  continuous_toFun := continuousOn_univ.mp <|
    f.continuous.continuousOn.circlePhase 1 fun x _ ↦ hf x

/-- Pointwise evaluation of the bundled normalization is the circle phase. -/
theorem normalizeToCircle_apply (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    f.normalizeToCircle hf x = Circle.phase (f x) 1 :=
  (rfl)

/-- The complex value of `f.normalizeToCircle hf x` is `f x / ‖f x‖`. -/
@[simp]
theorem coe_normalizeToCircle_apply (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    (f.normalizeToCircle hf x : ℂ) = f x / ‖f x‖ := by
  rw [normalizeToCircle_apply, Circle.coe_phase_of_ne_zero _ (hf x)]

/-- Multiplying the normalized phase `f.normalizeToCircle hf x` by `‖f x‖` recovers `f x`. -/
theorem norm_mul_normalizeToCircle_apply (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    (‖f x‖ : ℂ) * (f.normalizeToCircle hf x : ℂ) = f x := by
  simpa only [normalizeToCircle_apply] using Circle.norm_mul_phase 1 (f x)

/-- Radial normalization into `Circle` respects multiplication in `C(X, ℂ)`. -/
@[simp]
theorem normalizeToCircle_mul (f g : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0)
    (hfg : ∀ x, (f * g) x ≠ 0 := fun y => mul_ne_zero (hf y) (hg y)) :
    (f * g).normalizeToCircle hfg = f.normalizeToCircle hf * g.normalizeToCircle hg := by
  ext1 x
  simp only [normalizeToCircle_apply, ContinuousMap.mul_apply,
    Circle.phase_mul_of_ne_zero 1 (hf x) (hg x)]

/-- Radial normalization sends `1 : C(X, ℂ)` to `1 : C(X, Circle)`. -/
@[simp]
theorem normalizeToCircle_one
    (hf : ∀ x : X, (1 : C(X, ℂ)) x ≠ 0 := fun _ => one_ne_zero) :
    (1 : C(X, ℂ)).normalizeToCircle hf = 1 := by
  ext x
  simp [coe_normalizeToCircle_apply]

end ContinuousMap

namespace Circle

/-- A point of the circle that is the direction `w / ‖w‖` of a complex number `w` forces
`w ≠ 0`, since `0 / ‖0‖ = 0` is not on the circle. -/
theorem ne_zero_of_coe_eq_div_norm {z : Circle} {w : ℂ} (h : (z : ℂ) = w / ‖w‖) : w ≠ 0 := by
  rintro rfl
  simp at h

end Circle

end
