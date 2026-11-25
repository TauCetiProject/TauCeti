/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Analysis.Complex.Circle.Basic
public import TauCeti.Analysis.Normed.Module.Normalize

import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Radial normalization of nowhere-zero continuous complex maps into `Circle`

For any topological space `X`, radial projection `TauCeti.normalizeToSphere` sends a nowhere-zero
continuous complex function `f : C(X, ℂ)` to a continuous map
`f.normalizeToCircle hf : C(X, Circle)` whose value at `x` has complex coordinate `f x / ‖f x‖`.
Because `Circle` is a topological group under complex multiplication, radial normalization is
multiplicative and sends `1` to `1`.

The sphere direction `TauCeti.sphereDirection` gives a circle-valued phase via
`Circle.homeomorphSphere`, including an assigned value at zero.

## Main definitions

* `ContinuousMap.normalizeToCircle`: radial projection of `f : C(X, ℂ)` with `∀ x, f x ≠ 0` into
  `C(X, Circle)`.

## Main results

* `Complex.normalize_eq_div_norm`: complex normalization is division by the norm.
* `ContinuousMap.coe_normalizeToCircle_apply`: `(f.normalizeToCircle hf x : ℂ) = f x / ‖f x‖`.
* `ContinuousMap.norm_mul_normalizeToCircle_apply`:
  `(‖f x‖ : ℂ) * (f.normalizeToCircle hf x : ℂ) = f x`.
* `ContinuousMap.normalizeToCircle_mul`, `ContinuousMap.normalizeToCircle_one`: radial
  normalization preserves products and `1` in `C(X, Circle)`.
* `Complex.sphereDirection_one_eq_exp_arg`: the argument lifts the direction with value `1` at zero.
* `Circle.sphereDirection_mul_of_ne_zero`: the directions of nonzero complex numbers multiply.
* `ContinuousOn.sphereDirection`: the direction is continuous on any set where a complex function
  is continuous and nonzero.
* `Circle.ne_zero_of_coe_eq_div_norm`: a point of the circle equal to `w / ‖w‖` forces `w ≠ 0`.
-/

public section

noncomputable section

/-- Normalizing a complex number divides it by its norm. -/
theorem Complex.normalize_eq_div_norm (z : ℂ) : NormedSpace.normalize z = z / ‖z‖ := by
  rw [NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]

namespace TauCeti

/-- Away from zero, the complex coordinate of the sphere direction is `z / ‖z‖`. -/
@[simp] theorem coe_sphereDirection_eq_div_norm (e : Metric.sphere (0 : ℂ) 1) {z : ℂ} (hz : z ≠ 0) :
    (sphereDirection e z : ℂ) = z / ‖z‖ :=
  (coe_sphereDirection_of_ne_zero e hz).trans z.normalize_eq_div_norm

end TauCeti

open TauCeti

/-- The complex argument lifts the sphere direction with value `1` at zero. -/
theorem Complex.sphereDirection_one_eq_exp_arg (z : ℂ) :
    Circle.homeomorphSphere.symm (sphereDirection (Circle.homeomorphSphere 1) z) =
      Circle.exp z.arg := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · apply Circle.ext
    rw [Circle.coe_homeomorphSphere_symm_apply, coe_sphereDirection_eq_div_norm _ hz,
      Circle.coe_exp, Complex.exp_arg_mul_I hz]

namespace Circle

/-- The direction of the product of two nonzero complex numbers is the product of their
directions in the circle. -/
@[simp] theorem sphereDirection_mul_of_ne_zero (e : Circle) {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    homeomorphSphere.symm (sphereDirection (homeomorphSphere e) (z * w)) =
      homeomorphSphere.symm (sphereDirection (homeomorphSphere e) z) *
      homeomorphSphere.symm (sphereDirection (homeomorphSphere e) w) := by
  apply Circle.ext
  simp only [coe_mul, coe_homeomorphSphere_symm_apply,
    coe_sphereDirection_eq_div_norm _ (mul_ne_zero hz hw), coe_sphereDirection_eq_div_norm _ hz,
    coe_sphereDirection_eq_div_norm _ hw, norm_mul, Complex.ofReal_mul, div_mul_div_comm]

end Circle

/-- Taking the circle direction of a complex function preserves continuity on a set where the
function has no zeros. -/
theorem ContinuousOn.sphereDirection {X : Type*} [TopologicalSpace X] {f : X → ℂ} {s : Set X}
    (hf : ContinuousOn f s) (e : Circle) (hne : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x ↦ Circle.homeomorphSphere.symm
      (TauCeti.sphereDirection (Circle.homeomorphSphere e) (f x))) s := by
  intro x hx
  have h := continuousAt_sphereDirection (Circle.homeomorphSphere e) (hne x hx)
  exact Circle.homeomorphSphere.symm.continuous.continuousAt.comp_continuousWithinAt
    (h.comp_continuousWithinAt (hf x hx))

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X]

/-- Radial normalization of a nowhere-zero continuous complex function `f : C(X, ℂ)` as a
continuous map into `Circle`, sending `x` to `f x / ‖f x‖`. -/
def normalizeToCircle (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) : C(X, Circle) :=
  TauCeti.normalizeToSphere f f.continuous hf

/-- The complex value of `f.normalizeToCircle hf x` is `f x / ‖f x‖`. -/
@[simp]
theorem coe_normalizeToCircle_apply (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    (f.normalizeToCircle hf x : ℂ) = f x / ‖f x‖ := by
  have hcoe : (f.normalizeToCircle hf x : ℂ) = NormedSpace.normalize (f x) :=
    TauCeti.coe_normalizeToSphere_apply f f.continuous hf x
  exact hcoe.trans (f x).normalize_eq_div_norm

/-- Multiplying the normalized phase `f.normalizeToCircle hf x` by `‖f x‖` recovers `f x`. -/
theorem norm_mul_normalizeToCircle_apply (f : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (x : X) :
    (‖f x‖ : ℂ) * (f.normalizeToCircle hf x : ℂ) = f x := by
  have hnorm : (‖f x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hf x))
  rw [coe_normalizeToCircle_apply, mul_div_cancel₀ _ hnorm]

/-- Radial normalization into `Circle` respects multiplication in `C(X, ℂ)`. -/
@[simp]
theorem normalizeToCircle_mul (f g : C(X, ℂ)) (hf : ∀ x, f x ≠ 0) (hg : ∀ x, g x ≠ 0)
    (hfg : ∀ x, (f * g) x ≠ 0 := fun y => mul_ne_zero (hf y) (hg y)) :
    (f * g).normalizeToCircle hfg = f.normalizeToCircle hf * g.normalizeToCircle hg := by
  ext x
  simp [Complex.ofReal_mul, div_mul_div_comm]

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
