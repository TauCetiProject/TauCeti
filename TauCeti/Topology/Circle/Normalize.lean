/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Path

import TauCeti.Analysis.Normed.Module.Normalize

/-!
# Radial normalization of nowhere-zero continuous complex maps into `Circle`

For any topological space `X`, radial projection `TauCeti.normalizeToSphere` sends a nowhere-zero
continuous complex function `f : C(X, ℂ)` to a continuous map
`f.normalizeToCircle hf : C(X, Circle)` whose value at `x` has complex coordinate `f x / ‖f x‖`.
Because `Circle` is a topological group under complex multiplication, radial normalization is
multiplicative and sends `1` to `1`.

## Main definitions

* `ContinuousMap.normalizeToCircle`: radial projection of `f : C(X, ℂ)` with `∀ x, f x ≠ 0` into
  `C(X, Circle)`.
* `ContinuousMap.normalizeToCirclePath`: for `X` the unit interval, the same normalization as a
  `Path` between the normalized endpoints.

## Main results

* `ContinuousMap.coe_normalizeToCircle_apply`: `(f.normalizeToCircle hf x : ℂ) = f x / ‖f x‖`.
* `ContinuousMap.norm_mul_normalizeToCircle_apply`:
  `(‖f x‖ : ℂ) * (f.normalizeToCircle hf x : ℂ) = f x`.
* `ContinuousMap.normalizeToCircle_mul`, `ContinuousMap.normalizeToCircle_one`: radial
  normalization preserves products and `1` in `C(X, Circle)`.
* `ContinuousMap.coe_normalizeToCirclePath_apply`: normalization on the unit interval is a path
  in `Circle` between the normalized endpoints.
* `ContinuousMap.exists_path_eq_div_norm`: normalization on the unit interval with equal
  endpoint directions gives a loop in `Circle`.
* `Circle.ne_zero_of_coe_eq_div_norm`: a point of the circle equal to `w / ‖w‖` forces `w ≠ 0`.
-/

public section

noncomputable section

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
  rw [hcoe, NormedSpace.normalize, Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]

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

/-- Radial normalization of a nowhere-zero continuous complex map on the unit interval, as a path
in `Circle` between the normalized endpoints. -/
def normalizeToCirclePath (z : C(unitInterval, ℂ)) (hne : ∀ t, z t ≠ 0) :
    Path (z.normalizeToCircle hne 0) (z.normalizeToCircle hne 1) where
  toContinuousMap := z.normalizeToCircle hne
  source' := rfl
  target' := rfl

/-- The complex value of `z.normalizeToCirclePath hne t` is `z t / ‖z t‖`. -/
@[simp]
theorem coe_normalizeToCirclePath_apply (z : C(unitInterval, ℂ)) (hne : ∀ t, z t ≠ 0)
    (t : unitInterval) : (z.normalizeToCirclePath hne t : ℂ) = z t / (‖z t‖ : ℂ) := by
  simp only [normalizeToCirclePath, Path.coe_mk', coe_normalizeToCircle_apply]

/-- A nowhere-zero continuous complex map on the unit interval with equal normalized
endpoints gives a loop in `Circle` with complex coordinate `z t / ‖z t‖`. -/
theorem exists_path_eq_div_norm (z : C(unitInterval, ℂ)) (hne : ∀ t, z t ≠ 0)
    (hp : z 1 / (‖z 1‖ : ℂ) = z 0 / (‖z 0‖ : ℂ)) :
    ∃ v : Circle, ∃ p : Path v v, ∀ t : unitInterval, (p t : ℂ) = z t / (‖z t‖ : ℂ) := by
  have hclosed : z.normalizeToCircle hne 0 = z.normalizeToCircle hne 1 := Circle.ext <| by
    simpa only [coe_normalizeToCircle_apply] using hp.symm
  exact ⟨_, (z.normalizeToCirclePath hne).cast rfl hclosed, fun t ↦ by
    simp only [Path.cast_coe, coe_normalizeToCirclePath_apply]⟩

end ContinuousMap

namespace Circle

/-- A point of the circle that is the direction `w / ‖w‖` of a complex number `w` forces
`w ≠ 0`, since `0 / ‖0‖ = 0` is not on the circle. -/
theorem ne_zero_of_coe_eq_div_norm {z : Circle} {w : ℂ} (h : (z : ℂ) = w / ‖w‖) : w ≠ 0 := by
  rintro rfl
  simp at h

end Circle

end
