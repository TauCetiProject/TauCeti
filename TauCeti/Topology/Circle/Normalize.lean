/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.ContinuousMap.Algebra

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

## Main results

* `ContinuousMap.coe_normalizeToCircle_apply`: `(f.normalizeToCircle hf x : ℂ) = f x / ‖f x‖`.
* `ContinuousMap.norm_mul_normalizeToCircle_apply`:
  `(‖f x‖ : ℂ) * (f.normalizeToCircle hf x : ℂ) = f x`.
* `ContinuousMap.normalizeToCircle_mul`, `ContinuousMap.normalizeToCircle_one`: radial
  normalization preserves products and `1` in `C(X, Circle)`.
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

end ContinuousMap

end
