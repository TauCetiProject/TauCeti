/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import TauCeti.Analysis.InnerProductSpace.OrientedJacobian
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Least
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Planar linear maps: norm, minimal stretch and Jacobian

Every real-linear map of the plane `ℂ` has the form `A z = a z + b conj z` for unique `a b : ℂ`
(`TauCeti.planarLinearMap_eq`, `TauCeti.planarLinearMap_injective`). This file computes the three
quantities of linear distortion of `A` in terms of `a` and `b`:

* the operator norm `‖A‖ = |a| + |b|` (`TauCeti.norm_planarLinearMap`);
* the minimal stretch `ℓ(A) = ||a| - |b||` (`TauCeti.minimalStretch_planarLinearMap`);
* the Jacobian `J(A) = det A = |a|² - |b|²`, both as `LinearMap.det`
  (`TauCeti.det_planarLinearMap`) and as the oriented Jacobian for the orientation of `ℂ` by the
  basis `(1, i)` (`TauCeti.orientedJacobian_planarLinearMap`).

The extremal directions are explicit. Writing `a = |a| e^{iα}` and `b = |b| e^{iβ}`, the image of
the unit vector `e^{i((β - α)/2 + t)}` is `(|a| e^{it} + |b| e^{-it}) e^{i(α + β)/2}`
(`TauCeti.planarLinearMap_apply_exp`); `t = 0` stretches by `|a| + |b|` and `t = π/2` by
`||a| - |b||`.

These are the planar formulas of §1.5 of the QuasiregularMaps roadmap, the linear algebra behind
the Beltrami coefficient `b / a` of a planar map: the outer distortion `‖A‖² / J(A)` of `A` is
`(|a| + |b|) / (|a| - |b|)` when `|b| < |a|`.
-/

public section

noncomputable section

open Complex Module
open scoped ComplexConjugate

namespace TauCeti

/-- The real-linear map `z ↦ a z + b conj z` of the plane `ℂ`. Every real-linear map of `ℂ` has this
form (`TauCeti.planarLinearMap_eq`). -/
def planarLinearMap (a b : ℂ) : ℂ →ₗ[ℝ] ℂ :=
  a • (LinearMap.id : ℂ →ₗ[ℝ] ℂ) + b • (conjAe.toLinearMap.restrictScalars ℝ : ℂ →ₗ[ℝ] ℂ)

@[simp]
theorem planarLinearMap_apply (a b z : ℂ) : planarLinearMap a b z = a * z + b * conj z :=
  (rfl)

/-- Every real-linear map `A` of `ℂ` is `z ↦ a z + b conj z`, with `a = (A 1 - i A i) / 2` and
`b = (A 1 + i A i) / 2`. -/
theorem planarLinearMap_eq (A : ℂ →ₗ[ℝ] ℂ) :
    planarLinearMap ((A 1 - I * A I) / 2) ((A 1 + I * A I) / 2) = A := by
  refine Complex.basisOneI.ext fun i ↦ ?_
  fin_cases i
  · simp
    ring
  · simp
    linear_combination (-A I) * I_sq

/-- The coefficients `a` and `b` of `z ↦ a z + b conj z` are determined by the map. -/
theorem planarLinearMap_injective : Function.Injective fun p : ℂ × ℂ ↦ planarLinearMap p.1 p.2 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h1 := LinearMap.congr_fun h 1
  have hI := LinearMap.congr_fun h I
  simp only [planarLinearMap_apply, mul_one, map_one, conj_I] at h1 hI
  have ha : a = a' := by linear_combination (h1 - I * hI) / 2 + (a - b - a' + b') / 2 * I_sq
  subst ha
  have hb : b = b' := by linear_combination h1
  rw [hb]

/-- The image of the unit vector `e^{i((β - α)/2 + t)}`, where `α = arg a` and `β = arg b`: it is
`(|a| e^{it} + |b| e^{-it}) e^{i(α + β)/2}`. -/
theorem planarLinearMap_apply_exp (a b : ℂ) (t : ℝ) :
    planarLinearMap a b (exp (↑((arg b - arg a) / 2 + t) * I)) =
      (‖a‖ * exp (t * I) + ‖b‖ * exp (-t * I)) * exp (↑((arg a + arg b) / 2) * I) := by
  have hconj : conj (exp (↑((arg b - arg a) / 2 + t) * I)) =
      exp (-↑((arg b - arg a) / 2 + t) * I) := by
    rw [← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg, neg_mul]
  have key : ∀ r s α β : ℝ,
      r * exp (α * I) * exp (↑((β - α) / 2 + t) * I) +
          s * exp (β * I) * exp (-↑((β - α) / 2 + t) * I) =
        (r * exp (t * I) + s * exp (-t * I)) * exp (↑((α + β) / 2) * I) := by
    intro r s α β
    rw [add_mul, mul_assoc, mul_assoc, mul_assoc, mul_assoc, ← exp_add, ← exp_add, ← exp_add,
      ← exp_add]
    congr 3 <;> push_cast <;> ring
  have h := key ‖a‖ ‖b‖ (arg a) (arg b)
  rw [norm_mul_exp_arg_mul_I, norm_mul_exp_arg_mul_I] at h
  rw [planarLinearMap_apply, hconj, h]

/-- The operator norm of `z ↦ a z + b conj z` is `|a| + |b|`. -/
theorem norm_planarLinearMap (a b : ℂ) :
    ‖LinearMap.toContinuousLinearMap (planarLinearMap a b)‖ = ‖a‖ + ‖b‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z ↦ ?_) ?_
  · rw [LinearMap.coe_toContinuousLinearMap', planarLinearMap_apply, add_mul]
    refine (norm_add_le _ _).trans ?_
    simp
  · have h := (LinearMap.toContinuousLinearMap (planarLinearMap a b)).le_opNorm
      (exp (↑((arg b - arg a) / 2 + 0) * I))
    rw [LinearMap.coe_toContinuousLinearMap', planarLinearMap_apply_exp, norm_exp_ofReal_mul_I,
      mul_one, norm_mul, norm_exp_ofReal_mul_I, mul_one] at h
    simpa [← ofReal_add, abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))] using h

/-- The minimal stretch of `z ↦ a z + b conj z` is `||a| - |b||`. -/
theorem minimalStretch_planarLinearMap (a b : ℂ) :
    (planarLinearMap a b).minimalStretch = |‖a‖ - ‖b‖| := by
  refine le_antisymm ?_ ((LinearMap.le_minimalStretch_iff _).mpr fun z ↦ ?_)
  · have h := (planarLinearMap a b).minimalStretch_mul_norm_le_norm_apply
      (exp (↑((arg b - arg a) / 2 + Real.pi / 2) * I))
    rw [planarLinearMap_apply_exp, norm_exp_ofReal_mul_I, mul_one, norm_mul,
      norm_exp_ofReal_mul_I, mul_one] at h
    have e1 : exp (↑(Real.pi / 2) * I) = I := by
      rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
      simp
    have e2 : exp (-↑(Real.pi / 2) * I) = -I := by
      rw [neg_mul, exp_neg, e1, inv_I]
    have e3 : (‖a‖ : ℂ) * I + ‖b‖ * -I = ↑(‖a‖ - ‖b‖) * I := by
      push_cast
      ring
    rw [e1, e2, e3, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs] at h
    exact h
  · calc |‖a‖ - ‖b‖| * ‖z‖ = |‖a * z‖ - ‖b * conj z‖| := by
          rw [norm_mul, norm_mul, RCLike.norm_conj, ← sub_mul, abs_mul, abs_norm]
      _ ≤ ‖planarLinearMap a b z‖ := by
          simpa [sub_neg_eq_add] using abs_norm_sub_norm_le (a * z) (-(b * conj z))

/-- The determinant of `z ↦ a z + b conj z` is `|a|² - |b|²`. -/
theorem det_planarLinearMap (a b : ℂ) : (planarLinearMap a b).det = ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, ← normSq_eq_norm_sq, normSq_apply]
  ring

attribute [local instance] Complex.finrank_real_complex_fact

/-- The Jacobian of `z ↦ a z + b conj z`, for the orientation of `ℂ` by the basis `(1, i)`, is
`|a|² - |b|²`. -/
theorem orientedJacobian_planarLinearMap (a b : ℂ) :
    Complex.orientation.orientedJacobian Complex.orientation (planarLinearMap a b) =
      ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  rw [Orientation.orientedJacobian_self, det_planarLinearMap]

/-! ### Checks -/

/-- Check: `z ↦ z + conj z / 2` has `‖A‖ = 3/2`, `ℓ(A) = 1/2` and `J(A) = 3/4`. -/
theorem planarLinearMap_one_half :
    ‖LinearMap.toContinuousLinearMap (planarLinearMap 1 (1 / 2))‖ = 3 / 2 ∧
      (planarLinearMap 1 (1 / 2)).minimalStretch = 1 / 2 ∧
      (planarLinearMap 1 (1 / 2)).det = 3 / 4 := by
  have h : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_planarLinearMap, h, norm_one]
    norm_num
  · rw [minimalStretch_planarLinearMap, h, norm_one]
    norm_num [abs_of_pos]
  · rw [det_planarLinearMap, h, norm_one]
    norm_num

/-- Check: complex conjugation `z ↦ conj z` reverses orientation, `J(A) = -1`. -/
theorem det_planarLinearMap_zero_one : (planarLinearMap 0 1).det = -1 := by
  rw [det_planarLinearMap]
  norm_num

/-- Check: `z ↦ 2 i z` stretches every direction by `2`, `‖A‖ = ℓ(A) = 2`. -/
theorem planarLinearMap_two_mul_I :
    ‖LinearMap.toContinuousLinearMap (planarLinearMap (2 * I) 0)‖ = 2 ∧
      (planarLinearMap (2 * I) 0).minimalStretch = 2 := by
  have h : ‖(2 * I : ℂ)‖ = 2 := by simp
  refine ⟨?_, ?_⟩
  · rw [norm_planarLinearMap, h, norm_zero, add_zero]
  · rw [minimalStretch_planarLinearMap, h, norm_zero, sub_zero, abs_two]

end TauCeti
