/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Least
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Planar linear maps: norm, minimal stretch and Jacobian

Every real-linear map of the plane `ℂ` has the form `A z = z a + conj z b` for unique `a b : ℂ`: it
is `TauCeti.wirtingerPartsCLM a b`, with `a` and `b` its two Wirtinger parts
(`TauCeti.fderiv_eq_wirtingerPartsCLM`, `TauCeti.wirtingerPartsCLM_inj`). This file computes the
three quantities of linear distortion of `A` in terms of `a` and `b`:

* the operator norm `‖A‖ = |a| + |b|` (`TauCeti.norm_wirtingerPartsCLM`);
* the minimal stretch `ℓ(A) = ||a| - |b||` (`TauCeti.minimalStretch_wirtingerPartsCLM`);
* the Jacobian `J(A) = det A = |a|² - |b|²` (`TauCeti.det_wirtingerPartsCLM`), read off from the
  real matrix of `A` in the basis `(1, i)` (`TauCeti.toMatrix_wirtingerPartsCLM`); for the
  orientation of `ℂ` by the basis `(1, i)`, `Orientation.orientedJacobian_self` identifies the
  oriented Jacobian of `A` with this determinant.

The extremal directions are explicit. Writing `a = |a| e^{iα}` and `b = |b| e^{iβ}`, the image of
the unit vector `e^{i((β - α)/2 + t)}` is `(|a| e^{it} + |b| e^{-it}) e^{i(α + β)/2}`
(`TauCeti.wirtingerPartsCLM_apply_exp`, `TauCeti.norm_wirtingerPartsCLM_apply_exp`); `t = 0`
stretches by `|a| + |b|` (`TauCeti.norm_wirtingerPartsCLM_apply_exp_zero`) and `t = π/2` by
`||a| - |b||` (`TauCeti.norm_wirtingerPartsCLM_apply_exp_pi_div_two`).

These formulas are the linear algebra behind the Beltrami coefficient `b / a` of a planar map:
the outer distortion `‖A‖² / J(A)` of `A` is `(|a| + |b|) / (|a| - |b|)` when `|b| < |a|`.

## References

* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter I.
-/

public section

noncomputable section

open Complex Module
open scoped ComplexConjugate

namespace TauCeti

/-- The image of the unit vector `e^{i((β - α)/2 + t)}` under `z ↦ z a + conj z b`, where
`α = arg a` and `β = arg b`: it is `(|a| e^{it} + |b| e^{-it}) e^{i(α + β)/2}`. -/
theorem wirtingerPartsCLM_apply_exp (a b : ℂ) (t : ℝ) :
    wirtingerPartsCLM a b (exp (↑((arg b - arg a) / 2 + t) * I)) =
      (‖a‖ * exp (t * I) + ‖b‖ * exp (-t * I)) * exp (↑((arg a + arg b) / 2) * I) := by
  have hconj : conj (exp (↑((arg b - arg a) / 2 + t) * I)) =
      exp (-↑((arg b - arg a) / 2 + t) * I) := by
    rw [← exp_conj, map_mul, conj_ofReal, conj_I, mul_neg, neg_mul]
  have key : ∀ r s α β : ℝ,
      r * exp (α * I) * exp (↑((β - α) / 2 + t) * I) +
          s * exp (β * I) * exp (-↑((β - α) / 2 + t) * I) =
        (r * exp (t * I) + s * exp (-t * I)) * exp (↑((α + β) / 2) * I) := by
    intro r s α β
    simp only [add_mul, mul_assoc, ← exp_add]
    congr 3 <;> push_cast <;> ring
  have h := key ‖a‖ ‖b‖ (arg a) (arg b)
  rw [norm_mul_exp_arg_mul_I, norm_mul_exp_arg_mul_I] at h
  rw [wirtingerPartsCLM_apply, smul_eq_mul, smul_eq_mul, mul_comm _ a, mul_comm _ b, hconj, h]

/-- The stretch of `z ↦ z a + conj z b` in the unit direction `e^{i((β - α)/2 + t)}`, where
`α = arg a` and `β = arg b`, is `||a| e^{it} + |b| e^{-it}|`. -/
theorem norm_wirtingerPartsCLM_apply_exp (a b : ℂ) (t : ℝ) :
    ‖wirtingerPartsCLM a b (exp (↑((arg b - arg a) / 2 + t) * I))‖ =
      ‖‖a‖ * exp (t * I) + ‖b‖ * exp (-t * I)‖ := by
  rw [wirtingerPartsCLM_apply_exp, norm_mul, norm_exp_ofReal_mul_I, mul_one]

/-- The stretch of `z ↦ z a + conj z b` in the unit direction `e^{i(β - α)/2}`, where `α = arg a`
and `β = arg b`, is `|a| + |b|`. -/
theorem norm_wirtingerPartsCLM_apply_exp_zero (a b : ℂ) :
    ‖wirtingerPartsCLM a b (exp (↑((arg b - arg a) / 2) * I))‖ = ‖a‖ + ‖b‖ := by
  have h := norm_wirtingerPartsCLM_apply_exp a b 0
  rw [add_zero] at h
  rw [h]
  simp [← ofReal_add, abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))]

/-- The stretch of `z ↦ z a + conj z b` in the unit direction `e^{i((β - α)/2 + π/2)}`, where
`α = arg a` and `β = arg b`, is `||a| - |b||`. -/
theorem norm_wirtingerPartsCLM_apply_exp_pi_div_two (a b : ℂ) :
    ‖wirtingerPartsCLM a b (exp (↑((arg b - arg a) / 2 + Real.pi / 2) * I))‖ = |‖a‖ - ‖b‖| := by
  have e1 : exp (↑(Real.pi / 2) * I) = I := by push_cast; exact exp_pi_div_two_mul_I
  have e2 : exp (-↑(Real.pi / 2) * I) = -I := by
    push_cast; rw [← neg_div]; exact exp_neg_pi_div_two_mul_I
  have h : (‖a‖ : ℂ) * I + ‖b‖ * -I = ↑(‖a‖ - ‖b‖) * I := by push_cast; ring
  rw [norm_wirtingerPartsCLM_apply_exp, e1, e2, h]
  simp only [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]

/-- The operator norm of `z ↦ z a + conj z b` is `|a| + |b|`. -/
@[simp]
theorem norm_wirtingerPartsCLM (a b : ℂ) : ‖wirtingerPartsCLM a b‖ = ‖a‖ + ‖b‖ := by
  refine le_antisymm (norm_wirtingerPartsCLM_le a b) ?_
  have h := (wirtingerPartsCLM a b).le_opNorm (exp (↑((arg b - arg a) / 2) * I))
  rwa [norm_wirtingerPartsCLM_apply_exp_zero, norm_exp_ofReal_mul_I, mul_one] at h

/-- The minimal stretch of `z ↦ z a + conj z b` is `||a| - |b||`. -/
@[simp]
theorem minimalStretch_wirtingerPartsCLM (a b : ℂ) :
    (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ).minimalStretch = |‖a‖ - ‖b‖| := by
  refine le_antisymm ?_ ((LinearMap.le_minimalStretch_iff _).mpr fun z ↦ ?_)
  · have h := (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ).minimalStretch_mul_norm_le_norm_apply
      (exp (↑((arg b - arg a) / 2 + Real.pi / 2) * I))
    rwa [ContinuousLinearMap.coe_coe, norm_wirtingerPartsCLM_apply_exp_pi_div_two,
      norm_exp_ofReal_mul_I, mul_one] at h
  · calc |‖a‖ - ‖b‖| * ‖z‖ = |‖z * a‖ - ‖conj z * b‖| := by
          rw [norm_mul, norm_mul, RCLike.norm_conj, mul_comm ‖z‖, mul_comm ‖z‖, ← sub_mul,
            abs_mul, abs_norm]
      _ ≤ ‖(wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) z‖ := by
          simpa [sub_neg_eq_add] using abs_norm_sub_norm_le (z * a) (-(conj z * b))

/-- The real matrix of `z ↦ z a + conj z b` in the basis `(1, i)` of `ℂ`. -/
theorem toMatrix_wirtingerPartsCLM (a b : ℂ) :
    LinearMap.toMatrix basisOneI basisOneI (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) =
      !![a.re + b.re, b.im - a.im; a.im + b.im, a.re - b.re] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [LinearMap.toMatrix_apply] <;> ring

/-- The determinant of `z ↦ z a + conj z b` is `|a|² - |b|²`. -/
@[simp]
theorem det_wirtingerPartsCLM (a b : ℂ) :
    (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ).det = ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix basisOneI, toMatrix_wirtingerPartsCLM, Matrix.det_fin_two_of,
    ← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply]
  ring

/-! ### Checks -/

/-- Check: `z ↦ z + conj z / 2` has `‖A‖ = 3/2`, `ℓ(A) = 1/2` and `J(A) = 3/4`. -/
example :
    ‖wirtingerPartsCLM (1 : ℂ) (1 / 2)‖ = 3 / 2 ∧
      (wirtingerPartsCLM (1 : ℂ) (1 / 2) : ℂ →ₗ[ℝ] ℂ).minimalStretch = 1 / 2 ∧
      (wirtingerPartsCLM (1 : ℂ) (1 / 2) : ℂ →ₗ[ℝ] ℂ).det = 3 / 4 := by
  have h : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_wirtingerPartsCLM, h, norm_one]
    norm_num
  · rw [minimalStretch_wirtingerPartsCLM, h, norm_one]
    norm_num [abs_of_pos]
  · rw [det_wirtingerPartsCLM, h, norm_one]
    norm_num

/-- Check: complex conjugation `z ↦ conj z` reverses orientation, `J(A) = -1`. -/
example :
    (wirtingerPartsCLM (0 : ℂ) 1 : ℂ →ₗ[ℝ] ℂ).det = -1 := by
  rw [det_wirtingerPartsCLM]
  norm_num

/-- Check: `z ↦ 2 i z` stretches every direction by `2`, `‖A‖ = ℓ(A) = 2`. -/
example :
    ‖wirtingerPartsCLM (2 * I) (0 : ℂ)‖ = 2 ∧
      (wirtingerPartsCLM (2 * I) (0 : ℂ) : ℂ →ₗ[ℝ] ℂ).minimalStretch = 2 := by
  have h : ‖(2 * I : ℂ)‖ = 2 := by simp
  refine ⟨?_, ?_⟩
  · rw [norm_wirtingerPartsCLM, h, norm_zero, add_zero]
  · rw [minimalStretch_wirtingerPartsCLM, h, norm_zero, sub_zero, abs_two]

end TauCeti
