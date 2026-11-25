/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Analysis.InnerProductSpace.OrientedJacobian
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
* the Jacobian `J(A) = det A = |a|² - |b|²`, both as `LinearMap.det`
  (`TauCeti.det_wirtingerPartsCLM`) and as the oriented Jacobian for the orientation of `ℂ` by the
  basis `(1, i)` (`TauCeti.orientedJacobian_wirtingerPartsCLM`).

The extremal directions are explicit. Writing `a = |a| e^{iα}` and `b = |b| e^{iβ}`, the image of
the unit vector `e^{i((β - α)/2 + t)}` is `(|a| e^{it} + |b| e^{-it}) e^{i(α + β)/2}`
(`TauCeti.wirtingerPartsCLM_apply_exp`); `t = 0` stretches by `|a| + |b|` and `t = π/2` by
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
    rw [add_mul, mul_assoc, mul_assoc, mul_assoc, mul_assoc, ← exp_add, ← exp_add, ← exp_add,
      ← exp_add]
    congr 3 <;> push_cast <;> ring
  have h := key ‖a‖ ‖b‖ (arg a) (arg b)
  rw [norm_mul_exp_arg_mul_I, norm_mul_exp_arg_mul_I] at h
  rw [wirtingerPartsCLM_apply, smul_eq_mul, smul_eq_mul, mul_comm _ a, mul_comm _ b, hconj, h]

/-- The operator norm of `z ↦ z a + conj z b` is `|a| + |b|`. -/
theorem norm_wirtingerPartsCLM (a b : ℂ) : ‖wirtingerPartsCLM a b‖ = ‖a‖ + ‖b‖ := by
  refine le_antisymm (norm_wirtingerPartsCLM_le a b) ?_
  have h := (wirtingerPartsCLM a b).le_opNorm (exp (↑((arg b - arg a) / 2 + 0) * I))
  rw [wirtingerPartsCLM_apply_exp, norm_exp_ofReal_mul_I, mul_one, norm_mul,
    norm_exp_ofReal_mul_I, mul_one] at h
  simpa [← ofReal_add, abs_of_nonneg (add_nonneg (norm_nonneg a) (norm_nonneg b))] using h

/-- The minimal stretch of `z ↦ z a + conj z b` is `||a| - |b||`. -/
theorem minimalStretch_wirtingerPartsCLM (a b : ℂ) :
    (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ).minimalStretch = |‖a‖ - ‖b‖| := by
  refine le_antisymm ?_ ((LinearMap.le_minimalStretch_iff _).mpr fun z ↦ ?_)
  · have h := (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ).minimalStretch_mul_norm_le_norm_apply
      (exp (↑((arg b - arg a) / 2 + Real.pi / 2) * I))
    rw [ContinuousLinearMap.coe_coe, wirtingerPartsCLM_apply_exp, norm_exp_ofReal_mul_I, mul_one,
      norm_mul, norm_exp_ofReal_mul_I, mul_one] at h
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
  · calc |‖a‖ - ‖b‖| * ‖z‖ = |‖z * a‖ - ‖conj z * b‖| := by
          rw [norm_mul, norm_mul, RCLike.norm_conj, mul_comm ‖z‖, mul_comm ‖z‖, ← sub_mul,
            abs_mul, abs_norm]
      _ ≤ ‖(wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) z‖ := by
          simpa [sub_neg_eq_add] using abs_norm_sub_norm_le (z * a) (-(conj z * b))

/-- The determinant of `z ↦ z a + conj z b` is `|a|² - |b|²`. -/
theorem det_wirtingerPartsCLM (a b : ℂ) :
    (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ).det = ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, ← normSq_eq_norm_sq, normSq_apply]
  ring

attribute [local instance] Complex.finrank_real_complex_fact

/-- The Jacobian of `z ↦ z a + conj z b`, for the orientation of `ℂ` by the basis `(1, i)`, is
`|a|² - |b|²`. -/
theorem orientedJacobian_wirtingerPartsCLM (a b : ℂ) :
    Complex.orientation.orientedJacobian Complex.orientation (wirtingerPartsCLM a b) =
      ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  rw [Orientation.orientedJacobian_self, det_wirtingerPartsCLM]

/-! ### Checks -/

/-- Check: `z ↦ z + conj z / 2` has `‖A‖ = 3/2`, `ℓ(A) = 1/2` and `J(A) = 3/4`. -/
theorem wirtingerPartsCLM_one_half :
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
theorem det_wirtingerPartsCLM_zero_one :
    (wirtingerPartsCLM (0 : ℂ) 1 : ℂ →ₗ[ℝ] ℂ).det = -1 := by
  rw [det_wirtingerPartsCLM]
  norm_num

/-- Check: `z ↦ 2 i z` stretches every direction by `2`, `‖A‖ = ℓ(A) = 2`. -/
theorem wirtingerPartsCLM_two_mul_I :
    ‖wirtingerPartsCLM (2 * I) (0 : ℂ)‖ = 2 ∧
      (wirtingerPartsCLM (2 * I) (0 : ℂ) : ℂ →ₗ[ℝ] ℂ).minimalStretch = 2 := by
  have h : ‖(2 * I : ℂ)‖ = 2 := by simp
  refine ⟨?_, ?_⟩
  · rw [norm_wirtingerPartsCLM, h, norm_zero, add_zero]
  · rw [minimalStretch_wirtingerPartsCLM, h, norm_zero, sub_zero, abs_two]

end TauCeti
