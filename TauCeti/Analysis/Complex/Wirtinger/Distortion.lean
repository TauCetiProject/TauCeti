/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.LinearDistortion
public import TauCeti.Analysis.InnerProductSpace.LinearDistortion
import TauCeti.Analysis.InnerProductSpace.LinearDistortion.Comparison
public import Mathlib.LinearAlgebra.Complex.Orientation

/-!
# Outer and inner distortion of a planar linear map

Every real-linear map of the plane `ℂ` is `A = TauCeti.wirtingerPartsCLM a b`, `z ↦ z a + conj z b`,
for unique `a b : ℂ`. With `ℂ` oriented by the basis `(1, i)` (`Complex.orientation`) on both
sides, this file computes the outer and inner distortion of `A` in terms of `a` and `b`:

* the oriented Jacobian is `J(A) = |a|² - |b|²`
  (`TauCeti.orientedJacobian_wirtingerPartsCLM`);
* if `|b| < |a|` then `q_O(A) = q_I(A) = (|a| + |b|) / (|a| - |b|)`
  (`TauCeti.outerDistortion_wirtingerPartsCLM_of_lt`,
  `TauCeti.innerDistortion_wirtingerPartsCLM_of_lt`);
* if `|a| ≤ |b|` and `b ≠ 0` then `q_O(A) = ∞` and `q_I(A) = 0`
  (`TauCeti.outerDistortion_wirtingerPartsCLM_of_le`,
  `TauCeti.innerDistortion_wirtingerPartsCLM_of_le`);
* for `0 ≤ k < 1`, `q_O(A) ≤ (1 + k) / (1 - k)` exactly when `|b| ≤ k |a|`
  (`TauCeti.outerDistortion_wirtingerPartsCLM_le_iff`): the Beltrami coefficient `b / a` of a
  `K`-quasiconformal planar map has modulus at most `k = (K - 1) / (K + 1)`.

## References

* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter I.
-/

public section

noncomputable section

open Complex Module
open scoped ENNReal

namespace TauCeti

attribute [local instance] Complex.finrank_real_complex_fact

/-- The oriented Jacobian of `z ↦ z a + conj z b`, for the orientation of `ℂ` by the basis
`(1, i)`, is `|a|² - |b|²`. -/
@[simp]
theorem orientedJacobian_wirtingerPartsCLM (a b : ℂ) :
    Complex.orientation.orientedJacobian Complex.orientation
        (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) = ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
  rw [Orientation.orientedJacobian_self, det_wirtingerPartsCLM]

/-- The operator norm of `z ↦ z a + conj z b`, read as a linear map, is `|a| + |b|`. -/
theorem norm_toContinuousLinearMap_wirtingerPartsCLM (a b : ℂ) :
    ‖LinearMap.toContinuousLinearMap (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ)‖ = ‖a‖ + ‖b‖ :=
  norm_wirtingerPartsCLM a b

/-- If `|b| < |a|`, the outer distortion of `z ↦ z a + conj z b` is
`(|a| + |b|) / (|a| - |b|)`. -/
theorem outerDistortion_wirtingerPartsCLM_of_lt {a b : ℂ} (h : ‖b‖ < ‖a‖) :
    Complex.orientation.outerDistortion Complex.orientation (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) =
      ENNReal.ofReal ((‖a‖ + ‖b‖) / (‖a‖ - ‖b‖)) := by
  have hs : 0 < ‖a‖ - ‖b‖ := sub_pos.mpr h
  have hJ : 0 < ‖a‖ ^ 2 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  rw [Orientation.outerDistortion_of_pos _ _ (by rwa [orientedJacobian_wirtingerPartsCLM]),
    orientedJacobian_wirtingerPartsCLM, norm_toContinuousLinearMap_wirtingerPartsCLM]
  congr 1
  rw [div_eq_div_iff hJ.ne' hs.ne']
  ring

/-- If `|b| < |a|`, the inner distortion of `z ↦ z a + conj z b` is
`(|a| + |b|) / (|a| - |b|)`, the same as its outer distortion. -/
theorem innerDistortion_wirtingerPartsCLM_of_lt {a b : ℂ} (h : ‖b‖ < ‖a‖) :
    Complex.orientation.innerDistortion Complex.orientation (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) =
      (‖a‖ + ‖b‖) / (‖a‖ - ‖b‖) := by
  have hs : 0 < ‖a‖ - ‖b‖ := sub_pos.mpr h
  have hJ : 0 < ‖a‖ ^ 2 - ‖b‖ ^ 2 := by nlinarith [norm_nonneg b]
  rw [Orientation.innerDistortion_of_pos _ _ (by rwa [orientedJacobian_wirtingerPartsCLM]),
    orientedJacobian_wirtingerPartsCLM, minimalStretch_wirtingerPartsCLM, abs_of_pos hs,
    div_eq_div_iff (pow_pos hs 2).ne' hs.ne']
  ring

/-- If `|a| ≤ |b|` and `b ≠ 0`, the map `z ↦ z a + conj z b` is nonzero and does not preserve
orientation strictly, so its outer distortion is `∞`. -/
theorem outerDistortion_wirtingerPartsCLM_of_le {a b : ℂ} (h : ‖a‖ ≤ ‖b‖) (hb : b ≠ 0) :
    Complex.orientation.outerDistortion Complex.orientation
        (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) = ⊤ := by
  refine Orientation.outerDistortion_of_nonpos _ _ ?_ fun h0 ↦ ?_
  · rw [orientedJacobian_wirtingerPartsCLM, sub_nonpos]
    exact pow_le_pow_left₀ (norm_nonneg a) h 2
  · have := norm_toContinuousLinearMap_wirtingerPartsCLM a b
    rw [h0, map_zero, norm_zero] at this
    linarith [norm_nonneg a, norm_pos_iff.mpr hb]

/-- If `|a| ≤ |b|`, the inner distortion of `z ↦ z a + conj z b` is `0`. -/
theorem innerDistortion_wirtingerPartsCLM_of_le {a b : ℂ} (h : ‖a‖ ≤ ‖b‖) :
    Complex.orientation.innerDistortion Complex.orientation
        (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) = 0 := by
  refine Orientation.innerDistortion_of_nonpos _ _ ?_
  rw [orientedJacobian_wirtingerPartsCLM, sub_nonpos]
  exact pow_le_pow_left₀ (norm_nonneg a) h 2

/-- For `0 ≤ k < 1`, the outer distortion of `z ↦ z a + conj z b` is at most `(1 + k) / (1 - k)`
exactly when `|b| ≤ k |a|`. -/
theorem outerDistortion_wirtingerPartsCLM_le_iff {k : ℝ} (hk₀ : 0 ≤ k) (hk₁ : k < 1) (a b : ℂ) :
    Complex.orientation.outerDistortion Complex.orientation
        (wirtingerPartsCLM a b : ℂ →ₗ[ℝ] ℂ) ≤ ENNReal.ofReal ((1 + k) / (1 - k)) ↔
      ‖b‖ ≤ k * ‖a‖ := by
  have h1k : 0 < 1 - k := sub_pos.mpr hk₁
  rw [Orientation.outerDistortion_le_ofReal_iff _ _ two_pos (by positivity),
    orientedJacobian_wirtingerPartsCLM, norm_toContinuousLinearMap_wirtingerPartsCLM]
  have hab : 0 ≤ ‖a‖ + ‖b‖ := by positivity
  rcases hab.eq_or_lt with h0 | h0
  · have ha : ‖a‖ = 0 := by linarith [norm_nonneg a, norm_nonneg b]
    have hb : ‖b‖ = 0 := by linarith [norm_nonneg a, norm_nonneg b]
    simp [ha, hb]
  -- `(s + t)² ≤ K (s² - t²)` iff `s + t ≤ K (s - t)` iff `(s + t)(1 - k) ≤ (1 + k)(s - t)`.
  have key : (‖a‖ + ‖b‖) ^ 2 ≤ (1 + k) / (1 - k) * (‖a‖ ^ 2 - ‖b‖ ^ 2) ↔
      (‖a‖ + ‖b‖) * (1 - k) ≤ (1 + k) * (‖a‖ - ‖b‖) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ h1k,
      show (1 + k) * (‖a‖ ^ 2 - ‖b‖ ^ 2) = (‖a‖ + ‖b‖) * ((1 + k) * (‖a‖ - ‖b‖)) by ring,
      show (‖a‖ + ‖b‖) ^ 2 * (1 - k) = (‖a‖ + ‖b‖) * ((‖a‖ + ‖b‖) * (1 - k)) by ring,
      mul_le_mul_iff_right₀ h0]
  rw [key]
  constructor <;> intro h <;> linarith

/-! ### Checks -/

/-- Check: `z ↦ z + conj z / 2` has `q_O = (9/4) / (3/4) = 3`. -/
example :
    Complex.orientation.outerDistortion Complex.orientation
        (wirtingerPartsCLM (1 : ℂ) (1 / 2) : ℂ →ₗ[ℝ] ℂ) = 3 := by
  have h : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [outerDistortion_wirtingerPartsCLM_of_lt (by rw [h, norm_one]; norm_num), h, norm_one]
  norm_num

/-- Check: complex conjugation has `J = -1` and `q_O = ∞`. -/
example :
    Complex.orientation.orientedJacobian Complex.orientation
        (wirtingerPartsCLM (0 : ℂ) 1 : ℂ →ₗ[ℝ] ℂ) = -1 ∧
      Complex.orientation.outerDistortion Complex.orientation
        (wirtingerPartsCLM (0 : ℂ) 1 : ℂ →ₗ[ℝ] ℂ) = ⊤ := by
  refine ⟨?_, outerDistortion_wirtingerPartsCLM_of_le (by simp) one_ne_zero⟩
  rw [orientedJacobian_wirtingerPartsCLM]
  norm_num

/-- Check: `z ↦ 2 i z` has `q_O = 1`. -/
example :
    Complex.orientation.outerDistortion Complex.orientation
        (wirtingerPartsCLM (2 * I) (0 : ℂ) : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have h : ‖(2 * I : ℂ)‖ = 2 := by simp
  rw [outerDistortion_wirtingerPartsCLM_of_lt (by rw [h, norm_zero]; norm_num), h, norm_zero]
  norm_num

/-- Check: `K = 2` corresponds to `k = 1/3`, and `z ↦ z + conj z / 3` has
`q_O = (4/3) / (2/3) = 2`. -/
example :
    (1 + 1 / 3 : ℝ) / (1 - 1 / 3) = 2 ∧
      Complex.orientation.outerDistortion Complex.orientation
        (wirtingerPartsCLM (1 : ℂ) (1 / 3) : ℂ →ₗ[ℝ] ℂ) = 2 := by
  have h : ‖(1 / 3 : ℂ)‖ = 1 / 3 := by simp
  refine ⟨by norm_num, ?_⟩
  rw [outerDistortion_wirtingerPartsCLM_of_lt (by rw [h, norm_one]; norm_num), h, norm_one]
  norm_num

end TauCeti
