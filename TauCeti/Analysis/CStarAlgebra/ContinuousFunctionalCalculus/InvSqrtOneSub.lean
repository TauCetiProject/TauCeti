/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# The inverse square root of `1 - h`

For a self-adjoint element `h` of a unital C⋆-algebra with `‖h‖ < 1`, the spectrum of `h` lies in
`(-1, 1)`, so `1 - h` is invertible and positive, with inverse square root
`(1 - h) ^ (-1 / 2) = cfc (fun t ↦ (√(1 - t))⁻¹) h`. This element is the correction factor in the
polar decompositions that turn approximate partial isometries into exact ones.

## Main results

* `TauCeti.cfc_inv_sqrt_one_sub_mul_one_sub`: `(1 - h) ^ (-1 / 2) * (1 - h) = (1 - h) ^ (1 / 2)`.
* `TauCeti.cfc_inv_sqrt_one_sub_mul_self_mul_one_sub`:
  `(1 - h) ^ (-1 / 2) * (1 - h) ^ (-1 / 2) * (1 - h) = 1`.
-/

public section

namespace TauCeti

variable {A : Type*} [CStarAlgebra A] {h : A}

private theorem one_sub_eq_cfc (hh : IsSelfAdjoint h) : 1 - h = cfc (fun t : ℝ ↦ 1 - t) h := by
  rw [cfc_sub (fun _ : ℝ ↦ (1 : ℝ)) (fun t : ℝ ↦ t) h, cfc_const_one ℝ h, cfc_id' ℝ h]

variable (hh : IsSelfAdjoint h) (h₁ : ‖h‖ < 1)
include h₁

private theorem one_sub_pos_of_mem_spectrum {t : ℝ} (ht : t ∈ spectrum ℝ h) : 0 < 1 - t := by
  have := spectrum.norm_le_norm_of_mem ht
  rw [Real.norm_eq_abs] at this
  linarith [le_abs_self t]

private theorem continuousOn_inv_sqrt_one_sub :
    ContinuousOn (fun t : ℝ ↦ (√(1 - t))⁻¹) (spectrum ℝ h) :=
  ContinuousOn.inv₀ (by fun_prop) fun _ ht ↦
    (Real.sqrt_pos.2 (one_sub_pos_of_mem_spectrum h₁ ht)).ne'

include hh

/-- For a self-adjoint `h` with `‖h‖ < 1`, `(1 - h) ^ (-1 / 2) * (1 - h) = (1 - h) ^ (1 / 2)`. -/
theorem cfc_inv_sqrt_one_sub_mul_one_sub :
    cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h * (1 - h) = cfc (fun t : ℝ ↦ √(1 - t)) h := by
  rw [one_sub_eq_cfc hh, ← cfc_mul _ _ h (continuousOn_inv_sqrt_one_sub h₁) (by fun_prop)]
  refine cfc_congr fun t ht ↦ ?_
  have h₀ := one_sub_pos_of_mem_spectrum h₁ ht
  have := Real.sq_sqrt h₀.le
  have := (Real.sqrt_pos.2 h₀).ne'
  field_simp
  linarith

/-- For a self-adjoint `h` with `‖h‖ < 1`,
`(1 - h) ^ (-1 / 2) * (1 - h) ^ (-1 / 2) * (1 - h) = 1`. -/
theorem cfc_inv_sqrt_one_sub_mul_self_mul_one_sub :
    cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h * cfc (fun t : ℝ ↦ (√(1 - t))⁻¹) h * (1 - h) = 1 := by
  have hc := continuousOn_inv_sqrt_one_sub h₁
  rw [mul_assoc, cfc_inv_sqrt_one_sub_mul_one_sub hh h₁, ← cfc_mul _ _ h hc (by fun_prop),
    ← cfc_const_one ℝ h]
  refine cfc_congr fun t ht ↦ ?_
  exact inv_mul_cancel₀ (Real.sqrt_pos.2 (one_sub_pos_of_mem_spectrum h₁ ht)).ne'

end TauCeti
