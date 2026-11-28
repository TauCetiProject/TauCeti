/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Orthonormal

/-!
# Dilated Hermite functions

For a scale `c` the dilated Hermite function `x ↦ √c ψₖ(c x)` is the image of the Hermite
function `ψₖ` (`TauCeti.hermiteFunction`) under the dilation by `c`, normalized so that for
`0 < c` the dilation is unitary on `L²(ℝ)`. The dilated functions are therefore again orthonormal.

## Main definitions

* `TauCeti.dilatedHermiteFunction c k`: the function `x ↦ √c ψₖ(c x)`.

## Main results

* `TauCeti.memLp_two_dilatedHermiteFunction`: the dilated Hermite functions are square
  integrable.
* `TauCeti.integral_dilatedHermiteFunction_mul_dilatedHermiteFunction`: for `0 < c` the dilated
  Hermite functions are orthonormal in `L²(ℝ)`.
-/

public section

namespace TauCeti

open MeasureTheory Real

/-- The `k`th Hermite function **dilated by the scale `c`**, `x ↦ √c ψₖ(c x)`. The outer factor
makes the dilation unitary on `L²(ℝ)` when `0 < c`. -/
noncomputable def dilatedHermiteFunction (c : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  √c * hermiteFunction k (c * x)

/-- Defining formula for `TauCeti.dilatedHermiteFunction`. -/
theorem dilatedHermiteFunction_def (c : ℝ) (k : ℕ) (x : ℝ) :
    dilatedHermiteFunction c k x = √c * hermiteFunction k (c * x) := (rfl)

/-- The dilated Hermite functions are continuous. -/
@[fun_prop]
theorem continuous_dilatedHermiteFunction (c : ℝ) (k : ℕ) :
    Continuous (dilatedHermiteFunction c k) :=
  continuous_const.mul ((continuous_hermiteFunction k).comp (continuous_const.mul continuous_id))

/-- The dilated Hermite functions are square integrable. -/
theorem memLp_two_dilatedHermiteFunction (c : ℝ) (k : ℕ) :
    MemLp (dilatedHermiteFunction c k) 2 volume := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : dilatedHermiteFunction 0 k = 0 := funext fun x ↦ by
      simp [dilatedHermiteFunction_def]
    rw [h0]
    exact MemLp.zero
  refine (memLp_two_iff_integrable_sq
    (continuous_dilatedHermiteFunction c k).aestronglyMeasurable).2 ?_
  refine (((memLp_two_hermiteFunction k).integrable_sq.comp_mul_left' hc).const_mul
    (√c ^ 2)).congr (.of_forall fun x ↦ ?_)
  simp [dilatedHermiteFunction_def, mul_pow]

/-- **Orthonormality** of the dilated Hermite functions: for `0 < c`,
`∫ x, √c ψᵢ(c x) · √c ψⱼ(c x) = if i = j then 1 else 0`. -/
theorem integral_dilatedHermiteFunction_mul_dilatedHermiteFunction {c : ℝ} (hc : 0 < c)
    (i j : ℕ) :
    ∫ x, dilatedHermiteFunction c i x * dilatedHermiteFunction c j x =
      if i = j then 1 else 0 := by
  have h := Measure.integral_comp_mul_left
    (fun y ↦ hermiteFunction i y * hermiteFunction j y) c
  simp only [dilatedHermiteFunction_def, mul_mul_mul_comm (√c), mul_self_sqrt hc.le]
  rw [integral_const_mul, h, integral_hermiteFunction_mul_hermiteFunction, abs_inv,
    abs_of_pos hc, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

end TauCeti
