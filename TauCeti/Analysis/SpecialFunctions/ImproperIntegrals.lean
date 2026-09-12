/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Improper integrals with logarithmic decay

This file extends Mathlib's improper-integral estimates with integrability at infinity of
`(t (1 + log t) ^ 2)⁻¹`.

## Main declarations

* `TauCeti.integrableAtFilter_inv_mul_one_add_log_sq`: the function
  `t ↦ (t (1 + log t) ^ 2)⁻¹` is integrable at infinity.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set

/-- The function `(t (1 + log t) ^ 2)⁻¹` is integrable at infinity. On `Ioi 1` it is dominated
by Mathlib's log-Cauchy density `(t (1 + (log t) ^ 2))⁻¹`. -/
theorem integrableAtFilter_inv_mul_one_add_log_sq :
    IntegrableAtFilter (fun u : ℝ ↦ (u * (1 + Real.log u) ^ 2)⁻¹) atTop := by
  refine ⟨Ioi 1, Ioi_mem_atTop 1, ?_⟩
  have hmaj : IntegrableOn (fun u : ℝ ↦ (u * (1 + Real.log u ^ 2))⁻¹) (Ioi (1 : ℝ)) :=
    ((integrableOn_Ioi_zero_inv_mul_one_add_log_sq (b := 1) one_ne_zero).congr_fun
      (fun u _ ↦ by rw [one_mul]) measurableSet_Ioi).mono_set (Ioi_subset_Ioi zero_le_one)
  refine MeasureTheory.Integrable.mono hmaj (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu1 : (1 : ℝ) < u := hu
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu1
  have hL : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1.le
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  gcongr
  nlinarith

end TauCeti
