/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.EffectiveBounds.ClassNumber.Basic

/-!
# Logarithmic class-number bounds

The logarithmic class number is bounded by the degree times a logarithm of the root
discriminant. This version of `NumberField.classNumber_le_bound` is useful in families
where the degree varies but there is a separate bound on the root discriminant.
-/

public section

open Module Real

namespace NumberField

/-- If `D` bounds the root discriminant above, the logarithmic class number is at most
`[K : ℚ] * log (4 * D)`. -/
theorem log_classNumber_le_finrank_mul_log_of_rootDiscr_le (K : Type*) [Field K] [NumberField K]
    {D : ℝ} (hD : rootDiscr K ≤ D) :
    log (classNumber K) ≤ (finrank ℚ K : ℝ) * log (4 * D) := by
  have hdegree : 0 < (finrank ℚ K : ℝ) := Nat.cast_pos.mpr (finrank_pos (R := ℚ) (M := K))
  have hdiscr : 0 < |(discr K : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))
  have hroot : 0 < rootDiscr K := by
    rw [rootDiscr_def, Int.cast_abs]
    exact rpow_pos_of_pos hdiscr _
  have hlog : (finrank ℚ K : ℝ) * log (rootDiscr K) = log |(discr K : ℝ)| := by
    rw [rootDiscr_def, Int.cast_abs, log_rpow hdiscr,
      ← mul_assoc, mul_inv_cancel₀ hdegree.ne', one_mul]
  calc
    log (classNumber K) ≤ log (|(discr K : ℝ)| * 4 ^ finrank ℚ K) :=
      log_le_log (Nat.cast_pos.mpr (classNumber_pos K)) (classNumber_le_bound K)
    _ = (finrank ℚ K : ℝ) * log (4 * rootDiscr K) := by
      rw [log_mul hdiscr.ne' (by positivity), log_pow, log_mul (by norm_num) hroot.ne',
        mul_add, hlog, add_comm]
    _ ≤ (finrank ℚ K : ℝ) * log (4 * D) :=
      mul_le_mul_of_nonneg_left (log_le_log (by positivity) (by gcongr)) hdegree.le

end NumberField
