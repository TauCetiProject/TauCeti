/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The logarithmic size of the auxiliary level

In a theta-lift chain the auxiliary level `M` and the root discriminant `D` enter the
level-prime window and the Stirling bound for long rows through `log (M * D / (2 * π))`.
The bounds below control that common term independently of the chain length and weights.
The normalization follows `New.Data.abs_log_M_mul_rootDisc_le` in lsernau/grh-lean
(`grh/src/New/Reduction/Data/Sizes.lean`, revision `72fead1`).
-/

public section

open Real Set

namespace TauCeti.ThetaLift

/-- On the logarithmic scale `L`, the auxiliary level in `[exp(20L), exp(22L)]` and the root
discriminant in `[1, exp L]` give a logarithmic coefficient between `19L` and `23L`.
In particular its absolute value is at most `23L`. -/
theorem log_M_mul_rootDiscr_div_two_pi_mem_Icc {M D L : ℝ} (hL : log (2 * π) ≤ L)
    (hM : M ∈ Icc (exp (20 * L)) (exp (22 * L))) (hD : D ∈ Icc 1 (exp L)) :
    log (M * D / (2 * π)) ∈ Icc (19 * L) (23 * L) := by
  have hMpos := (exp_pos _).trans_le hM.1
  have hDpos := zero_lt_one.trans_le hD.1
  have hπ : 0 ≤ log (2 * π) := log_nonneg (by linarith [pi_gt_three])
  have hMlo := (le_log_iff_exp_le hMpos).2 hM.1
  have hMhi := (log_le_iff_le_exp hMpos).2 hM.2
  have hDlo := log_nonneg hD.1
  have hDhi := (log_le_iff_le_exp hDpos).2 hD.2
  rw [log_div (mul_ne_zero hMpos.ne' hDpos.ne') (by positivity), log_mul hMpos.ne' hDpos.ne']
  exact ⟨by linarith only [hMlo, hDlo, hL], by linarith only [hMhi, hDhi, hπ]⟩

end TauCeti.ThetaLift
