/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Geometric decay along geometric levels is power decay

Let `g` be antitone, bounded by `V`, and suppose that `g (Mʲ) ≤ δʲ V` for every `j`, with
`M > 1` and `0 < δ ≤ 1`. Every `t ≥ 1` lies between two consecutive levels `Mʲ ≤ t < M^(j+1)`, so
`g t ≤ δʲ V ≤ δ⁻¹ t^(log δ / log M) V`. For `δ < 1` the exponent is negative, and the geometric
decay along the levels is power decay at every level.

This is the last step of the Krylov–Safonov `L^ε` estimate, where `g t` is the measure of the
superlevel set `{u ≥ t}`.

## Main declarations

* `TauCeti.le_ofReal_inv_mul_rpow_mul_of_forall_le_pow_mul`: geometric decay along the levels
  `Mʲ` of an antitone function gives power decay at every level.

## References

* L. A. Caffarelli and X. Cabré, *Fully Nonlinear Elliptic Equations*, AMS Colloquium
  Publications **43** (1995), proof of Lemma 4.6.
-/

public section

open scoped ENNReal

namespace TauCeti

/-- **Geometric decay along the levels `Mʲ` gives power decay.** If an antitone `g` is bounded
by `V` and satisfies `g (Mʲ) ≤ δʲ V` for every `j`, with `M > 1` and `0 < δ ≤ 1`, then
`g t ≤ δ⁻¹ t^(log δ / log M) V` for every `t > 0`. For `δ < 1` the exponent `log δ / log M` is
negative. -/
theorem le_ofReal_inv_mul_rpow_mul_of_forall_le_pow_mul {M δ t : ℝ} {g : ℝ → ℝ≥0∞} {V : ℝ≥0∞}
    (hM : 1 < M) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hg : Antitone g) (hgV : ∀ s, g s ≤ V)
    (hgj : ∀ j : ℕ, g (M ^ j) ≤ ENNReal.ofReal δ ^ j * V) (ht : 0 < t) :
    g t ≤ ENNReal.ofReal (δ⁻¹ * t ^ (Real.log δ / Real.log M)) * V := by
  have he : Real.log δ / Real.log M ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos hδ0.le hδ1) (Real.log_pos hM).le
  rcases lt_or_ge t 1 with ht1 | ht1
  · -- Below level `1` the bound is at least `V`.
    refine (hgV t).trans (le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 ?_))
    exact one_le_mul_of_one_le_of_one_le (one_le_inv₀ hδ0 |>.2 hδ1)
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1.le he)
  -- Above level `1`, `t` lies between two consecutive levels `Mʲ ≤ t < M^(j+1)`.
  obtain ⟨j, hjt, htj⟩ := exists_nat_pow_near ht1 hM
  have hMe : M ^ (Real.log δ / Real.log M) = δ := by
    rw [Real.rpow_def_of_pos (by linarith), mul_div_cancel₀ _ (Real.log_pos hM).ne',
      Real.exp_log hδ0]
  have hδj : δ ^ (j + 1) ≤ t ^ (Real.log δ / Real.log M) := by
    calc δ ^ (j + 1) = (M ^ (Real.log δ / Real.log M)) ^ (j + 1) := by rw [hMe]
      _ = (M ^ (j + 1)) ^ (Real.log δ / Real.log M) := Real.rpow_pow_comm (by linarith) _ _
      _ ≤ t ^ (Real.log δ / Real.log M) := Real.rpow_le_rpow_of_nonpos ht htj.le he
  refine (hg hjt).trans ((hgj j).trans ?_)
  rw [← ENNReal.ofReal_pow hδ0.le]
  gcongr
  rw [pow_succ] at hδj
  calc δ ^ j = δ⁻¹ * (δ ^ j * δ) := by field_simp
    _ ≤ δ⁻¹ * t ^ (Real.log δ / Real.log M) := by gcongr

end TauCeti
