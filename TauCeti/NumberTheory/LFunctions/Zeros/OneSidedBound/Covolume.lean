/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Covolume comparison for a one-sided prime-sum bound

An upper covolume bound on a nearly full-dimensional span and a lower bound involving
its index share a main term. Cancelling the main term controls the weighted remainder
that occurs only in the upper bound. The comparison and normalization follow the
statement of `New.star_inequality` in `lsernau/grh-lean` (commit `72fead1`).
-/

public section

open Real

namespace TauCeti.OneSidedBound

private theorem covolume_scale_bounds {b : ℝ} (hb : 64 ≤ log b) :
    4 / b ^ 2 ≤ (1 / 8 : ℝ) ∧
      4 * log b ^ 4 + 20 * log (1 + 2 * b ^ 2) * log b ^ 3 ≤ 7 / 8 * log b ^ 5 := by
  have hL : 0 ≤ log b := by linarith
  have hb₀ : b ≠ 0 := by rintro rfl; norm_num at hb
  have hbpos : 0 < b ^ 2 := sq_pos_of_ne_zero hb₀
  have hb₂ : 1 + 2 * log b ≤ b ^ 2 := by
    have h := log_le_sub_one_of_pos hbpos
    rw [log_pow] at h
    norm_num at h
    linarith
  refine ⟨(div_le_iff₀ hbpos).2 (by linarith), ?_⟩
  have hlog : log (1 + 2 * b ^ 2) ≤ (9 / 4 : ℝ) * log b := by
    calc
      log (1 + 2 * b ^ 2) ≤ log (3 * b ^ 2) := by gcongr; linarith
      _ = log 3 + 2 * log b := by
        rw [log_mul (by norm_num) hbpos.ne', log_pow]
        norm_num
      _ ≤ _ := by linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
  calc
    _ ≤ 4 * log b ^ 4 + 20 * ((9 / 4) * log b) * log b ^ 3 := by gcongr
    _ = 49 * log b ^ 4 := by ring
    _ ≤ (7 / 8 * log b) * log b ^ 4 := by gcongr; linarith
    _ = _ := by ring

/-- Compare the covolume and index bounds for a family of rank `n` in a target of rank `d`.
Here `A` is the product of the number of infinite places and the large derivative order,
`H` is the shared main amount, and `r` is the total remainder weighted by the chain length.
A span missing at most a fraction `4/b²` of the target suffices for `r ≤ A (log b)^5`. -/
theorem weightedRemainder_le_of_covolume_bounds {n d : ℕ} {b A H r c i : ℝ}
    (hb : 64 ≤ log b) (hd : 0 < d) (hnd : n ≤ d)
    (hspan : (1 - 4 / b ^ 2) * (d : ℝ) ≤ n) (hA : 0 ≤ A) (hH : 0 ≤ H + A * log b ^ 4)
    (hc : c ≤ (n : ℝ) * (H - r + A * log b ^ 4))
    (hi : i ≤ (d : ℝ) * (10 * log (1 + 2 * b ^ 2) * (A * log b ^ 3)))
    (hlower : (d : ℝ) * (H - 3 * A * log b ^ 4) ≤ c + 2 * i) :
    r ≤ A * log b ^ 5 := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hnd' : (n : ℝ) ≤ d := by exact_mod_cast hnd
  obtain ⟨hfrac, herr⟩ := covolume_scale_bounds hb
  have hspan' : (7 / 8 : ℝ) * (d : ℝ) ≤ n :=
    (mul_le_mul_of_nonneg_right (by linarith : (7 / 8 : ℝ) ≤ 1 - 4 / b ^ 2) hd'.le).trans hspan
  have hn : 0 < (n : ℝ) := lt_of_lt_of_le (by positivity) hspan'
  -- Replace only the common main amount by its all-target value, not the signed remainder.
  have hcancel := mul_le_mul_of_nonneg_right hnd' hH
  have hr : (n : ℝ) * r ≤ (d : ℝ) * A *
      (4 * log b ^ 4 + 20 * log (1 + 2 * b ^ 2) * log b ^ 3) := by
    linear_combination hlower + hc + 2 * hi + hcancel
  have hbudget : (d : ℝ) * A *
      (4 * log b ^ 4 + 20 * log (1 + 2 * b ^ 2) * log b ^ 3) ≤
      ((7 / 8 : ℝ) * (d : ℝ)) * (A * log b ^ 5) := by
    calc
      _ ≤ (d : ℝ) * A * (7 / 8 * log b ^ 5) :=
        mul_le_mul_of_nonneg_left herr (by positivity)
      _ = _ := by ring
  have hnonneg : 0 ≤ A * log b ^ 5 := mul_nonneg hA (pow_nonneg (by linarith) _)
  exact le_of_mul_le_mul_left
    (hr.trans (hbudget.trans (mul_le_mul_of_nonneg_right hspan' hnonneg))) hn

end TauCeti.OneSidedBound
