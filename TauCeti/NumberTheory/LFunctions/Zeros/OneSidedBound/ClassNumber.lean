/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.EffectiveBounds.ClassNumber.RootDiscr
import TauCeti.NumberTheory.NumberField.ClassNumber.RingEquiv

/-!
# Class numbers at the theta-lift scale

For a coefficient field, control its logarithmic class number by the
same scale that bounds the root discriminant and the number of infinite places. The
logarithmic bound is used to budget the denominators of projections onto theta lifts.

The scale and target follow `New.Data.log_classNumber_le` in the shorter formalization of
Dirichlet GRH (`grh/src/New/Reduction/Data/Sizes.lean` in `lsernau/grh-lean`, commit `72fead1`).
The estimate here uses `NumberField.classNumber_le_bound` instead of counting ideals anew.
-/

public section

open Module NumberField NumberField.InfinitePlace Real

namespace TauCeti.OneSidedBound

/-- If the number of infinite places and the root discriminant of a number field are both
bounded by `x ^ 12`, its logarithmic class number is at most `x ^ 30`. -/
theorem log_classNumber_le (K : Type*) [Field K] [NumberField K]
    {x : ℕ} (hplaces : Fintype.card (InfinitePlace K) ≤ x ^ 12)
    (hroot : rootDiscr K ≤ (x : ℝ) ^ 12) : log (classNumber K) ≤ (x : ℝ) ^ 30 := by
  have hdegree : finrank ℚ K ≤ 2 * x ^ 12 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces] at hplaces
    have := card_add_two_mul_card_eq_rank K
    omega
  have hpos : 0 < finrank ℚ K := finrank_pos
  rcases lt_or_ge x 2 with hx | hx
  · -- A root discriminant at most one forces the small-scale case to be rational.
    have hx' : x = 1 := by
      by_contra! h
      have : x = 0 := by omega
      simp only [this, zero_pow (by decide : (12 : ℕ) ≠ 0), mul_zero] at hdegree
      omega
    have hd : finrank ℚ K = 1 := by
      by_contra! h
      have h' : (2 : ℝ) < |(discr K : ℝ)| := by
        exact_mod_cast abs_discr_gt_two (K := K) (by omega)
      have hgt : 1 < rootDiscr K := by
        rw [rootDiscr_def, Int.cast_abs, ← one_rpow ((finrank ℚ K : ℝ)⁻¹)]
        exact rpow_lt_rpow zero_le_one (by linarith) (by positivity)
      exact hgt.not_ge (by simpa only [hx', Nat.cast_one, one_pow] using hroot)
    obtain ⟨e⟩ := (nonempty_algEquiv_iff_finrank_eq_one (R := ℚ) (S := K)).mpr hd
    rw [← e.toRingEquiv.classNumber_eq, Rat.classNumber_eq, hx']
    simp
  · have hx' : (2 : ℝ) ≤ x := by exact_mod_cast hx
    have hxpos : (0 : ℝ) < x := by linarith
    have hlog : log (4 * (x : ℝ) ^ 12) ≤ 12 * (x : ℝ) := by
      rw [log_mul (by norm_num) (by positivity), log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [log_le_sub_one_of_pos hxpos, log_le_sub_one_of_pos (by norm_num : 0 < (4 : ℝ))]
    have hfin : (finrank ℚ K : ℝ) ≤ 2 * (x : ℝ) ^ 12 := by exact_mod_cast hdegree
    have hpow : (24 : ℝ) ≤ (x : ℝ) ^ 17 :=
      (by norm_num : (24 : ℝ) ≤ 2 ^ 17).trans (pow_le_pow_left₀ (by norm_num) hx' 17)
    calc
      log (classNumber K) ≤ (finrank ℚ K : ℝ) * log (4 * (x : ℝ) ^ 12) :=
        log_classNumber_le_finrank_mul_log_of_rootDiscr_le K hroot
      _ ≤ (finrank ℚ K : ℝ) * (12 * (x : ℝ)) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (2 * (x : ℝ) ^ 12) * (12 * (x : ℝ)) := mul_le_mul_of_nonneg_right hfin (by positivity)
      _ = (x : ℝ) ^ 13 * 24 := by ring
      _ ≤ (x : ℝ) ^ 13 * (x : ℝ) ^ 17 := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (x : ℝ) ^ 30 := by ring

end TauCeti.OneSidedBound
