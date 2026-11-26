/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.CardIntervalMod

/-!
# An upper bound for the integers of an interval with given residue

Mathlib's `Int.Ico_filter_modEq_card` counts the integers of `[a, b)` congruent to `v` modulo
`r > 0` exactly, as a difference of two ceilings. For estimates, the useful consequence is the
uniform bound `(b - a) / r + 1`, independent of the residue `v`: a box of side `L` in `ℤ^n`
contains at most `(L / r + 1) ^ n` points of any one residue class modulo `r`.

Through the injective affine map `b ↦ t - k b`, the same bound counts the integers `b` of an
interval `(-c, c)` with `q ∣ t - k b` (`Int.card_Ioo_filter_dvd_sub_mul_le`).
-/

public section

open Finset

namespace Int

/-- An interval `[a, b)` of integers with `a ≤ b` contains at most `(b - a) / r + 1` integers
congruent to `v` modulo `r > 0`, whatever the residue `v`. -/
theorem card_Ico_filter_modEq_le {r : ℤ} (hr : 0 < r) {a b : ℤ} (hab : a ≤ b) (v : ℤ) :
    (#{x ∈ Ico a b | x ≡ v [ZMOD r]} : ℚ) ≤ (b - a) / r + 1 := by
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hcard : ((#{x ∈ Ico a b | x ≡ v [ZMOD r]} : ℤ) : ℚ) =
      ((max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 : ℤ) : ℚ) := by
    rw [Ico_filter_modEq_card _ _ hr]
  rw [Int.cast_natCast] at hcard
  rw [hcard, Int.cast_max, Int.cast_zero, max_le_iff]
  have hba : (0 : ℚ) ≤ (b - a) / r := div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hr'.le
  refine ⟨?_, by linarith⟩
  have h₁ := Int.ceil_lt_add_one ((b - v) / (r : ℚ))
  have h₂ := Int.le_ceil ((a - v) / (r : ℚ))
  have hsplit : ((b : ℚ) - a) / r = (b - v) / r - (a - v) / r := by ring
  push_cast
  linarith

/-- For `k > 0` and `q > 0`, at most `(2 k c - 1) / q + 1` integers `b` of the interval `(-c, c)`,
`c ≥ 1`, have `q ∣ t - k b`: the map `b ↦ t - k b` sends them injectively to multiples of `q` in
an interval with `2 k c - 1` integers. -/
theorem card_Ioo_filter_dvd_sub_mul_le (t : ℤ) {k q c : ℤ} (hk : 0 < k) (hq : 0 < q)
    (hc : 1 ≤ c) : (#{b ∈ Ioo (-c) c | q ∣ t - k * b} : ℚ) ≤ (2 * k * c - 1) / q + 1 := by
  have hinj : #{b ∈ Ioo (-c) c | q ∣ t - k * b} ≤
      #{v ∈ Ico (t - k * c + 1) (t + k * c) | v ≡ 0 [ZMOD q]} := by
    refine card_le_card_of_injOn (fun b ↦ t - k * b) (fun b hb ↦ ?_) fun b _ b' _ h ↦ ?_
    · simp only [coe_filter, mem_Ioo, Set.mem_ofPred_eq] at hb
      simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq, Int.modEq_zero_iff_dvd]
      obtain ⟨⟨hb₁, hb₂⟩, hd⟩ := hb
      have h₁ : k * (-c + 1) ≤ k * b := mul_le_mul_of_nonneg_left (by omega) hk.le
      have h₂ : k * b ≤ k * (c - 1) := mul_le_mul_of_nonneg_left (by omega) hk.le
      exact ⟨⟨by linarith, by linarith⟩, hd⟩
    · simp only at h
      exact mul_left_cancel₀ hk.ne' (by linarith)
  have hkc : 0 < k * c := mul_pos hk (by omega)
  have hab : t - k * c + 1 ≤ t + k * c := by linarith
  calc (#{b ∈ Ioo (-c) c | q ∣ t - k * b} : ℚ)
      ≤ #{v ∈ Ico (t - k * c + 1) (t + k * c) | v ≡ 0 [ZMOD q]} := by exact_mod_cast hinj
    _ ≤ ((t + k * c : ℤ) - (t - k * c + 1 : ℤ)) / q + 1 := card_Ico_filter_modEq_le hq hab 0
    _ = (2 * k * c - 1) / q + 1 := by push_cast; ring

end Int
