/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int

/-!
# Nearest multiples of an integer

Every integer `t` lies within `|μ| / 2` of a multiple of a nonzero integer `μ`. It is stated
without division, as `2 · |t - c μ| ≤ |μ|`. The multiple comes from Lean's balanced division
`Int.bdiv`, whose remainder `Int.bmod t m` lies in `[-(m / 2), (m + 1) / 2)` for `0 < m`.

Whenever a multiple `c μ` lies strictly closer than `|μ|` to `t` (in particular whenever
`2 · |t - c μ| ≤ |μ|` and `μ ≠ 0`), the distance `|t - c μ|` vanishes if and only if `μ ∣ t`.
Moreover, `t` lies strictly closer than `|μ| / 2` to some multiple of `μ` if and only if
`μ ∣ 2 t` implies `μ ∣ t`, isolating the midpoint case of odd multiples of `μ / 2` for even `μ`.

## Main results

* `Int.exists_two_mul_abs_sub_mul_le` : `∃ c, 2 * |t - c * μ| ≤ |μ|` for `μ ≠ 0`.
* `Int.abs_sub_mul_eq_zero_iff_dvd` : `|t - c * μ| = 0 ↔ μ ∣ t` when `|t - c * μ| < |μ|`.
* `Int.exists_two_mul_abs_sub_mul_lt_iff` : for `μ ≠ 0`,
  `(∃ c, 2 * |t - c * μ| < |μ|) ↔ (μ ∣ 2 * t → μ ∣ t)`.
-/

public section

namespace Int

/-- Every integer lies within `|μ| / 2` of a multiple of a nonzero integer `μ`. -/
theorem exists_two_mul_abs_sub_mul_le (t : ℤ) {μ : ℤ} (hμ : μ ≠ 0) :
    ∃ c : ℤ, 2 * |t - c * μ| ≤ |μ| := by
  have hm : 0 < μ.natAbs := natAbs_pos.mpr hμ
  refine ⟨t.bdiv μ.natAbs * μ.sign, ?_⟩
  have h₁ := t.le_bmod hm
  have h₂ := t.bmod_lt hm
  have h := t.bdiv_add_bmod' μ.natAbs
  rw [mul_assoc, sign_mul_self, abs_eq_natAbs, abs_eq_natAbs]
  omega

/-- For a multiple `c * μ` at distance strictly less than `|μ|` from `t`, the distance
`|t - c * μ|` vanishes if and only if `μ ∣ t`. In particular, this applies whenever
`2 * |t - c * μ| ≤ |μ|` and `μ ≠ 0`. -/
theorem abs_sub_mul_eq_zero_iff_dvd {t c μ : ℤ} (h : |t - c * μ| < |μ|) :
    |t - c * μ| = 0 ↔ μ ∣ t := by
  rw [abs_eq_natAbs]
  rw [abs_eq_natAbs, abs_eq_natAbs] at h
  refine ⟨fun h₀ ↦ ⟨c, ?_⟩, ?_⟩
  · have ht : t = c * μ := by omega
    rw [ht, mul_comm]
  · rintro ⟨d, rfl⟩
    have hdvd : μ ∣ μ * d - c * μ := ⟨d - c, by rw [mul_sub, mul_comm c μ]⟩
    have hrem := eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by omega)
    omega

/-- For `μ ≠ 0`, an integer `t` lies strictly closer than `|μ| / 2` to some multiple of `μ` if
and only if `μ ∣ 2 * t` implies `μ ∣ t`. Thus the only integers with no strict nearest multiple
are the odd multiples of `μ / 2` when `μ` is even. -/
theorem exists_two_mul_abs_sub_mul_lt_iff {t μ : ℤ} (hμ : μ ≠ 0) :
    (∃ c : ℤ, 2 * |t - c * μ| < |μ|) ↔ (μ ∣ 2 * t → μ ∣ t) := by
  constructor
  · rintro ⟨c, hc⟩ h₂
    have hlt : |2 * t - (2 * c) * μ| < |μ| := by
      rw [abs_eq_natAbs, abs_eq_natAbs] at hc ⊢
      rw [mul_assoc, ← mul_sub, natAbs_mul]
      simpa using hc
    have hzero := (abs_sub_mul_eq_zero_iff_dvd hlt).mpr h₂
    rw [abs_eq_natAbs, mul_assoc] at hzero
    refine ⟨c, ?_⟩
    have ht : t = c * μ := by omega
    rw [ht, mul_comm]
  · intro h
    obtain ⟨c, hc⟩ := exists_two_mul_abs_sub_mul_le t hμ
    rcases lt_or_eq_of_le hc with hlt | heq
    · exact ⟨c, hlt⟩
    · rw [abs_eq_natAbs, abs_eq_natAbs] at heq
      have hdvd₂ : μ ∣ 2 * t := by
        have hsign : 2 * (t - c * μ) = μ ∨ 2 * (t - c * μ) = -μ := by omega
        rcases hsign with h' | h'
        · refine ⟨2 * c + 1, ?_⟩
          rw [mul_add, mul_one, mul_comm μ (2 * c), mul_assoc]
          omega
        · refine ⟨2 * c - 1, ?_⟩
          rw [mul_sub, mul_one, mul_comm μ (2 * c), mul_assoc]
          omega
      obtain ⟨d, rfl⟩ := h hdvd₂
      refine ⟨d, ?_⟩
      have hm : 0 < μ.natAbs := natAbs_pos.mpr hμ
      rw [mul_comm μ d, abs_eq_natAbs, abs_eq_natAbs]
      omega

end Int
