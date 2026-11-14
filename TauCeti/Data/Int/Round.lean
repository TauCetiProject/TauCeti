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
`Int.bdiv`, whose remainder `Int.bmod t m` lies in `[-(m / 2), (m + 1) / 2)` for `0 < m`. Within
`|t - c μ| < |μ|` (and in particular within `2 · |t - c μ| ≤ |μ|`), the distance `|t - c μ|`
vanishes if and only if `μ` divides `t`.

## Main results

* `Int.exists_two_mul_abs_sub_mul_le` : `∃ c, 2 * |t - c * μ| ≤ |μ|` for `μ ≠ 0`.
* `Int.abs_sub_mul_eq_zero_iff_dvd_of_lt` : `|t - c * μ| = 0 ↔ μ ∣ t` when `|t - c * μ| < |μ|`.
* `Int.abs_sub_mul_eq_zero_iff_dvd_of_two_mul_le` : `|t - c * μ| = 0 ↔ μ ∣ t` when
  `2 * |t - c * μ| ≤ |μ|`.
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

/-- If `t` lies strictly within `|μ|` of `c * μ`, then `|t - c * μ|` vanishes if and only if `μ`
divides `t`. -/
theorem abs_sub_mul_eq_zero_iff_dvd_of_lt {t c μ : ℤ} (h : |t - c * μ| < |μ|) :
    |t - c * μ| = 0 ↔ μ ∣ t := by
  rw [abs_eq_zero]
  refine ⟨fun h₀ ↦ ⟨c, by rw [sub_eq_zero.mp h₀, mul_comm]⟩, ?_⟩
  rintro ⟨k, rfl⟩
  rw [abs_eq_natAbs μ] at h
  exact eq_zero_of_abs_lt_dvd (natAbs_dvd.mpr ⟨k - c, by rw [mul_comm c, ← mul_sub]⟩) h

/-- If `t` lies within `|μ| / 2` of `c * μ`, in the form `2 * |t - c * μ| ≤ |μ|`, then
`|t - c * μ|` vanishes if and only if `μ` divides `t`. -/
theorem abs_sub_mul_eq_zero_iff_dvd_of_two_mul_le {t c μ : ℤ} (h : 2 * |t - c * μ| ≤ |μ|) :
    |t - c * μ| = 0 ↔ μ ∣ t := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · obtain rfl : t = 0 := by
      rw [mul_zero, sub_zero, abs_zero, abs_eq_natAbs] at h
      omega
    simp
  · refine abs_sub_mul_eq_zero_iff_dvd_of_lt ?_
    rw [abs_eq_natAbs, abs_eq_natAbs] at h ⊢
    omega

end Int
