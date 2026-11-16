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

Moreover, whenever `|t - c μ| < |μ|` — and in particular for any nearest multiple satisfying
`2 · |t - c μ| ≤ |μ|` — the remainder vanishes (`t = c μ`) if and only if `μ ∣ t`.

## Main results

* `Int.exists_two_mul_abs_sub_mul_le` : `∃ c, 2 * |t - c * μ| ≤ |μ|` for `μ ≠ 0`.
* `Int.eq_mul_iff_dvd_of_abs_sub_mul_lt` : `t = c * μ ↔ μ ∣ t` when `|t - c * μ| < |μ|`.
* `Int.eq_mul_iff_dvd_of_two_mul_abs_sub_mul_le` : `t = c * μ ↔ μ ∣ t` when
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

/-- If `t` lies strictly within `|μ|` of `c * μ`, then `t = c * μ` if and only if `μ ∣ t`. -/
theorem eq_mul_iff_dvd_of_abs_sub_mul_lt {t c μ : ℤ} (h : |t - c * μ| < |μ|) :
    t = c * μ ↔ μ ∣ t := by
  refine ⟨fun ht ↦ ⟨c, by rw [ht, mul_comm]⟩, fun ⟨k, hk⟩ ↦ sub_eq_zero.mp ?_⟩
  refine eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨k - c, ?_⟩
    (by simpa only [abs_eq_natAbs, Int.ofNat_lt] using h)
  rw [hk, Int.mul_sub, mul_comm μ c]

/-- For a nearest multiple `c * μ` with `2 * |t - c * μ| ≤ |μ|`, `t = c * μ` if and only if
`μ ∣ t`. -/
theorem eq_mul_iff_dvd_of_two_mul_abs_sub_mul_le {t c μ : ℤ} (h : 2 * |t - c * μ| ≤ |μ|) :
    t = c * μ ↔ μ ∣ t := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp only [mul_zero, sub_zero, abs_zero] at h
    have ht : t = 0 := abs_eq_zero.mp (by have := abs_nonneg t; omega)
    simp [ht]
  · exact eq_mul_iff_dvd_of_abs_sub_mul_lt
      (by have := abs_nonneg (t - c * μ); have := abs_pos.mpr hμ; omega)

end Int
