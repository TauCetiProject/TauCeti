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
vanishes if and only if `μ` divides `t`. Moreover, `t` lies strictly closer than `|μ| / 2` to
some multiple of `μ` if and only if `μ ∣ 2 t` implies `μ ∣ t`, isolating the midpoint case of
odd multiples of `μ / 2` for even `μ`.

For natural numbers `n` and `m ≠ 0`, both the nearest-multiple index `i` and the distance `j`
can be chosen in `ℕ`, giving `2 * j ≤ m` and `(n : ℤ) = (i : ℤ) * m ± j`.

## Main results

* `Int.exists_two_mul_abs_sub_mul_le` : `∃ c, 2 * |t - c * μ| ≤ |μ|` for `μ ≠ 0`.
* `Int.abs_sub_mul_eq_zero_iff_dvd_of_lt` : `|t - c * μ| = 0 ↔ μ ∣ t` when `|t - c * μ| < |μ|`.
* `Int.abs_sub_mul_eq_zero_iff_dvd_of_two_mul_le` : `|t - c * μ| = 0 ↔ μ ∣ t` when
  `2 * |t - c * μ| ≤ |μ|`.
* `Int.exists_two_mul_abs_sub_mul_lt_iff` : for `μ ≠ 0`,
  `(∃ c, 2 * |t - c * μ| < |μ|) ↔ (μ ∣ 2 * t → μ ∣ t)`.
* `Nat.exists_two_mul_le_and_natCast_eq_mul_add_or_mul_sub` : `∃ i j : ℕ, 2 * j ≤ m` with
  `(n : ℤ) = (i : ℤ) * m + j ∨ (n : ℤ) = (i : ℤ) * m - j` for `m ≠ 0`.
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
    have hzero := (abs_sub_mul_eq_zero_iff_dvd_of_lt hlt).mpr h₂
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

namespace Nat

/-- Every natural number `n` lies within `m / 2` of a natural multiple `i * m` of a nonzero
natural number `m`, with signed decomposition `(n : ℤ) = (i : ℤ) * m ± j` and `2 * j ≤ m`. -/
theorem exists_two_mul_le_and_natCast_eq_mul_add_or_mul_sub (n : ℕ) {m : ℕ} (hm : m ≠ 0) :
    ∃ i j : ℕ, 2 * j ≤ m ∧
      ((n : ℤ) = (i : ℤ) * m + j ∨ (n : ℤ) = (i : ℤ) * m - j) := by
  have hmod : n % m < m := Nat.mod_lt n (Nat.pos_of_ne_zero hm)
  have hdiv : ((n / m : ℕ) : ℤ) * m + (n % m : ℕ) = n := by
    rw [← Nat.cast_mul, ← Nat.cast_add, Nat.div_add_mod']
  by_cases h : 2 * (n % m) ≤ m
  · exact ⟨n / m, n % m, h, .inl hdiv.symm⟩
  · refine ⟨n / m + 1, m - n % m, by omega, .inr ?_⟩
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, Nat.cast_sub hmod.le]
    omega

end Nat
