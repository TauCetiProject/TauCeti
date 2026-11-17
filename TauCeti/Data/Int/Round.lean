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

For natural numbers `n` and `m ≠ 0`, both the nearest-multiple index `i` and the distance `j`
can be chosen in `ℕ`, giving `2 * j ≤ m` and `(n : ℤ) = (i : ℤ) * m ± j`.

## Main results

* `Int.exists_two_mul_abs_sub_mul_le` : `∃ c, 2 * |t - c * μ| ≤ |μ|` for `μ ≠ 0`.
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
