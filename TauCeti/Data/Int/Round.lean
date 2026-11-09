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

## Main results

* `Int.exists_two_mul_abs_sub_mul_le` : `∃ c, 2 * |t - c * μ| ≤ |μ|` for `μ ≠ 0`.
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
