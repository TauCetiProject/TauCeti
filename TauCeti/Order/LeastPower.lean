/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Bounds.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Least powers above a threshold and dyadic-triadic rank selection

For `1 < q` and `1 < z`, the least power of `q` that is at least `z` has the form `q ^ (e + 1)`
with `q ^ e < z`, so it lies in `[z, q * z]`. Applying this to `q = 2` at `exp (y / 2)` and
`q = 3` at `exp (5 * y)` for `y ≥ 2` yields the dyadic rank `m`, the triadic rank `r`, and the
tower exponent `s = 22 * (e + 1) ≤ 32 * y` used in admissible data.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026
Anthropic, PBC), commit `72fead102f663d5c7a407964a13dc0cf9d977207`, specifically
`New.exists_isLeast_pow` and `New.exists_isLeast_two_pow_three_pow` in
`grh/src/New/Reduction/Data/Existence.lean`.
-/

public section

open Real Set

namespace TauCeti

/-- For `1 < q` and `1 < z`, the least power of `q` that is at least `z` is `q ^ (e + 1)` for
some `e : ℕ` with `q ^ e < z`. -/
theorem exists_isLeast_pow {q : ℕ} {z : ℝ} (hq : 1 < q) (hz : 1 < z) :
    ∃ e : ℕ, IsLeast {n : ℕ | (∃ j : ℕ, n = q ^ j) ∧ z ≤ n} (q ^ (e + 1)) ∧
      (q : ℝ) ^ e < z := by
  classical
  have hex : ∃ j : ℕ, z ≤ (q : ℝ) ^ j :=
    (pow_unbounded_of_one_lt z (by exact_mod_cast hq)).imp fun _ ↦ le_of_lt
  obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero (n := Nat.find hex) (by
    intro h0
    have hspec : z ≤ (q : ℝ) ^ 0 := by simpa [h0] using Nat.find_spec hex
    linarith [pow_zero (q : ℝ)])
  have hle : z ≤ (q : ℝ) ^ (e + 1) := by simpa [he] using Nat.find_spec hex
  refine ⟨e, ⟨⟨⟨e + 1, rfl⟩, by exact_mod_cast hle⟩, ?_⟩,
    not_le.mp (Nat.find_min hex (by omega))⟩
  rintro _ ⟨⟨j, rfl⟩, hj⟩
  exact Nat.pow_le_pow_right hq.le
    (he.ge.trans (Nat.find_min' hex (by exact_mod_cast hj)))

/-- For `1 < q` and `1 < z`, the least power of `q` that is at least `z` has positive exponent
and lies in `[z, q * z]`. -/
theorem exists_isLeast_pow_mem_Icc {q : ℕ} {z : ℝ} (hq : 1 < q) (hz : 1 < z) :
    ∃ e : ℕ, IsLeast {n : ℕ | (∃ j : ℕ, n = q ^ j) ∧ z ≤ n} (q ^ (e + 1)) ∧
      ((q ^ (e + 1) : ℕ) : ℝ) ∈ Icc z (q * z) := by
  obtain ⟨e, hleast, hlt⟩ := exists_isLeast_pow hq hz
  refine ⟨e, hleast, hleast.left.right, ?_⟩
  rw [Nat.cast_pow, pow_succ']
  exact mul_le_mul_of_nonneg_left hlt.le (Nat.cast_nonneg q)

/-- For `y ≥ 2`, the least power `m` of `2` with `exp (y / 2) ≤ m` and the least power `r` of
`3` with `exp (5 * y) ≤ r` satisfy `m ≤ 2 * exp (y / 2)`, `r ≤ 3 * exp (5 * y)`, have positive
exponents, and `s = 22 * (e + 1)` satisfies `s ≤ 32 * y`. -/
theorem exists_isLeast_two_pow_three_pow {y : ℝ} (hy : 2 ≤ y) :
    ∃ m r s : ℕ,
      IsLeast {n : ℕ | (∃ j : ℕ, n = 2 ^ j) ∧ exp (y / 2) ≤ n} m ∧
      IsLeast {n : ℕ | (∃ j : ℕ, n = 3 ^ j) ∧ exp (5 * y) ≤ n} r ∧
      (m : ℝ) ≤ 2 * exp (y / 2) ∧
      (r : ℝ) ≤ 3 * exp (5 * y) ∧
      (∃ e : ℕ, m = 2 ^ (e + 1) ∧ s = (e + 1) * 22) ∧
      (∃ e : ℕ, r = 3 ^ (e + 1)) ∧
      (s : ℝ) ≤ 32 * y := by
  obtain ⟨a, hm, hma⟩ :=
    exists_isLeast_pow (q := 2) (z := exp (y / 2)) one_lt_two
      (Real.one_lt_exp_iff.mpr (by linarith))
  obtain ⟨c, hr, hrc⟩ :=
    exists_isLeast_pow (q := 3) (z := exp (5 * y)) (by norm_num)
      (Real.one_lt_exp_iff.mpr (by linarith))
  refine ⟨2 ^ (a + 1), 3 ^ (c + 1), (a + 1) * 22, hm, hr,
    by simpa [pow_succ'] using mul_le_mul_of_nonneg_left hma.le zero_le_two,
    by simpa [pow_succ'] using mul_le_mul_of_nonneg_left hrc.le (by norm_num : (0 : ℝ) ≤ 3),
    ⟨a, rfl, rfl⟩, ⟨c, rfl⟩, ?_⟩
  have hlog : (a : ℝ) * log 2 < y / 2 := by
    simpa [Real.log_pow] using (Real.log_lt_iff_lt_exp (by positivity)).mpr hma
  push_cast
  nlinarith [Real.log_two_gt_d9]

end TauCeti
