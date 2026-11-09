/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.GCongr

/-!
# Choosing step counts in Archimedean ordered semifields

This file chooses a positive number of steps `n` with `L * n⁻¹ < c`, which splits a segment into `n`
steps of length `n⁻¹` with an error of at most `c`.

It also chooses the length of a finite geometric sequence of exponents. Given a ratio `r > 1`
and a target `s < r`, it finds a number `M ≥ 1` of steps such that the starting value
`s / r ^ M` lies below any prescribed `p > 0` while every term `s / r ^ M * r ^ k` with `k < M`
stays below `1`. Moser's iteration uses it to pick the exponents `p₀ χ^k` along which a reverse
Hölder inequality is iterated.

## Main results

* `TauCeti.exists_pos_nat_mul_inv_lt`: for `0 < c` there is `n > 0` with `L * n⁻¹ < c`.
* `TauCeti.exists_div_pow_lt_and_forall_mul_pow_lt_one`: for `1 < r`, `s < r` and `0 < p`
  there is `M > 0` with `s / r ^ M < p` and `s / r ^ M * r ^ k < 1` for all `k < M`.
* `TauCeti.exists_nat_ge_and_div_le`: for `0 < δ` and `n₀ : ℕ` there are `n ≥ n₀` and `N > 0`
  with `1 / (N + 1) ≤ δ` and `2 * n / N ≤ δ`.
-/

public section

namespace TauCeti

variable {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]

/-- For `r > 1`, `s < r` and `p > 0` there is a number `M ≥ 1` of steps such that the
starting value `s / r ^ M` is below `p`, and the terms `s / r ^ M * r ^ k` of the geometric
sequence for the steps `k < M` stay below `1`. -/
theorem exists_div_pow_lt_and_forall_mul_pow_lt_one [ExistsAddOfLE K] {r s p : K} (hr : 1 < r)
    (hsr : s < r) (hp : 0 < p) :
    ∃ M : ℕ, 0 < M ∧ s / r ^ M < p ∧ ∀ k < M, s / r ^ M * r ^ k < 1 := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (s / p) hr
  refine ⟨m + 1, m.succ_pos, ?_, fun k hk => ?_⟩
  · rw [div_lt_iff₀ (by positivity), ← div_lt_iff₀' hp]
    exact hm.trans_le (pow_le_pow_right₀ hr.le m.le_succ)
  · rw [div_mul_eq_mul_div, div_lt_one (by positivity)]
    calc s * r ^ k < r * r ^ k := by gcongr
      _ = r ^ (k + 1) := (pow_succ' r k).symm
      _ ≤ r ^ (m + 1) := pow_le_pow_right₀ hr.le hk

/-- For any `L` and `c > 0` there is a positive integer `n` with `L * n⁻¹ < c`. -/
theorem exists_pos_nat_mul_inv_lt (L : K) {c : K} (hc : 0 < c) :
    ∃ n : ℕ, 0 < n ∧ L * (n : K)⁻¹ < c := by
  obtain ⟨m, hm⟩ := exists_nat_gt (L / c)
  refine ⟨m + 1, m.succ_pos, ?_⟩
  rw [← div_eq_mul_inv, div_lt_iff₀ (by positivity), ← div_lt_iff₀' hc]
  exact hm.trans (by simp)

/-- For `δ > 0` and any `n₀`, there are a positive `n ≥ n₀` and a positive `N` so large that both
`1 / (N + 1)` and `2 * n / N` are at most `δ`. -/
theorem exists_nat_ge_and_div_le {δ : K} (hδ : 0 < δ) (n₀ : ℕ) :
    ∃ n N : ℕ, 0 < n ∧ n₀ ≤ n ∧ 0 < N ∧ 1 / ((N : K) + 1) ≤ δ ∧ 2 * (n : K) / N ≤ δ := by
  obtain ⟨N, hNpos, h2⟩ := exists_pos_nat_mul_inv_lt (2 * ((n₀ + 1 : ℕ) : K)) hδ
  rw [← div_eq_mul_inv] at h2
  refine ⟨n₀ + 1, N, n₀.succ_pos, n₀.le_succ, hNpos, ?_, h2.le⟩
  calc 1 / ((N : K) + 1) ≤ 1 / N :=
        one_div_le_one_div_of_le (Nat.cast_pos.2 hNpos) (le_add_of_nonneg_right zero_le_one)
    _ ≤ 2 * ((n₀ + 1 : ℕ) : K) / N := by gcongr; norm_cast; omega
    _ ≤ δ := h2.le

end TauCeti
