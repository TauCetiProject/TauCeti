/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Choosing step counts in Archimedean ordered semifields

This file chooses a positive number of steps `n` with `L * n⁻¹ < c`, which splits a segment into `n`
steps of length `n⁻¹` with an error of at most `c`.

It also chooses the length of a finite geometric sequence of exponents. Given a ratio `r > 1`
and a target `s < r`, it finds a number `M ≥ 1` of steps such that the starting value
`s / r ^ M` lies below any prescribed `p > 0` while every term `s / r ^ M * r ^ k` with `k < M`
stays below `1`. Moser's iteration uses it to pick the exponents `p₀ χ^k` along which a reverse
Hölder inequality is iterated. It also records that an additive endomorphism of `ℝ` preserving
positivity is linear.

Finally, it chooses a dyadic scale `2ᵏ` comparable to a given length: for `ρ, n > 0` there is
an integer `k` with `4 · 2ᵏ n ≤ ρ < 8 · 2ᵏ n`. Covering arguments with dyadic cubes use it to fit
a cube of side `2ᵏ` and diameter `2ᵏ √d` into a ball of radius `ρ`, with `n = √d`.

## Main results

* `TauCeti.exists_pos_nat_mul_inv_lt`: for `0 < c` there is `n > 0` with `L * n⁻¹ < c`.
* `TauCeti.exists_div_pow_lt_and_forall_mul_pow_lt_one`: for `1 < r`, `s < r` and `0 < p`
  there is `M > 0` with `s / r ^ M < p` and `s / r ^ M * r ^ k < 1` for all `k < M`.
* `TauCeti.exists_nat_ge_and_div_le`: for `0 < δ` and `n₀ : ℕ` there are `n ≥ n₀` and `N > 0`
  with `1 / (N + 1) ≤ δ` and `2 * n / N ≤ δ`.
* `AddMonoidHom.real_eq_mul_one`: an additive map `ℝ →+ ℝ` sending positive reals to positive
  reals is linear (`f r = r * f 1`).
* `TauCeti.exists_four_mul_two_zpow_mul_le_and_lt`: for `ρ, n > 0` there is `k : ℤ` with
  `4 · 2ᵏ n ≤ ρ < 8 · 2ᵏ n`.
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

section Field

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L] [Archimedean L]

/-- A dyadic scale `2ᵏ` with `4 · 2ᵏ n ≤ ρ < 8 · 2ᵏ n`, for `ρ, n > 0`. -/
theorem exists_four_mul_two_zpow_mul_le_and_lt {ρ n : L} (hρ : 0 < ρ) (hn : 0 < n) :
    ∃ k : ℤ, 4 * 2 ^ k * n ≤ ρ ∧ ρ / 4 < 2 * 2 ^ k * n := by
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow (x := ρ / (4 * n)) (by positivity) one_lt_two
  rw [le_div_iff₀ (by positivity)] at hk1
  rw [div_lt_iff₀ (by positivity), zpow_add_one₀ two_ne_zero] at hk2
  exact ⟨k, by linarith, by linarith⟩

end Field

end TauCeti

/-- An additive map `ℝ →+ ℝ` sending positive reals to positive reals is linear. -/
theorem AddMonoidHom.real_eq_mul_one (f : ℝ →+ ℝ) (hf : ∀ r : ℝ, 0 < r → 0 < f r)
    (r : ℝ) : f r = r * f 1 := by
  have hmono : StrictMono f := fun a b hab ↦
    sub_pos.mp (by rw [← map_sub]; exact hf _ (sub_pos.mpr hab))
  have hrat (q : ℚ) : f q = (q : ℝ) * f 1 := by
    have hq' : (q.den : ℝ) * (q : ℝ) = (q.num : ℝ) := by
      rw [mul_comm]; exact_mod_cast Rat.mul_den_eq_num q
    have hq : (q.den : ℕ) • (q : ℝ) = (q.num : ℤ) • (1 : ℝ) := by
      rw [nsmul_eq_mul, zsmul_eq_mul, mul_one]; exact hq'
    have hden : (q.den : ℝ) * f q = q.num * f 1 := by
      have h := congrArg f hq
      rwa [map_nsmul, map_zsmul, nsmul_eq_mul, zsmul_eq_mul] at h
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr q.den_nz)
    calc (q.den : ℝ) * f q = (q.num : ℝ) * f 1 := hden
      _ = ((q.den : ℝ) * (q : ℝ)) * f 1 := by rw [hq']
      _ = (q.den : ℝ) * ((q : ℝ) * f 1) := mul_assoc _ _ _
  have hf1 : 0 < f 1 := hf 1 one_pos
  refine le_antisymm (le_of_not_gt fun hlt ↦ ?_) (le_of_not_gt fun hlt ↦ ?_)
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ((lt_div_iff₀ hf1).mpr hlt)
    linarith [hmono hq1, (lt_div_iff₀ hf1).mp hq2, hrat q]
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ((div_lt_iff₀ hf1).mpr hlt)
    linarith [hmono hq2, (div_lt_iff₀ hf1).mp hq1, hrat q]
