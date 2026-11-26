/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Choosing multiples and step counts in Archimedean ordered structures

This file chooses a positive number of steps `n` with `L * n⁻¹ < c`, which splits a segment into `n`
steps of length `n⁻¹` with an error of at most `c`.

It also chooses the length of a finite geometric sequence of exponents. Given a ratio `r > 1`
and a target `s < r`, it finds a number `M ≥ 1` of steps such that the starting value
`s / r ^ M` lies below any prescribed `p > 0` while every term `s / r ^ M * r ^ k` with `k < M`
stays below `1`. Moser's iteration uses it to pick the exponents `p₀ χ^k` along which a reverse
Hölder inequality is iterated.

Finally, it chooses a dyadic scale `2ᵏ` comparable to a given length: for `ρ, n > 0` there is
an integer `k` with `4 · 2ᵏ n ≤ ρ < 8 · 2ᵏ n`. Covering arguments with dyadic cubes use it to fit
a cube of side `2ᵏ` and diameter `2ᵏ √d` into a ball of radius `ρ`, with `n = √d`.

In an Archimedean linearly ordered commutative ring, a quotient `a / b` is determined by how the
integer multiples of `a` and `b` compare, which identifies two quotients from such comparisons
without dividing.

Beyond ordered semifields, in an Archimedean linearly ordered additive group the integer
multiples `k • ℓ` of a nonzero element `ℓ` are unbounded above, whatever the sign of `ℓ`. For maps
of the strip `ℝ × Y` commuting with the translation by a period `ℓ`, it gives a multiple of the
period exceeding any prescribed distance. This shows that such maps are onto along horizontal
lines, and that the inverse of a positive twist lift twists negatively.

## Main results

* `TauCeti.exists_pos_nat_mul_inv_lt`: for `0 < c` there is `n > 0` with `L * n⁻¹ < c`.
* `TauCeti.exists_div_pow_lt_and_forall_mul_pow_lt_one`: for `1 < r`, `s < r` and `0 < p`
  there is `M > 0` with `s / r ^ M < p` and `s / r ^ M * r ^ k < 1` for all `k < M`.
* `TauCeti.exists_nat_ge_and_div_le`: for `0 < δ` and `n₀ : ℕ` there are `n ≥ n₀` and `N > 0`
  with `1 / (N + 1) ≤ δ` and `2 * n / N ≤ δ`.
* `TauCeti.exists_four_mul_two_zpow_mul_le_and_lt`: for `ρ, n > 0` there is `k : ℤ` with
  `4 · 2ᵏ n ≤ ρ < 8 · 2ᵏ n`.
* `TauCeti.mul_eq_mul_of_forall_intCast_mul_le_iff`: if `p * a ≤ q * b ↔ p * c ≤ q * d` for all
  integers `p` and `q`, then `c * b = d * a`.
* `TauCeti.exists_lt_zsmul`: in an Archimedean linearly ordered additive group, the integer
  multiples of a nonzero element are unbounded above.
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

/-- In an Archimedean linearly ordered commutative ring, if the integer multiples of `a` and `b`
compare like those of `c` and `d`, then `a / b = c / d`, written without division:
`c * b = d * a`. -/
theorem mul_eq_mul_of_forall_intCast_mul_le_iff {L : Type*} [CommRing L] [LinearOrder L]
    [IsStrictOrderedRing L] [Archimedean L] {a b c d : L}
    (h : ∀ p q : ℤ, p * a ≤ q * b ↔ p * c ≤ q * d) : c * b = d * a := by
  -- Comparing with `p = 0` shows that `b` and `d` have the same sign.
  have h₀ : ∀ q : ℤ, 0 ≤ q * b ↔ 0 ≤ q * d := fun q ↦ by
    simpa only [Int.cast_zero, zero_mul] using h 0 q
  wlog hb : 0 < b generalizing b d
  · rcases (not_lt.1 hb).lt_or_eq with hb | rfl
    · have := this (b := -b) (d := -d) (fun p q ↦ by simpa using h p (-q))
        (fun q ↦ by simpa using h₀ (-q)) (neg_pos.2 hb)
      linarith
    · have h₁ := h₀ 1
      have h₂ := h₀ (-1)
      simp only [Int.cast_one, Int.cast_neg, one_mul, neg_one_mul, mul_zero,
        le_refl, true_iff, neg_nonneg] at h₁ h₂
      rw [le_antisymm h₂ h₁, zero_mul, mul_zero]
  have hd : 0 < d := by
    have h₂ := h₀ (-1)
    simp only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_nonneg] at h₂
    exact lt_of_not_ge fun hd ↦ hb.not_ge (h₂.2 hd)
  -- If `a / b` and `c / d` differed, some integer quotient `q / p` would separate them.
  have key : ∀ {a b c d : L}, 0 < b → 0 < d → (∀ p q : ℤ, p * a ≤ q * b ↔ p * c ≤ q * d) →
      ¬ c * b < d * a := by
    intro a b c d hb hd h hlt
    have hbd : 0 < b * d := mul_pos hb hd
    obtain ⟨n, hn⟩ := exists_lt_nsmul (sub_pos.2 hlt) (b * d)
    obtain ⟨k, hk₁, hk₂⟩ := (existsUnique_zsmul_near_of_pos hbd (n * c * b)).exists
    rw [nsmul_eq_mul] at hn
    rw [zsmul_eq_mul] at hk₁ hk₂
    have hq₁ : ((k + 1 : ℤ) : L) * b * d < (n : ℤ) * a * d := by push_cast at hk₂ ⊢; nlinarith
    have hq₂ : (n : ℤ) * c * b < ((k + 1 : ℤ) : L) * d * b := by push_cast at hk₂ ⊢; nlinarith
    have h₁ : ((k + 1 : ℤ) : L) * b < (n : ℤ) * a := lt_of_mul_lt_mul_right hq₁ hd.le
    have h₂ : ((n : ℤ) : L) * c < ((k + 1 : ℤ) : L) * d := lt_of_mul_lt_mul_right hq₂ hb.le
    exact h₁.not_ge ((h n (k + 1)).2 h₂.le)
  rcases lt_trichotomy (c * b) (d * a) with hlt | heq | hgt
  · exact (key hb hd h hlt).elim
  · exact heq
  · exact (key hd hb (fun p q ↦ (h p q).symm) (by linarith)).elim

/-- In an Archimedean linearly ordered additive group, some integer multiple of a nonzero element
`ℓ` exceeds any given `r`, whatever the sign of `ℓ`. -/
theorem exists_lt_zsmul {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
    [Archimedean M] {ℓ : M} (hℓ : ℓ ≠ 0) (r : M) : ∃ k : ℤ, r < k • ℓ := by
  rcases hℓ.lt_or_gt with h | h
  · obtain ⟨n, hn⟩ := exists_lt_nsmul (neg_pos.2 h) r
    exact ⟨-n, by rwa [neg_zsmul, natCast_zsmul, ← neg_nsmul]⟩
  · obtain ⟨n, hn⟩ := exists_lt_nsmul h r
    exact ⟨n, by rwa [natCast_zsmul]⟩

end TauCeti
