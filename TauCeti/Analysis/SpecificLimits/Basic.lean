/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Specific limits for real sequences

This module extends `Mathlib.Analysis.SpecificLimits.Basic` with asymptotic divergence for real
sequences under eventual multiplicative step growth, with the comparison of two geometric
sequences of different ratios, and with the summability over `ℤ` of a geometric sequence cut off
below.

## Main results

* `TauCeti.tendsto_atTop_of_eventually_geom_le`: if `1 < c`, `c * v m ≤ v (m + 1)` eventually,
  and `0 < v m` frequently, then `v n → +∞`.
* `TauCeti.eventually_div_pow_le_div_pow`: for `0 < d < r`, the geometric sequence `M / r ^ k`
  is eventually at most `δ / d ^ (k + 1)`, for every `δ > 0`.
* `TauCeti.zpow_le_add_zpow_of_le_of_le`: for `0 < x ≤ y ≤ z` and `n ∈ ℤ`,
  `y ^ n ≤ x ^ n + z ^ n`.
* `TauCeti.summable_ite_le_zpow`: for `0 < ρ < 1`, `n ↦ ρ ^ n` on `n ≥ N` (and `0` below) is
  summable over `ℤ`.
-/

public section

open Filter

namespace TauCeti

/-- If `1 < c`, `c * v m ≤ v (m + 1)` eventually, and `0 < v m` frequently, then `v n → +∞` as
`n → ∞`. -/
theorem tendsto_atTop_of_eventually_geom_le {v : ℕ → ℝ} {c : ℝ} (hc : 1 < c)
    (hstep : ∀ᶠ m in atTop, c * v m ≤ v (m + 1)) (hne : ∃ᶠ m in atTop, 0 < v m) :
    Tendsto v atTop atTop := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hstep
  obtain ⟨M, hpos, _⟩ := (hne.and_eventually (eventually_ge_atTop M₀)).exists
  exact (tendsto_add_atTop_iff_nat M).1 <|
    tendsto_atTop_of_geom_le (v := fun n ↦ v (n + M)) (by simpa using hpos) hc
      fun n ↦ by simpa only [Nat.add_right_comm] using hM₀ (n + M) (by omega)

/-- A geometric sequence is eventually dominated by any positive multiple of a geometric sequence
of larger ratio: for `0 < d < r` and `0 < δ`, eventually `M / r ^ k ≤ δ / d ^ (k + 1)`. -/
theorem eventually_div_pow_le_div_pow (M : ℝ) {δ d r : ℝ} (hδ : 0 < δ) (hd : 0 < d)
    (hdr : d < r) : ∀ᶠ k : ℕ in atTop, M / r ^ k ≤ δ / d ^ (k + 1) := by
  have hr : 0 < r := hd.trans hdr
  have hlim : Tendsto (fun k : ℕ ↦ M * d * (d / r) ^ k) atTop (nhds (M * d * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hd.le hr.le)
      ((div_lt_one hr).2 hdr)).const_mul _
  rw [mul_zero] at hlim
  filter_upwards [hlim.eventually_le_const hδ] with k hk
  have hrk : 0 < r ^ k := pow_pos hr k
  rw [div_le_div_iff₀ hrk (pow_pos hd _)]
  calc M * d ^ (k + 1) = M * d * (d / r) ^ k * r ^ k := by
        rw [div_pow, pow_succ]
        field_simp
    _ ≤ δ * r ^ k := mul_le_mul_of_nonneg_right hk hrk.le

/-- For `0 < x ≤ y ≤ z`, every integer power of `y` is at most `x ^ n + z ^ n`: the second term
dominates for `n ≥ 0` and the first for `n < 0`. -/
theorem zpow_le_add_zpow_of_le_of_le {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] {x y z : α} (hx : 0 < x) (hxy : x ≤ y) (hyz : y ≤ z) (n : ℤ) :
    y ^ n ≤ x ^ n + z ^ n := by
  rcases le_or_gt 0 n with hn | hn
  · exact le_add_of_nonneg_of_le (zpow_nonneg hx.le n)
      (zpow_le_zpow_left₀ hn (hx.trans_le hxy).le hyz)
  · have h := inv_anti₀ (zpow_pos hx (-n)) (zpow_le_zpow_left₀ (neg_nonneg.2 hn.le) hx.le hxy)
    rw [zpow_neg, zpow_neg, inv_inv, inv_inv] at h
    exact le_add_of_le_of_nonneg h (zpow_nonneg (hx.le.trans (hxy.trans hyz)) n)

/-- The two-sided geometric sequence `n ↦ ρ ^ n` on `ℤ`, cut off below `N`, is summable for
`0 < ρ < 1`. -/
theorem summable_ite_le_zpow (N : ℤ) {ρ : ℝ} (hρ₀ : 0 < ρ) (hρ : ρ < 1) :
    Summable fun n : ℤ ↦ if N ≤ n then ρ ^ n else 0 := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine (summable_geometric_of_lt_one hρ₀.le hρ).of_nonneg_of_le
      (fun k ↦ by split_ifs; exacts [zpow_nonneg hρ₀.le _, le_rfl]) fun k ↦ ?_
    split_ifs
    · rw [zpow_natCast]
    · exact pow_nonneg hρ₀.le k
  · refine summable_of_ne_finset_zero (s := Finset.range (-N).toNat) fun k hk ↦ ?_
    rw [Finset.mem_range, not_lt] at hk
    exact ite_eq_right_iff.2 fun h ↦ absurd h (by omega)

end TauCeti
