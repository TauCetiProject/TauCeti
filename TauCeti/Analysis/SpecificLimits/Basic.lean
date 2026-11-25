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
sequences under eventual multiplicative step growth, and with the comparison of two geometric
sequences of different ratios.

## Main results

* `TauCeti.tendsto_atTop_of_eventually_geom_le`: if `1 < c`, `c * v m ≤ v (m + 1)` eventually,
  and `0 < v m` frequently, then `v n → +∞`.
* `TauCeti.eventually_div_pow_le_div_pow`: for `0 < d < r`, the geometric sequence `M / r ^ k`
  is eventually at most `δ / d ^ (k + 1)`, for every `δ > 0`.
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

end TauCeti
