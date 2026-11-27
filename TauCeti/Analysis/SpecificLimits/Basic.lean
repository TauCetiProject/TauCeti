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
* `TauCeti.tendsto_add_div_succ`: `(n + a) / (n + 1) → 1`.
* `TauCeti.tendsto_inv_succ_smul_const`: `(n + 1)⁻¹ • c → 0`.
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

/-- For any shift `a`, `((n : 𝕜) + a) / ((n + 1 : ℕ) : 𝕜)` converges to `1`. -/
theorem tendsto_add_div_succ {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜]
    [ContinuousSMul ℚ≥0 𝕜] [IsTopologicalSemiring 𝕜] [ContinuousInv₀ 𝕜] (a : 𝕜) :
    Tendsto (fun n : ℕ ↦ ((n : 𝕜) + a) / ((n + 1 : ℕ) : 𝕜)) atTop (nhds 1) := by
  simpa [add_comm, Nat.cast_add, Nat.cast_one] using
    tendsto_add_mul_div_add_mul_atTop_nhds a 1 1 (one_ne_zero : (1 : 𝕜) ≠ 0)

/-- `((n + 1 : ℕ) : 𝕜)⁻¹ • c → 0` for any constant `c : E`. -/
theorem tendsto_inv_succ_smul_const {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] {E : Type*} [Zero E] [SMulWithZero 𝕜 E]
    [TopologicalSpace E] [ContinuousSMul 𝕜 E] (c : E) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : 𝕜)⁻¹ • c) atTop (nhds 0) := by
  simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := 𝕜)).smul_const c

end TauCeti
