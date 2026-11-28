/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Explicit size bounds for one-sided prime-sum parameters

Elementary size inequalities derived from the tower exponent `s`, the odd prime-power bound
`l₀ s`, the auxiliary modulus `q₂ s = (q₀ * d) ^ (s + 6)`, and the level scales `b`, `M`,
and `Ω`:
* `m ^ 594 ≤ 2 ^ l₀ s` whenever `m ^ 22 = 2 ^ s`;
* `q₂ s ≤ exp logX ^ (33 * (q₀ * d))` whenever `s + 6 ≤ 33 * logX`;
* `log (M / Ω) ∈ [20 * log b, 23 * log b]` when `b ^ 20 ≤ M`, `0 < Ω ≤ 1`, and
  `M / Ω ≤ b ^ 23`;
* `|log x| ≤ 23 * log b` whenever `1 ≤ x ≤ b ^ 23`.

## Provenance

Adapted from `grh-lean` (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026
Anthropic, PBC), commit `72fead102f663d5c7a407964a13dc0cf9d977207`, specifically
`New.Data.m_pow_le_two_pow_l₀`, `New.Data.q₂_le`, `New.Data.log_M_div_bigOmega_mem_Icc`, and
`New.Data.abs_log_M_mul_rootDisc_le` in `grh/src/New/Reduction/Data/Sizes.lean`.
-/

public section

open Real Set

namespace TauCeti.OneSidedBound

/-- If `m ^ 22 = 2 ^ s`, then `m ^ 594 ≤ 2 ^ l₀ s`, since `594 = 22 * 27` and `27 * s < l₀ s`. -/
theorem pow_594_le_two_pow_l₀ {m s : ℕ} (hm : m ^ 22 = 2 ^ s) :
    m ^ 594 ≤ 2 ^ l₀ s := by
  calc m ^ 594 = (m ^ 22) ^ 27 := by rw [← pow_mul]
    _ = 2 ^ (27 * s) := by rw [hm, ← pow_mul, mul_comm]
    _ ≤ 2 ^ l₀ s := Nat.pow_le_pow_right two_pos (lt_l₀ s).le

/-- If `s + 6 ≤ 33 * logX`, then the auxiliary modulus `q₂ s = (q₀ * d) ^ (s + 6)` is at most
`exp logX ^ (33 * (q₀ * d))`. -/
theorem Parameters.q₂_le_exp_mul (P : Parameters) {s : ℕ} {logX : ℝ}
    (hs : (s + 6 : ℝ) ≤ 33 * logX) :
    (P.q₂ s : ℝ) ≤ exp logX ^ (33 * (P.q₀ * P.d)) := by
  calc (P.q₂ s : ℝ) = ((P.q₀ * P.d : ℕ) : ℝ) ^ (s + 6) := by rw [Parameters.q₂_def, Nat.cast_pow]
    _ ≤ exp ((P.q₀ * P.d : ℕ) : ℝ) ^ (s + 6) := by
        gcongr
        linarith only [add_one_le_exp ((P.q₀ * P.d : ℕ) : ℝ)]
    _ = exp ((s + 6 : ℝ) * (P.q₀ * P.d : ℕ)) := by
        rw [← exp_natCast_mul, Nat.cast_add, Nat.cast_ofNat]
    _ ≤ exp (33 * logX * (P.q₀ * P.d : ℕ)) := by gcongr
    _ = exp logX ^ (33 * (P.q₀ * P.d)) := by
        rw [← exp_natCast_mul]
        push_cast
        ring_nf

/-- If `b > 0`, `0 < Ω ≤ 1`, `b ^ 20 ≤ M`, and `M / Ω ≤ b ^ 23`, then
`log (M / Ω) ∈ [20 * log b, 23 * log b]`. -/
theorem log_div_mem_Icc_of_le_one {b M Ω : ℝ} (hb : 0 < b) (hΩ_pos : 0 < Ω) (hΩ_le : Ω ≤ 1)
    (hM_lo : b ^ 20 ≤ M) (hM_hi : M / Ω ≤ b ^ 23) :
    log (M / Ω) ∈ Icc (20 * log b) (23 * log b) := by
  have hlo : b ^ 20 ≤ M / Ω :=
    hM_lo.trans (le_div_self ((pow_nonneg hb.le 20).trans hM_lo) hΩ_pos hΩ_le)
  constructor
  · simpa [log_pow] using log_le_log (by positivity) hlo
  · simpa [log_pow] using log_le_log (lt_of_lt_of_le (by positivity) hlo) hM_hi

/-- If `1 ≤ x ≤ b ^ 23`, then `|log x| ≤ 23 * log b`. -/
theorem abs_log_le_mul_log_of_mem_Icc {b x : ℝ} (hlo : 1 ≤ x) (hhi : x ≤ b ^ 23) :
    |log x| ≤ 23 * log b := by
  rw [abs_of_nonneg (log_nonneg hlo)]
  simpa [log_pow] using log_le_log (one_pos.trans_le hlo) hhi

end TauCeti.OneSidedBound
