/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-!
# Geometric exponent sequences in Archimedean ordered fields

This file chooses the length of a finite geometric sequence of exponents. Given a ratio `r > 1`
and a target `0 < s < r`, it finds a number `M ≥ 1` of steps such that the starting value
`s / r ^ M` lies below any prescribed `p > 0` while every term `s / r ^ M * r ^ k` with `k < M`
stays below `1`. Moser's iteration uses it to pick the exponents `p₀ χ^k` along which a reverse
Hölder inequality is iterated.

## Main results

* `TauCeti.exists_div_pow_le_and_forall_mul_pow_lt_one`: for `1 < r`, `0 < s < r` and `0 < p`
  there is `M > 0` with `s / r ^ M ≤ p` and `s / r ^ M * r ^ k < 1` for all `k < M`.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]

/-- For `r > 1`, `0 < s < r` and `p > 0` there is a number `M ≥ 1` of steps such that the
starting value `s / r ^ M` is at most `p`, and the terms `s / r ^ M * r ^ k` of the geometric
sequence for the steps `k < M` stay below `1`. -/
theorem exists_div_pow_le_and_forall_mul_pow_lt_one {r s p : K} (hr : 1 < r)
    (hs : 0 < s) (hsr : s < r) (hp : 0 < p) :
    ∃ M : ℕ, 0 < M ∧ s / r ^ M ≤ p ∧ ∀ k < M, s / r ^ M * r ^ k < 1 := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (s / p) hr
  refine ⟨m + 1, m.succ_pos, ?_, fun k hk => ?_⟩
  · calc s / r ^ (m + 1) ≤ s / r ^ m :=
          div_le_div_of_nonneg_left hs.le (by positivity) (pow_le_pow_right₀ hr.le m.le_succ)
      _ ≤ p := by
          rw [div_le_iff₀ (by positivity), mul_comm, ← div_le_iff₀ hp]
          exact hm.le
  · calc s / r ^ (m + 1) * r ^ k ≤ s / r ^ (m + 1) * r ^ m := by
          gcongr
          · exact hr.le
          · omega
      _ = s / r := by
          rw [pow_succ]
          field_simp
      _ < 1 := (div_lt_one hr0).2 hsr

end TauCeti
