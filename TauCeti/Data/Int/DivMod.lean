/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Init
import Mathlib.Tactic.Ring

/-!
# Quotient and remainder of a successor in `ℤ`, and reflected quotients

Passing from `m` to `m + 1` either increases the remainder `m % n` by one, keeping the quotient
`m / n`, or, when `m % n + 1 = n`, resets the remainder to `0` and increases the quotient by one.
These are the integer counterparts of `Nat.succ_div_of_not_dvd` and `Nat.succ_div_of_dvd`, phrased
by the remainder so that they apply to the periodic indexing `m ↦ (m / n, m % n)`.

## Main results

* `Int.add_one_ediv_of_emod_add_one_lt`, `Int.add_one_emod_of_emod_add_one_lt`: if
  `m % n + 1 < n` then `(m + 1) / n = m / n` and `(m + 1) % n = m % n + 1`.
* `Int.add_one_ediv_of_emod_add_one_eq`, `Int.add_one_emod_of_emod_add_one_eq`: if
  `m % n + 1 = n` then `(m + 1) / n = m / n + 1` (for `n ≠ 0`) and `(m + 1) % n = 0`.
* `Int.ediv_add_sub_ediv`: the quotient by `N` rises by `0` or `1` when the numerator rises by
  `d ∈ [0, N]`.
* `TauCeti.natCast_mul_sub_div`: reflecting `x ↦ T - x` reflects the quotient of `b x` by `T`:
  `⌊b (T - x) / T⌋ = b - 1 - ⌊b x / T⌋` for `x ≤ T` with `T ∤ b x`.
-/

public section

namespace Int

variable {m n : ℤ}

/-- If the remainder of `m` modulo `n` is not the last one, `m + 1` has the same quotient. -/
theorem add_one_ediv_of_emod_add_one_lt (h : m % n + 1 < n) : (m + 1) / n = m / n := by
  by_cases hn : n = 0
  · simp [hn]
  have := emod_nonneg m hn
  have := emod_add_mul_ediv m n
  exact ((Int.ediv_emod_unique (r := m % n + 1) (by omega)).2 ⟨by omega, by omega, h⟩).1

/-- If the remainder of `m` modulo `n` is not the last one, `m + 1` has the next remainder. -/
theorem add_one_emod_of_emod_add_one_lt (h : m % n + 1 < n) : (m + 1) % n = m % n + 1 := by
  rw [emod_def, add_one_ediv_of_emod_add_one_lt h, emod_def]
  omega

/-- If the remainder of `m` modulo `n ≠ 0` is the last one, `m + 1` has the next quotient. -/
theorem add_one_ediv_of_emod_add_one_eq (hn : n ≠ 0) (h : m % n + 1 = n) :
    (m + 1) / n = m / n + 1 :=
  Int.ediv_eq_of_eq_mul_right hn (by have := emod_add_mul_ediv m n; rw [Int.mul_add]; omega)

/-- If the remainder of `m` modulo `n` is the last one, `m + 1` is divisible by `n`. -/
theorem add_one_emod_of_emod_add_one_eq (h : m % n + 1 = n) : (m + 1) % n = 0 :=
  emod_eq_zero_of_dvd ⟨m / n + 1, by have := emod_add_mul_ediv m n; rw [Int.mul_add]; omega⟩

/-- The quotient by `N` rises by `0` or `1` when the numerator rises by `d ∈ [0, N]`. -/
theorem ediv_add_sub_ediv {t d N : ℤ} (hd : 0 ≤ d) (hdN : d ≤ N) :
    (t + d) / N - t / N = 0 ∨ (t + d) / N - t / N = 1 := by
  rcases eq_or_lt_of_le (hd.trans hdN) with hN | hN
  · simp [← hN]
  have h₁ : t / N ≤ (t + d) / N := Int.ediv_le_ediv hN (by omega)
  have h₂ : (t + d) / N ≤ (t + N) / N := Int.ediv_le_ediv hN (by omega)
  rw [show t + N = t + 1 * N by ring, Int.add_mul_ediv_right _ _ hN.ne'] at h₂
  omega

end Int

namespace TauCeti

/-- **Reflected quotients.** For `x ≤ T` with `T ∤ b x`, `⌊b (T - x) / T⌋ = b - 1 - ⌊b x / T⌋`. -/
theorem natCast_mul_sub_div {T b x : ℕ} (hx : x ≤ T) (h : ¬ T ∣ b * x) :
    ((b * (T - x) / T : ℕ) : ℤ) = b - 1 - (b * x / T : ℕ) := by
  have hT0 : T ≠ 0 := by
    rintro rfl
    exact h (by simp [Nat.le_zero.1 hx])
  have hT : (T : ℤ) ≠ 0 := by exact_mod_cast hT0
  push_cast [Nat.cast_sub hx]
  have hsplit : (b : ℤ) * (T - x) = -(b * x) + b * T := by ring
  have hdvd : ¬ (T : ℤ) ∣ b * x := by exact_mod_cast h
  rw [hsplit, Int.add_mul_ediv_right _ _ hT, Int.neg_ediv]
  simp only [hdvd, ↓reduceIte,
    Int.sign_natCast_of_ne_zero hT0]
  ring

end TauCeti
