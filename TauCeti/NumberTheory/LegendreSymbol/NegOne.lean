/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Natural numbers with Legendre symbol `-1`

A natural number `n` with `(n / p) = -1` is neither `p`, since `(p / p) = 0`
(`ne_of_legendreSym_eq_neg_one`), nor `0` or `1`, since `(0 / p) = 0` and `(1 / p) = 1`
(`two_le_of_legendreSym_eq_neg_one`). Conversely, a prime `n ≠ p` with `(n / p) ≠ 1` has
`(n / p) = -1` (`legendreSym_eq_neg_one_of_ne_one`).
-/

public section

namespace TauCeti

variable {p n : ℕ} [Fact p.Prime]

/-- A natural number `n` with `(n / p) = -1` is not `p`, since `(p / p) = 0`. -/
theorem ne_of_legendreSym_eq_neg_one (h : legendreSym p n = -1) : n ≠ p := by
  rintro rfl
  rw [(legendreSym.eq_zero_iff n n).mpr (by simp)] at h
  exact absurd h (by decide)

/-- A natural number `n` with `(n / p) = -1` satisfies `2 ≤ n`, since `(0 / p) = 0` and
`(1 / p) = 1`. -/
theorem two_le_of_legendreSym_eq_neg_one (h : legendreSym p n = -1) : 2 ≤ n := by
  by_contra! hlt
  interval_cases n
  · rw [Nat.cast_zero, legendreSym.at_zero] at h; exact absurd h (by decide)
  · rw [Nat.cast_one, legendreSym.at_one] at h; exact absurd h (by decide)

/-- A prime `n ≠ p` with `(n / p) ≠ 1` has `(n / p) = -1`, since `p ∤ n`. -/
theorem legendreSym_eq_neg_one_of_ne_one (hn : n.Prime) (hnp : n ≠ p)
    (h : legendreSym p n ≠ 1) : legendreSym p n = -1 := by
  refine (legendreSym.eq_one_or_neg_one p ?_).resolve_left h
  rw [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff,
    Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hn]
  exact Ne.symm hnp

end TauCeti
