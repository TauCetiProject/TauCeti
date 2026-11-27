/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.RingTheory.Int.Basic

/-!
# The even extension of the von Mangoldt function to the integers

Sums of the von Mangoldt function over the values of an integer polynomial, as in
Skorobogatov and Sofos, *Schinzel Hypothesis on average and rational points*,
Invent. Math. 231 (2023), §3, evaluate `Λ` at integers of either sign. This file defines the even
extension `ArithmeticFunction.evenVonMangoldt n = Λ |n|` of the von Mangoldt function to `ℤ`,
which vanishes at `0`, and transfers the basic API of `ArithmeticFunction.vonMangoldt` to it.

## Main definitions

* `ArithmeticFunction.evenVonMangoldt`: the function `n ↦ Λ n.natAbs` on `ℤ`.

## Main results

* `ArithmeticFunction.evenVonMangoldt_natCast`: on natural numbers it is the von Mangoldt function.
* `ArithmeticFunction.evenVonMangoldt_neg`: it is an even function.
* `ArithmeticFunction.evenVonMangoldt_apply_prime`: its value at a prime integer `p` of either
  sign is `Real.log p`.
* `ArithmeticFunction.evenVonMangoldt_eq_zero_iff`: it vanishes exactly where the absolute value
  is not a prime power.
* `ArithmeticFunction.evenVonMangoldt_le_log`: it is at most `Real.log n`.
-/

public section

namespace ArithmeticFunction

/-- The even extension of the von Mangoldt function to the integers: `evenVonMangoldt n` is
`Λ |n|`, so it is `Real.log p` when `n = ± p ^ k` for a prime `p` and `k ≥ 1`, and `0` otherwise,
in particular at `n = 0`. -/
noncomputable def evenVonMangoldt (n : ℤ) : ℝ :=
  Λ n.natAbs

/-- The even von Mangoldt function at `n` is the von Mangoldt function at `n.natAbs`. -/
theorem evenVonMangoldt_def (n : ℤ) : evenVonMangoldt n = Λ n.natAbs := (rfl)

/-- On natural numbers the even von Mangoldt function is the von Mangoldt function. -/
@[simp]
theorem evenVonMangoldt_natCast (n : ℕ) : evenVonMangoldt n = Λ n := by
  rw [evenVonMangoldt_def, Int.natAbs_natCast]

/-- On numeric literals the even von Mangoldt function is the von Mangoldt function. -/
@[simp]
theorem evenVonMangoldt_ofNat (n : ℕ) : evenVonMangoldt ofNat(n) = Λ ofNat(n) :=
  evenVonMangoldt_natCast n

/-- The even von Mangoldt function is even. -/
@[simp]
theorem evenVonMangoldt_neg (n : ℤ) : evenVonMangoldt (-n) = evenVonMangoldt n := by
  rw [evenVonMangoldt_def, evenVonMangoldt_def, Int.natAbs_neg]

/-- The even von Mangoldt function only depends on the absolute value. -/
@[simp]
theorem evenVonMangoldt_abs (n : ℤ) : evenVonMangoldt |n| = evenVonMangoldt n := by
  rw [evenVonMangoldt_def, evenVonMangoldt_def, Int.natAbs_abs]

/-- The even von Mangoldt function vanishes at zero. -/
theorem evenVonMangoldt_zero : evenVonMangoldt 0 = 0 := by
  rw [evenVonMangoldt_def, Int.natAbs_zero, map_zero]

/-- The even von Mangoldt function vanishes at one. -/
theorem evenVonMangoldt_one : evenVonMangoldt 1 = 0 := by
  rw [evenVonMangoldt_def, Int.natAbs_one, vonMangoldt_apply_one]

/-- The even von Mangoldt function is nonnegative. -/
theorem evenVonMangoldt_nonneg (n : ℤ) : 0 ≤ evenVonMangoldt n := by
  rw [evenVonMangoldt_def]
  exact vonMangoldt_nonneg

/-- The even von Mangoldt function takes the same value at `n ^ k` as at `n`, for `k ≠ 0`. -/
theorem evenVonMangoldt_apply_pow (n : ℤ) {k : ℕ} (hk : k ≠ 0) :
    evenVonMangoldt (n ^ k) = evenVonMangoldt n := by
  rw [evenVonMangoldt_def, evenVonMangoldt_def, Int.natAbs_pow, vonMangoldt_apply_pow hk]

/-- At a prime integer `p`, positive or negative, the even von Mangoldt function is `Real.log p`
(recall that `Real.log p = Real.log |p|`). -/
theorem evenVonMangoldt_apply_prime {p : ℤ} (hp : Prime p) :
    evenVonMangoldt p = Real.log p := by
  rw [evenVonMangoldt_def, vonMangoldt_apply_prime (Int.prime_iff_natAbs_prime.mp hp),
    Nat.cast_natAbs, Int.cast_abs, Real.log_abs]

/-- The even von Mangoldt function vanishes at `n` exactly when `|n|` is not a prime power. -/
@[simp]
theorem evenVonMangoldt_eq_zero_iff {n : ℤ} : evenVonMangoldt n = 0 ↔ ¬IsPrimePow n.natAbs := by
  rw [evenVonMangoldt_def, vonMangoldt_eq_zero_iff]

/-- The even von Mangoldt function is nonzero at `n` exactly when `|n|` is a prime power. -/
theorem evenVonMangoldt_ne_zero_iff {n : ℤ} : evenVonMangoldt n ≠ 0 ↔ IsPrimePow n.natAbs := by
  rw [evenVonMangoldt_def, vonMangoldt_ne_zero_iff]

/-- The even von Mangoldt function is positive at `n` exactly when `|n|` is a prime power. -/
@[simp]
theorem evenVonMangoldt_pos_iff {n : ℤ} : 0 < evenVonMangoldt n ↔ IsPrimePow n.natAbs := by
  rw [evenVonMangoldt_def, vonMangoldt_pos_iff]

/-- The even von Mangoldt function is at most the logarithm; at `n = 0` both sides vanish. -/
theorem evenVonMangoldt_le_log (n : ℤ) : evenVonMangoldt n ≤ Real.log n := by
  rw [evenVonMangoldt_def, ← Real.log_abs, ← Int.cast_abs, ← Nat.cast_natAbs]
  exact vonMangoldt_le_log

example : evenVonMangoldt 0 = 0 := by simp

example : evenVonMangoldt (-2) = Real.log 2 := by
  simp [vonMangoldt_apply_prime Nat.prime_two]

example : evenVonMangoldt (-8) = Real.log 2 := by
  have h : (-8 : ℤ) = -(2 ^ 3) := by norm_num
  rw [h, evenVonMangoldt_neg, evenVonMangoldt_apply_pow 2 three_ne_zero,
    evenVonMangoldt_apply_prime Int.prime_two, Int.cast_ofNat]

example : evenVonMangoldt (-6) = 0 := by
  rw [evenVonMangoldt_eq_zero_iff, isPrimePow_iff_unique_prime_dvd]
  rintro ⟨p, -, hp⟩
  have h2 := hp 2 ⟨Nat.prime_two, by decide⟩
  have h3 := hp 3 ⟨Nat.prime_three, by decide⟩
  omega

end ArithmeticFunction
